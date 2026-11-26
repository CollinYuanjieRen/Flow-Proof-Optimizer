import Lean
import Lean.Util.NumObjs

open Lean

namespace ProofPairs

-- Store de Bruijn binders and their kinds, dropping their display names only.
private partial def clean (e : Expr) : MonadCacheT ExprStructEq Expr IO Expr :=
  checkCache (α := ExprStructEq) ⟨e⟩ fun _ => do
    match e with
    | .lam _ d b i => return .lam .anonymous (← clean d) (← clean b) i
    | .forallE _ d b i => return .forallE .anonymous (← clean d) (← clean b) i
    | .letE _ t v b n => return .letE .anonymous (← clean t) (← clean v) (← clean b) n
    | .mdata _ b => clean b
    | _ => e.traverseChildren clean

private def normalized (params : List Name) (e : Expr) : IO Expr := do
  let levels := (List.range params.length).map fun i => Level.param (.num .anonymous i)
  (clean (e.instantiateLevelParams params levels)).run

private def key (d : TheoremVal) (e : Expr) : IO ExprStructEq := do
  return ⟨← normalized d.levelParams e⟩

-- A necessary condition for normalized statements to match. This cheap
-- projection lets most library declarations bypass the full expression walk.
private def conclusionHead : Expr → Name
  | .forallE _ _ b _ | .mdata _ b | .app b _ => conclusionHead b
  | .const n _ => n
  | _ => .anonymous

-- Alternate binder conventions are useful for discovery. Keep this separate
-- from the exact interface comparison used to authorize a patch proposal.
private def explicitTelescope : Expr → Expr
  | .forallE n t b _ => .forallE n t (explicitTelescope b) .default
  | e => e

-- The last part contains the complete declaration table, including private proofs.
private def constants (path : System.FilePath) : IO (Array ConstantInfo) := do
  let server := path.withExtension "olean.server"
  let paths := if ← server.pathExists then #[path, server, path.withExtension "olean.private"] else #[path]
  let parts ← readModuleDataParts paths
  let some (data, _) := parts.back? | throw <| IO.userError s!"empty module data for {path}"
  if data.isModule && paths.size != 3 then
    throw <| IO.userError s!"missing private module data for {path}"
  return data.constants

private def declarations (path : System.FilePath) : IO (Array TheoremVal) := do
  return (← constants path).filterMap fun
    | .thmInfo d => some d
    | _ => none

-- A tactic may name a lifted subproof after its enclosing theorem. Compare one
-- layer of those closed private helpers by their actual type and value.
private def liftedProof (name : Name) : Bool :=
  isPrivateName name && match name with
    | .str _ suffix => suffix.startsWith "_proof_"
    | _ => false

private def alignHelpers (a b : Expr) (decls : Std.HashMap Name TheoremVal) : IO Bool := do
  let mut representatives : Std.HashMap (Nat × ExprStructEq × ExprStructEq) Name := {}
  let mut names : Std.HashMap Name Name := {}
  for e in #[a, b] do
    for n in e.getUsedConstants do
      if liftedProof n && !names.contains n then
        if let some d := decls[n]? then
          let id := (d.levelParams.length, ← key d d.type, ← key d d.value)
          let repr := representatives.getD id n
          representatives := representatives.insert id repr
          names := names.insert n repr
  if names.isEmpty then return false
  let rewrite := fun (e : Expr) => e.replace fun
    | .const n us => (names[n]?).map fun r => .const r us
    | _ => none
  return Expr.equal (rewrite a) (rewrite b)

/-- The first module is the target. Later modules supply reference theorems
    (e.g. from mathlib). Only pairs involving the target are emitted. -/
def scan (target : String) (refs : List String) (onlyNames : List String := []) (crossOnly := false) : IO Unit := do
  let started ← IO.monoMsNow
  let allTargets ← declarations target
  let wanted := Std.HashSet.ofList onlyNames
  let targets := if wanted.isEmpty then allTargets else allTargets.filter fun d => wanted.contains d.name.toString
  let mut index : Std.HashMap (Nat × ExprStructEq) (Array (TheoremVal × ExprStructEq)) := {}
  let mut bodies : Std.HashMap Name ExprStructEq := {}
  let mut rows : Array String := #[]
  let mut nref := 0
  let shapes := targets.foldl (init := ({} : Std.HashSet (Nat × Name))) fun acc d =>
    acc.insert (d.levelParams.length, conclusionHead d.type)
  let mut referenceKeys := 0
  let targetHelpers := allTargets.foldl (init := ({} : Std.HashMap Name TheoremVal)) fun m d =>
    if liftedProof d.name then m.insert d.name d else m
  for path in target :: refs do
    let isTarget := path == target
    let decls ← if isTarget then pure targets else declarations path
    unless isTarget do nref := nref + decls.size
    let helpers := if isTarget then targetHelpers else decls.foldl (init := targetHelpers) fun m d =>
      if liftedProof d.name then m.insert d.name d else m
    for d in decls do
      unless isTarget do
        unless shapes.contains (d.levelParams.length, conclusionHead d.type) do continue
        referenceKeys := referenceKeys + 1
      let strict ← key d d.type
      let signature := (d.levelParams.length, (⟨explicitTelescope strict.val⟩ : ExprStructEq))
      let bucket := index.getD signature #[]
      let mut currentBody := none
      for (prev, prevType) in (if crossOnly && isTarget then #[] else bucket) do
        let mut kind := "different-binders"
        if strict == prevType then
          let value ← match currentBody with
            | some v => pure v
            | none => key d d.value
          currentBody := some value
          let prevValue ← match bodies[prev.name]? with
            | some v => pure v
            | none => key prev prev.value
          bodies := bodies.insert prev.name prevValue
          kind ← if value == prevValue then pure "same-body"
            else if ← alignHelpers prevValue.val value.val helpers then pure "same-body-via-helpers"
            else pure "same-statement"
        rows := rows.push s!"{kind}\t{prev.name}\t{d.name}"
      if isTarget then
        index := index.insert signature (bucket.push (d, strict))
        if let some v := currentBody then bodies := bodies.insert d.name v
  for row in rows.qsort (· < ·) do IO.println row
  IO.eprintln s!"target={targets.size} reference={nref} reference_keys={referenceKeys} pairs={rows.size} elapsed_ms={(← IO.monoMsNow) - started}"

-- Check all retained kernel types and values in the defining module, including
-- opaque values. A private theorem's nested auxiliary declarations go with it.
def checkUnused (path : String) (names : List String) : IO Unit := do
  let cs ← constants path
  let wanted := Std.HashSet.ofList names
  let roots := cs.foldl (init := ({} : Std.HashSet Name)) fun set c =>
    if c matches .thmInfo _ then
      if isPrivateName c.name && wanted.contains c.name.toString then set.insert c.name else set
    else set
  unless roots.size == wanted.size && !roots.isEmpty do
    throw <| IO.userError "each requested root must be a private theorem in this module"
  let rec belongs (n : Name) : Bool :=
    roots.contains n || match n with
      | .anonymous => false
      | .num p _ | .str p _ => belongs p
  let owned := cs.foldl (init := ({} : Std.HashSet Name)) fun set c =>
    if belongs c.name then set.insert c.name else set
  let mut edges := 0
  for c in cs do
    unless owned.contains c.name do
      for dep in c.getUsedConstantsAsSet do
        if owned.contains dep then
          IO.eprintln s!"{c.name} uses {dep}"
          edges := edges + 1
  IO.eprintln s!"private_roots={roots.size} owned={owned.size} retained={cs.size-owned.size} incoming={edges}"
  if edges > 0 then throw <| IO.userError "retained declarations depend on the candidate"

def edges (path : String) : IO Unit := do
  for c in ← constants path do
    let refs := c.getUsedConstantsAsSet.toList.map Name.toString
    IO.println (toJson (c.name.toString, refs)).compress

-- Used on demand for one module when looking for an existing lemma with a similar conclusion.
def resultProviders (path : String) : IO Unit := do
  let rec result : Expr → Expr
    | .forallE _ _ b _ | .mdata _ b => result b
    | e => e
  for c in ← constants path do
    let symbols := match c with
      | .thmInfo d => some ((result d.type).getUsedConstants.map Name.toString)
      | _ => none
    IO.println (toJson (c.name.toString, (c.getUsedConstantsAsSet.toList.map Name.toString, symbols))).compress

def proofInfo (path : String) (names : List String) : IO Unit := do
  for c in ← constants path do
    if names.contains c.name.toString then
      if let some v := c.value? (allowOpaque := true) then
        IO.println (toJson (c.name.toString, ← v.numObjs, v.getUsedConstants.map Name.toString)).compress

-- Preserve universe arguments. Instantiating or permuting them needs a different rewrite.
private def forwardedName? (d : TheoremVal) : Option Name := do
  let .const n levels := d.value.eta | none
  guard (levels == d.levelParams.map Level.param)
  return n

def forwarders (path : String) : IO Unit := do
  for d in ← declarations path do
    if let some n := forwardedName? d then
      IO.println (toJson (d.name.toString, n.toString)).compress

def checkForward (path provider : String) (wrapper target : Name) : IO Unit := do
  let some f := (← declarations path).find? (·.name == wrapper)
    | throw <| IO.userError s!"missing wrapper {wrapper}"
  let some g := (← declarations provider).find? (·.name == target)
    | throw <| IO.userError s!"missing target {target}"
  unless forwardedName? f == some target && f.levelParams.length == g.levelParams.length &&
      (← key f f.type) == (← key g g.type) do
    throw <| IO.userError s!"{wrapper} does not forward with the same interface to {target}"
  IO.println "same interface and exact eta forwarding"

-- Binder names locate a source candidate; the de Bruijn test detects implicit uses too.
def localLets (path : String) (names : List String) : IO Unit := do
  let wanted := Std.HashSet.ofList names
  for d in ← declarations path do
    if wanted.contains d.name.toString then
      d.value.forEach fun e => do
        if let .letE n _ v b _ := e then
          IO.println (toJson (d.name.toString, n.eraseMacroScopes.toString,
            b.hasLooseBVar 0, ← v.numObjs)).compress

-- Work from the continuation backwards so an entire dead chain disappears in one pass.
-- Only report bindings that originally had a use. Names nominate source edits for replay.
private partial def pruneDeadLets (newlyDead : IO.Ref (Array String)) (e : Expr) :
    MonadCacheT ExprStructEq Expr IO Expr := checkCache (α := ExprStructEq) ⟨e⟩ fun _ => do
  match e with
  | .letE n t v b nd =>
    let body ← pruneDeadLets newlyDead b
    if !body.hasLooseBVar 0 then
      if b.hasLooseBVar 0 then newlyDead.modify (·.push n.eraseMacroScopes.toString)
      return body.lowerLooseBVars 1 1
    return .letE n (← pruneDeadLets newlyDead t) (← pruneDeadLets newlyDead v) body nd
  | _ => e.traverseChildren (pruneDeadLets newlyDead)

def cascadeLets (path : String) (names : List String) : IO Unit := do
  let wanted := Std.HashSet.ofList names
  for d in ← declarations path do
    if wanted.contains d.name.toString then
      let newlyDead ← IO.mkRef #[]
      discard <| (pruneDeadLets newlyDead d.value).run
      IO.println (toJson (d.name.toString, ← newlyDead.get)).compress

-- Index used local bindings whose types and values are independent of binder context.
-- Within each enclosing theorem the IDs partition exact normalized type/value pairs.
def closedLocalClasses (path : String) (names : List String) (acrossDecls := false) : IO Unit := do
  let wanted := Std.HashSet.ofList names
  let classes ← IO.mkRef ({} : Std.HashMap (Nat × ExprStructEq × ExprStructEq) Nat)
  for d in ← declarations path do
    if wanted.contains d.name.toString then
      unless acrossDecls do classes.set {}
      d.value.forEach fun e => do
        if let .letE n type value body _ := e then
          if body.hasLooseBVar 0 && !type.hasLooseBVars && !value.hasLooseBVars then
            let sig := (d.levelParams.length, ← key d type, ← key d value)
            let index ← classes.get
            let id := index.getD sig index.size
            unless index.contains sig do classes.set (index.insert sig id)
            IO.println (toJson (d.name.toString, n.eraseMacroScopes.toString, id)).compress

-- Check the recompiled proof against a specified sequence of unused let eliminations.
def checkDropLets (oldPath newPath oldName newName : String) (binders : List String) : IO Unit := do
  let readThm := fun path name => do
    let some d := (← declarations path).find? (·.name.toString == name)
      | throw <| IO.userError s!"missing theorem {name}"
    return d
  let a ← readThm oldPath oldName
  let b ← readThm newPath newName
  let mut reduced := a.value
  for binder in binders do
    let count ← IO.mkRef 0
    reduced.forEach fun e => do
      if let .letE n _ _ body _ := e then
        if n.eraseMacroScopes.toString == binder && !body.hasLooseBVar 0 then
          count.modify (· + 1)
    unless (← count.get) == 1 do
      throw <| IO.userError s!"expected one unused binder named {binder}"
    let next := reduced.replace fun e => match e with
      | .letE n _ _ body _ =>
        if n.eraseMacroScopes.toString == binder && !body.hasLooseBVar 0 then
          some (body.lowerLooseBVars 1 1)
        else none
      | _ => none
    if Expr.equal reduced next then throw <| IO.userError s!"binder {binder} is used"
    reduced := next
  unless a.levelParams.length == b.levelParams.length &&
      (← key a a.type) == (← key b b.type) && (← key a reduced) == (← key b b.value) do
    throw <| IO.userError "the recompiled proof does not match this unused let elimination"
  if binders.length == 1 then IO.println "same type and proof after one unused let elimination"
  else IO.println s!"same type and proof after {binders.length} unused let eliminations"

-- Hashes schedule exact comparisons; equality of hashes never licenses a rewrite.
def census (path : String) : IO Unit := do
  for c in ← constants path do
    let signature ← match c with
      | .thmInfo d => do
        let ty ← key d d.type
        let body ← key d d.value
        pure <| Json.arr #[toJson d.levelParams.length, toJson (toString (hash ty)),
          toJson (toString (hash body))]
      | _ => pure Json.null
    IO.println (Json.arr #[toJson c.name.toString, signature,
      toJson (c.getUsedConstantsAsSet.toList.map Name.toString)]).compress

structure Member where
  name : String
  group : Nat
  index : Nat
  deriving FromJson

-- Each hash bucket is partitioned by exact normalized type and proof structure.
def partition (paths : List String) : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let jobs : List (List Member) ← IO.ofExcept (Json.parse input >>= fromJson?)
  unless paths.length == jobs.length do throw <| IO.userError "module count mismatch"
  let mut reps : Std.HashMap (Nat × Nat × ExprStructEq × ExprStructEq) Nat := {}
  for (path, requests) in paths.zip jobs do
    let names := Std.HashMap.ofList (requests.map fun r => (r.name, r))
    let mut found := 0
    for d in ← declarations path do
      if let some r := names[d.name.toString]? then
        let sig := (r.group, d.levelParams.length, ← key d d.type, ← key d d.value)
        let rep := reps.getD sig r.index
        reps := reps.insert sig rep
        IO.println (Json.arr #[toJson r.group, toJson r.index, toJson rep]).compress
        found := found + 1
    unless found == requests.length do throw <| IO.userError s!"missing source theorem in {path}"

private partial def expandLocalReuse (binders : Std.HashSet Name) (providers : Std.HashMap Name TheoremVal) (e : Expr) :
    MonadCacheT ExprStructEq Expr IO Expr := do
  checkCache (α := ExprStructEq) ⟨e⟩ fun _ => do
    match e with
    | .const n ls =>
      if let some d := providers[n]? then
        return ← expandLocalReuse binders providers (d.value.instantiateLevelParams d.levelParams ls)
      return e
    | .letE n _ v b _ =>
      if binders.contains n.eraseMacroScopes then
        return ← expandLocalReuse binders providers (b.instantiate1 v)
      e.traverseChildren (expandLocalReuse binders providers)
    | .app f x =>
      let f ← expandLocalReuse binders providers f
      let x ← expandLocalReuse binders providers x
      if let .lam _ _ b _ := f then return ← expandLocalReuse binders providers (b.instantiate1 x)
      return .app f x
    | .mdata _ b => expandLocalReuse binders providers b
    | _ => e.traverseChildren (expandLocalReuse binders providers)


-- Read pairs of local binder names and existing provider theorem names from stdin.
def checkLocalReuse (before after source : String) (consumers : List String) : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let pairs : List (String × String) ← IO.ofExcept (Json.parse input >>= fromJson?)
  let binders := Std.HashSet.ofList (pairs.map fun p => p.1.toName)
  let wanted := Std.HashSet.ofList (pairs.map fun p => p.2.toName)
  let targets := Std.HashSet.ofList (consumers.map String.toName)
  let mut providers : Std.HashMap Name TheoremVal := {}
  for d in ← declarations source do
    if wanted.contains d.name then providers := providers.insert d.name d
  unless providers.size == wanted.size && !providers.isEmpty && !targets.isEmpty do
    throw <| IO.userError "expected existing provider and consumer theorems"
  let old ← constants before
  let edited ← constants after
  let byName := Std.HashMap.ofList (edited.toList.map fun d => (d.name, d))
  unless old.size == edited.size do throw <| IO.userError "declaration count changed"
  let mut compared := 0
  for c in old do
    let some d := byName[c.name]? | throw <| IO.userError s!"missing {c.name}"
    unless c.levelParams == d.levelParams && Expr.equal c.type d.type do
      throw <| IO.userError s!"interface changed: {c.name}"
    if targets.contains c.name then
      let (.thmInfo x, .thmInfo y) := (c, d) | throw <| IO.userError s!"expected theorem {c.name}"
      let lhs ← (expandLocalReuse binders providers x.value).run
      let rhs ← (expandLocalReuse binders providers y.value).run
      unless (← key x lhs) == (← key y rhs) do throw <| IO.userError s!"expanded proof differs: {c.name}"
      compared := compared + 1
    else
      match c.value? (allowOpaque := true), d.value? (allowOpaque := true) with
      | some x, some y => unless Expr.equal x y do throw <| IO.userError s!"value differs: {c.name}"
      | none, none => pure ()
      | _, _ => throw <| IO.userError s!"value kind changed: {c.name}"
  unless compared == targets.size do throw <| IO.userError "missing consumer"
  IO.println s!"{compared} expanded proofs agree; {old.size-compared} other declarations agree"

private inductive Outer where
  | binder (n : Name) (t : Expr) (info : BinderInfo)
  | binding (n : Name) (t v : Expr) (nondep : Bool)

-- Only capture an enclosing binder if either the local type or its proof needs it.
private def closePair (ctx : List Outer) (t v : Expr) : Expr × Expr := Id.run do
  let mut x := t
  let mut y := v
  for outer in ctx do
    if x.hasLooseBVar 0 || y.hasLooseBVar 0 then
      match outer with
      | .binder n type info =>
        x := .forallE n type x info
        y := .lam n type y info
      | .binding n type value nondep =>
        x := .letE n type value x nondep
        y := .letE n type value y nondep
    else
      x := x.lowerLooseBVars 1 1
      y := y.lowerLooseBVars 1 1
  return (x,y)

private abbrev LocalSlot := Expr × Expr × List Outer

-- Record the first used occurrence in the same depth-first order as the source lookup.
private partial def collectSlots (slots : IO.Ref (Std.HashMap Name LocalSlot))
    (e : Expr) (ctx : List Outer) : MonadCacheT ExprStructEq Unit IO Unit :=
  checkCache (α := ExprStructEq) ⟨e⟩ fun _ => do
    match e with
    | .letE n t v b nd =>
      let label := n.eraseMacroScopes
      if b.hasLooseBVar 0 && !(← slots.get).contains label then
        slots.modify (·.insert label (t,v,ctx))
      collectSlots slots t ctx
      collectSlots slots v ctx
      collectSlots slots b (.binding n t v nd :: ctx)
    | .lam n t b bi | .forallE n t b bi =>
      collectSlots slots t ctx
      collectSlots slots b (.binder n t bi :: ctx)
    | .app f a => collectSlots slots f ctx; collectSlots slots a ctx
    | .proj _ _ b | .mdata _ b => collectSlots slots b ctx
    | _ => pure ()

def compareLocalContexts : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let groups : List (List (String × String × String)) ← IO.ofExcept (Json.parse input >>= fromJson?)
  -- Consecutive groups often compare different binders in the same pair of proofs.
  let mut previous : Std.HashMap (String × String) (TheoremVal × Std.HashMap String Nat × Std.HashMap Name LocalSlot) := {}
  for group in groups do
    let mut current := {}
    let mut classes : Std.HashMap (Nat × ExprStructEq × ExprStructEq) Nat := {}
    let mut ids := #[]
    for (path, owner, binder) in group do
      let ownerKey := (path, owner)
      let entry ← match current[ownerKey]? <|> previous[ownerKey]? with
        | some entry => pure entry
        | none => do
          let some d := (← declarations path).find? (·.name.toString == owner) | throw <| IO.userError owner
          let counts ← IO.mkRef ({} : Std.HashMap String Nat)
          d.value.forEach fun expr => do
            if let .letE n _ _ _ _ := expr then
              let label := n.eraseMacroScopes.toString
              counts.modify fun m => m.insert label (m.getD label 0 + 1)
          let slots ← IO.mkRef {}
          (collectSlots slots d.value []).run
          pure (d, ← counts.get, ← slots.get)
      current := current.insert ownerKey entry
      let (d, counts, slots) := entry
      unless counts.getD binder 0 == 1 do throw <| IO.userError s!"ambiguous local binder {owner}.{binder}"
      let some (type,value,ctx) := slots[binder.toName]? | throw <| IO.userError binder
      let (t,v) := closePair ctx type value
      if t.hasLooseBVars || v.hasLooseBVars then throw <| IO.userError "unclosed extracted term"
      let sig := (d.levelParams.length, ← key d t, ← key d v)
      let idx := classes.getD sig classes.size
      classes := classes.insert sig idx
      ids := ids.push idx
    previous := current
    IO.println (toJson ids).compress

/-- Count distinct normalized subexpressions across the supplied compiled bodies.
    Each JSON input row pairs a module path with its selected declaration names. -/
def footprint : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let rows : List (String × List String) ← IO.ofExcept (Json.parse input >>= fromJson?)
  let shared ← IO.mkRef ({} : Std.HashSet ExprStructEq)
  let mut modules : Std.HashSet String := {}
  let mut bodies := 0
  let mut sum := 0
  for (path, names) in rows do
    if modules.contains path then throw <| IO.userError s!"repeated module path {path}"
    modules := modules.insert path
    let mut wanted := Std.HashSet.ofList names
    for d in ← constants path do
      if wanted.contains d.name.toString then
        let some value := d.value? (allowOpaque := true) | throw <| IO.userError s!"no body for {d.name}"
        let localNodes ← IO.mkRef ({} : Std.HashSet ExprStructEq)
        (← normalized d.levelParams value).forEach fun node => do
          localNodes.modify (·.insert ⟨node⟩)
          shared.modify (·.insert ⟨node⟩)
        sum := sum + (← localNodes.get).size
        bodies := bodies + 1
        wanted := wanted.erase d.name.toString
    unless wanted.isEmpty do throw <| IO.userError s!"missing declarations in {path}: {wanted.toList}"
  IO.println (Json.mkObj [("bodies", toJson bodies), ("union", toJson (← shared.get).size),
    ("sum", toJson sum)]).compress

private partial def expand (providers : Std.HashMap Name (List Name × Expr)) (e : Expr) :
    MonadCacheT ExprStructEq Expr IO Expr := do
  checkCache (α := ExprStructEq) ⟨e⟩ fun _ => do
    match e with
    | .const n ls =>
      if let some d := providers[n]? then
        return ← expand providers (d.2.instantiateLevelParams d.1 ls)
      return e
    | .app f x =>
      let f ← expand providers f
      let x ← expand providers x
      if let .lam _ _ b _ := f then return ← expand providers (b.instantiate1 x)
      return .app f x
    | .mdata _ b => expand providers b
    | _ => e.traverseChildren (expand providers)


private partial def sameZeta (x y : Expr) : MonadCacheT (ExprStructEq × ExprStructEq) Bool IO Bool :=
  checkCache (α := ExprStructEq × ExprStructEq) (⟨x⟩, ⟨y⟩) fun _ => do
    if (⟨x⟩ : ExprStructEq) == ⟨y⟩ then return true
    let x' := x.headBeta
    let y' := y.headBeta
    if !(x' == x && y' == y) then return ← sameZeta x' y'
    match x, y with
    | .letE _ t v b a, .letE _ u w c d =>
      if a == d && (← sameZeta t u) && (← sameZeta v w) then return ← sameZeta b c
      return ← sameZeta (b.instantiate1 v) (c.instantiate1 w)
    | .letE _ _ v b _, _ => return ← sameZeta (b.instantiate1 v) y
    | _, .letE _ _ w c _ => return ← sameZeta x (c.instantiate1 w)
    | .app f a, .app g b => return (← sameZeta f g) && (← sameZeta a b)
    | .forallE _ t v a, .forallE _ u w b | .lam _ t v a, .lam _ u w b =>
      return a == b && (← sameZeta t u) && (← sameZeta v w)
    | .proj n i a, .proj m j b => return n == m && i == j && (← sameZeta a b)
    | _, _ => return false

private structure ShareModule where
  old : String
  «new» : String
  owners : List String
  deriving FromJson

private structure ShareRequest where
  provider : String
  helper : String
  modules : List ShareModule
  deriving FromJson

private abbrev ShareDefs := Std.HashMap Name (List Name × Expr)

-- Match the first component immediately beneath the owner in the private namespace.
private def generatedFor (owner n : Name) : Bool := Id.run do
  unless isPrivateName n do return false
  let o := privateToUserName owner
  let mut p := privateToUserName n
  while !p.isAnonymous do
    if p.getPrefix == o then
      return match p with
        | .str _ s => ["_proof_", "match_", "_simp_"].any (fun pre => s.startsWith pre)
        | _ => false
    p := p.getPrefix
  return false

private def shareBody (c : ConstantInfo) : IO Expr := do
  let some v := c.value? (allowOpaque := true) | throw <| IO.userError s!"missing body {c.name}"
  return v

private def addAux (ds : ShareDefs) (cs : Array ConstantInfo) (owners : List Name) : IO ShareDefs := do
  let mut ds := ds
  for c in cs do
    if owners.any (generatedFor · c.name) then
      ds := ds.insert c.name (c.levelParams, ← shareBody c)
  return ds

private def countShareBody (nodes : IO.Ref (Std.HashSet ExprStructEq)) (c : ConstantInfo) : IO Unit := do
  (← normalized c.levelParams (← shareBody c)).forEach fun e => nodes.modify (·.insert ⟨e⟩)

private def replayShared : IO Unit := do
  let req : ShareRequest ← IO.ofExcept (Json.parse (← (← IO.getStdin).readToEnd) >>= fromJson?)
  let helper := req.helper.toName
  let provider ← constants req.provider
  let some (.thmInfo h) := provider.find? (·.name == helper) | throw <| IO.userError "missing helper theorem"
  unless (req.modules.filter (·.new == req.provider)).length == 1 &&
      (req.modules.map (·.new)).Nodup && (req.modules.map (·.old)).Nodup do
    throw <| IO.userError "expected distinct module pairs including provider"
  let targets := req.modules.flatMap (·.owners)
  unless targets.Nodup && !targets.isEmpty && !targets.contains req.helper do
    throw <| IO.userError "expected distinct edited owners"
  let allRoots := helper :: targets.map String.toName
  let helperDefs ← addAux ({} : ShareDefs) provider [helper]
  let helperDefs := helperDefs.insert helper (h.levelParams,h.value)
  let before ← IO.mkRef ({} : Std.HashSet ExprStructEq)
  let after ← IO.mkRef ({} : Std.HashSet ExprStructEq)
  for m in req.modules do
    let cs ← constants m.old
    let ds ← if m.new == req.provider then pure provider else constants m.new
    let olds := Std.HashMap.ofList (cs.toList.map fun c => (c.name,c))
    let news := Std.HashMap.ofList (ds.toList.map fun c => (c.name,c))
    let owners := m.owners.map String.toName
    let roots := if m.new == req.provider then helper :: owners else owners
    if olds.contains helper then throw <| IO.userError "helper already exists"
    for c in cs do
      -- Every changed private body must be expanded at all of its uses.
      -- A retained user, or a reference across two owner scopes, fails closed.
      for n in c.getUsedConstantsAsSet do
        if isPrivateName n && allRoots.any (fun r => generatedFor r n &&
            !(owners.contains r && (r == c.name || generatedFor r c.name))) then
          throw <| IO.userError s!"outside use of edited auxiliary {n} by {c.name}"
      let aux := owners.any (generatedFor · c.name)
      if aux || owners.contains c.name then countShareBody before c
      if aux then continue
      let some d := news[c.name]? | throw <| IO.userError s!"removed {c.name}"
      unless c.ctorIdx == d.ctorIdx && c.levelParams == d.levelParams && Expr.equal c.type d.type do
        throw <| IO.userError s!"changed interface {c.name}"
      if owners.contains c.name then
        if c.type.getUsedConstants.any (fun n => isPrivateName n && allRoots.any (generatedFor · n)) then
          throw <| IO.userError s!"edited interface depends on an edited auxiliary: {c.name}"
      else
        unless c == d && (match c.value? true, d.value? true with
          | some x, some y => Expr.equal x y
          | none, none => true
          | _, _ => false) do
          throw <| IO.userError s!"changed retained value {c.name}"
    for d in ds do
      if roots.any (fun r => r == d.name || generatedFor r d.name) then
        for n in d.getUsedConstantsAsSet do
          if isPrivateName n && allRoots.any (fun r => generatedFor r n &&
              !(roots.contains r && (r == d.name || generatedFor r d.name))) then
            throw <| IO.userError s!"cross-owner auxiliary {n} used by {d.name}"
      if roots.contains d.name || roots.any (generatedFor · d.name) then countShareBody after d
      else unless olds.contains d.name do throw <| IO.userError s!"unexpected addition {d.name}"
    for owner in owners do
      let some (.thmInfo a) := olds[owner]? | throw <| IO.userError s!"missing old theorem {owner}"
      let some (.thmInfo b) := news[owner]? | throw <| IO.userError s!"missing new theorem {owner}"
      let leftDefs ← addAux {} cs [owner]
      let rightAux ← addAux {} ds [owner]
      -- Check actual use after expanding only the owner's auxiliary bodies.
      let rhs ← (expand rightAux b.value).run
      unless rhs.getUsedConstants.contains helper do throw <| IO.userError s!"helper unused by {owner}"
      let x ← (expand leftDefs a.value).run
      let y ← (expand helperDefs rhs).run
      unless ← (sameZeta (← normalized a.levelParams x) (← normalized b.levelParams y)).run do
        throw <| IO.userError s!"expanded proof differs: {owner}"
  let oldSize := (← before.get).size
  let newSize := (← after.get).size
  unless newSize < oldSize do throw <| IO.userError s!"no reduction: {oldSize} -> {newSize}"
  IO.println (Json.mkObj [("before",toJson oldSize),("after",toJson newSize),
    ("saved",toJson (oldSize-newSize)),("owners",toJson targets.length)]).compress

-- Identify candidate parameter applications in a checked declaration. The output is
-- a source-editing hint. Instantiation replay still checks the completed rewrite.
private partial def boundaryOccurrences (targets : Array Name) (e : Expr)
    (seen : IO.Ref (Std.HashSet ExprStructEq)) (acc : IO.Ref (Array Expr)) : IO Unit := do
  if (← seen.get).contains ⟨e⟩ then return
  seen.modify (·.insert ⟨e⟩)
  let fn := e.getAppFn
  if targets.contains (fn.constName?.getD .anonymous) then acc.modify (·.push e)
  if e.isApp then
    unless fn.isConst do boundaryOccurrences targets fn seen acc
    for arg in e.getAppArgs do boundaryOccurrences targets arg seen acc
  else
    discard <| e.traverseChildren fun child => do boundaryOccurrences targets child seen acc; pure child

private structure BoundaryDecl where
  file : String
  name : String
  deriving FromJson

private structure BoundaryRequest where
  owner : BoundaryDecl
  targets : Array BoundaryDecl
  deriving FromJson

private def boundaryConstant (d : BoundaryDecl) : IO ConstantInfo := do
  let some c := (← constants d.file).find? (·.name == d.name.toName) | throw <| IO.userError d.name
  return c

def boundaryCuts : IO Unit := do
  let q : BoundaryRequest ← IO.ofExcept (Json.parse (← (← IO.getStdin).readToEnd) >>= fromJson?)
  let .thmInfo d ← boundaryConstant q.owner | throw <| IO.userError "expected theorem"
  let mut ty := d.type
  let mut body := d.value
  let mut xs := #[]
  let mut names := #[]
  while let .forallE n _ b _ := ty do
    let .lam _ _ e _ := body | throw <| IO.userError "unsupported original theorem telescope"
    let x := mkFVar ⟨.num .anonymous xs.size⟩
    names := names.push n.toString
    xs := xs.push x
    ty := b.instantiate1 x
    body := e.instantiate1 x
  let seen ← IO.mkRef {}
  let acc ← IO.mkRef #[]
  for e in #[ty,body] do boundaryOccurrences (q.targets.map (·.name.toName)) e seen acc
  let terms ← acc.get
  let mut items := #[]
  for t in q.targets do
    let c ← boundaryConstant t
    let uses := terms.filter (·.getAppFn.isConstOf c.name)
    let some first := uses[0]? | throw <| IO.userError s!"no kernel use {c.name}"
    let mut cut := first.getAppFn
    let mut cutType := c.type.instantiateLevelParams c.levelParams first.getAppFn.constLevels!
    let mut ids := #[]
    let mut explicitArgs := #[]
    for arg in first.getAppArgs, i in [:first.getAppNumArgs] do
      let some pos := xs.idxOf? arg | break
      unless uses.all (fun use => (use.getAppArgs[i]?).any (Expr.equal arg) &&
        Expr.equal use.getAppFn first.getAppFn) do break
      let .forallE _ _ r bi := cutType | throw <| IO.userError s!"unsupported declaration type {c.name}"
      cut := mkApp cut arg
      ids := ids.push pos
      if bi.isExplicit then explicitArgs := explicitArgs.push names[pos]!
      cutType := r.instantiate1 arg
    unless cut.isApp do throw <| IO.userError s!"no common caller argument {c.name}"
    items := items.push (c.name,cut,cutType,ids,explicitArgs)
  let mut pending := items.toList
  let mut rows := #[]
  let mut replacements : List (Expr × Expr) := []
  for _ in [:items.size] do
    let some pick := pending.find? (fun (_,_,t,_,_) => !pending.any (fun (_,other,_,_,_) =>
      (t.find? (Expr.equal other)).isSome)) | throw <| IO.userError "dependent types form a cycle"
    let (name, cut, raw, ids, explicitArgs) := pick
    let deps := replacements.filter (fun (old,_) => (raw.find? (Expr.equal old)).isSome)
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),("binders",toJson (ids.map (names[·]!))),
      ("binderIndices",toJson ids),("explicitCallerArguments",toJson explicitArgs),
      ("priorParameters", toJson (deps.map (fun (_,v) => toString v)))]
    replacements := (cut,mkFVar ⟨("param" ++ toString replacements.length).toName⟩)::replacements
    pending := pending.filter (·.1 != name)
  IO.println (Json.compress (.arr rows))

-- A candidate family may use the other candidates in its types and values.
-- Retest after a rejection so no surviving comparison relies on a rejected pair.
def alignFamily (source provider : String) : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let pairs : List (String × String) ← IO.ofExcept (Json.parse input >>= fromJson?)
  let old := (← constants source).toList
  let targets := Std.HashMap.ofList ((← constants provider).toList.map fun c => (c.name,c))
  let mut groups := #[]
  for (a,b) in pairs do
    let members := old.filter (fun c => a.toName.isPrefixOf c.name)
    unless members.any (fun c => c.name == a.toName) do throw <| IO.userError s!"missing {a}"
    groups := groups.push ((a,b), members.map fun c => (c, c.name.replacePrefix a.toName b.toName))
  repeat
    let names := Std.HashMap.ofList <| groups.toList.flatMap fun (_,ds) =>
      ds.map fun (c,n) => (c.name,n)
    let subst (e : Expr) := e.replace fun x => match x with
      | .const n us => (names[n]?).map fun k => .const k us
      | _ => none
    let kept ← groups.filterM fun (_,ds) => ds.allM fun (c,n) => do
      let some d := targets[n]? | return false
      unless c.ctorIdx == d.ctorIdx && c.levelParams.length == d.levelParams.length do return false
      let some x := c.value? true | return false
      let some y := d.value? true | return false
      let equal (x y : Expr) := do
        return Expr.equal (← normalized c.levelParams (subst x)) (← normalized d.levelParams y)
      return (← equal c.type d.type) && (← equal x y)
    if kept.size == groups.size then
      IO.println (toJson (kept.map (·.1))).compress
      return
    groups := kept

end ProofPairs

def main (args : List String) : IO Unit := do
  if args == ["--boundary-cuts"] then return ← ProofPairs.boundaryCuts
  if args == ["--shared-lemma-replay"] then return ← ProofPairs.replayShared
  if args == ["--footprint"] then return ← ProofPairs.footprint
  if args == ["--compare-local-contexts"] then return ← ProofPairs.compareLocalContexts
  let target :: refs := args | throw <| IO.userError "usage: ProofPairs.lean TARGET.olean [REFERENCE.olean ...]"
  if let ["--align-family", provider] := refs then return ← ProofPairs.alignFamily target provider
  if refs == ["--result-providers"] then ProofPairs.resultProviders target
  else if refs == ["--edges"] then ProofPairs.edges target
  else if let "--drop-unused-let" :: other :: name :: targetName :: first :: rest := refs then
    ProofPairs.checkDropLets target other name targetName (first :: rest)
  else if let "--check-local-reuse" :: after :: source :: names := refs then
    ProofPairs.checkLocalReuse target after source names
  else if let "--shared-closed-locals" :: names := refs then
    ProofPairs.closedLocalClasses target names true
  else if let "--closed-local-classes" :: names := refs then
    ProofPairs.closedLocalClasses target names
  else if let "--local-lets" :: names := refs then ProofPairs.localLets target names
  else if let "--cascade-lets" :: names := refs then ProofPairs.cascadeLets target names
  else if let "--proof-info" :: names := refs then ProofPairs.proofInfo target names
  else if let ["--check-forward", provider, wrapper, name] := refs then
    ProofPairs.checkForward target provider wrapper.toName name.toName
  else if let "--forwarders" :: paths := refs then
    for path in target :: paths do
      ProofPairs.forwarders path
      IO.println ""
  else if let ["--cross", other] := refs then ProofPairs.scan target [other] [] true
  else if let "--census" :: paths := refs then
    for path in target :: paths do
      ProofPairs.census path
      IO.println ""
  else if let "--partition" :: paths := refs then ProofPairs.partition (target :: paths)
  else if let "--edge-batch" :: paths := refs then
    for path in target :: paths do
      ProofPairs.edges path
      IO.println ""
  else if let "--unused" :: names := refs then
    ProofPairs.checkUnused target names
  else if let "--only" :: names := refs then
    if names.isEmpty then throw <| IO.userError "expected theorem names after --only"
    ProofPairs.scan target [] names
  else
    ProofPairs.scan target (refs.eraseDups.filter (· != target))
