module
public meta import Lean

public meta section

open Lean Meta Elab Command

namespace ReverseShare

private abbrev Seen := Std.HashSet ExprStructEq

-- Count a structural expression once across all roots. A refcount update
-- only recurses when a node enters or leaves the union, so candidate scores
-- reuse the original two-declaration DAG without recounting unchanged nodes.
private abbrev Refs := Std.HashMap ExprStructEq Nat

private partial def adjust (refs : Refs) (e : Expr) (add : Bool) : Refs := Id.run do
  let n := refs.getD ⟨e⟩ 0
  if add && n > 0 then return refs.insert ⟨e⟩ (n + 1)
  if !add && n > 1 then return refs.insert ⟨e⟩ (n - 1)
  let refs := if add then refs.insert ⟨e⟩ 1 else refs.erase ⟨e⟩
  return ((e.traverseChildren (M := StateM Refs) fun x => do
    modify fun r => adjust r x add
    pure x).run refs).2

private partial def sites (e : Expr) : StateT Seen MetaM (Array Expr) := do
  if (← get).contains ⟨e⟩ then return #[]
  modify (·.insert ⟨e⟩)
  let mut xs := #[]
  -- Traverse whole arguments, skipping the partially applied prefixes.
  if e.isApp then
    if !e.hasLooseBVars && e.getAppFn.isConst then
      if ← isProof e then xs := xs.push e
    for arg in e.getAppArgs do xs := xs ++ (← sites arg)
    xs := xs ++ (← sites e.getAppFn)
  else
    let children := (e.traverseChildren (M := StateM (Array Expr)) fun x => do
      modify (·.push x); pure x).run #[]
    for x in children.2 do xs := xs ++ (← sites x)
  return xs

private structure Hole where
  a : Expr
  b : Expr
  type : Expr
  marker : Expr

-- Descend common applications backwards. An unequal leaf can become a
-- parameter only if both terms prove the same proposition.
private partial def align (a b : Expr) : StateT (Array Hole) MetaM (Option Expr) := do
  if Expr.equal a b then return some a
  let hs ← get
  if a.isApp && b.isApp && Expr.equal a.getAppFn b.getAppFn &&
      a.getAppNumArgs == b.getAppNumArgs then
    let mut body := a.getAppFn
    let mut ok := true
    for (x, y) in a.getAppArgs.zip b.getAppArgs do
      if let some t ← align x y then body := .app body t
      else
        ok := false
        break
    if ok then return some body
    set hs
  if !(← isProof a) then return none
  let t ← inferType a
  unless ← isDefEq t (← inferType b) do return none
  if let some h := hs.find? (fun h => Expr.equal h.a a && Expr.equal h.b b) then
    return some h.marker
  let marker := mkFVar (← mkFreshFVarId)
  modify (·.push ⟨a, b, t, marker⟩)
  return some marker

private def lambda (holes : Array Hole) (body : Expr) : Expr := Id.run do
  let mut e := body
  for h in holes.reverse do
    e := .lam (.str .anonymous s!"p{holes.findIdx (fun x => Expr.equal x.marker h.marker)}")
      h.type (e.abstract #[h.marker]) .default
  return e

private def replay (body : Expr) (args : Array Expr) : Option Expr := do
  let mut e := body
  for a in args do
    let .lam _ _ b _ := e | none
    e := b.instantiate1 a
  return e

private def render (e : Expr) : MetaM String := do return (← ppExpr e).pretty

private structure Candidate where
  helper : Expr
  type : Expr
  left : Array Expr
  right : Array Expr
  a : Expr
  b : Expr
  after : Nat

private def extract (v₁ v₂ a b ref : Expr) (base : Refs) : MetaM (Option Candidate) := do
  let (some shape, holes) ← (align a b).run #[] | return none
  unless shape.isApp do return none
  let helper := lambda holes shape
  let env ← getEnv
  let lctx ← getLCtx
  let .ok t := Kernel.check env lctx helper | return none
  let left := holes.map (·.a)
  let right := holes.map (·.b)
  unless (replay helper left).any (Expr.equal · a) &&
         (replay helper right).any (Expr.equal · b) do return none
  for args in #[left, right] do
    let .ok _ := Kernel.check env lctx (mkAppN helper args) | return none
  let rewrite := fun (v site : Expr) (args : Array Expr) =>
    v.replace fun x => if Expr.equal x site then some (mkAppN ref args) else none
  let refs := #[rewrite v₁ a left, rewrite v₂ b right, t, helper].foldl
    (fun r e => adjust r e true) base
  let refs := adjust (adjust refs v₁ false) v₂ false
  return some ⟨helper, t, left, right, a, b, refs.size⟩

private def row (c : Candidate) (before : Nat) : MetaM Json := do
  return Json.mkObj [
    ("kind", toJson (if c.left.isEmpty then "exact" else "parameterized")),
    ("helper_type", toJson (← render c.type)), ("helper_body", toJson (← render c.helper)),
    ("left_args", toJson (← c.left.mapM render)), ("right_args", toJson (← c.right.mapM render)),
    ("site_left", toJson (← render c.a)), ("site_right", toJson (← render c.b)),
    ("site_left_hash", toJson (toString (hash c.a))), ("site_right_hash", toJson (toString (hash c.b))),
    ("dag_before", toJson before), ("dag_after", toJson c.after)]

private structure Bucket where
  hits : Nat := 0
  gains : Array Candidate := #[]
  bestLoss : Option Candidate := none

private def Bucket.add (s : Bucket) (before : Nat) (c : Candidate) : Bucket :=
  if c.after < before then {s with hits := s.hits + 1, gains := s.gains.push c}
  else {s with hits := s.hits + 1, bestLoss := match s.bestLoss with
    | some old => some (if c.after < old.after then c else old)
    | none => some c}

private def Bucket.rows (s : Bucket) : Array Candidate :=
  s.gains ++ s.bestLoss.toArray

/-- Compare two compiled bodies in the same universe-parameter convention.
Only closed proof applications headed by constants are considered. Each trial
replaces all exact occurrences of the selected site in each body. The score
counts distinct Expr nodes across the original types, rewritten bodies and
fresh helper type/value. Output includes every gain and the best non-gain in
each category. Printed terms illustrate kernel expressions and need not parse. -/
elab "#reverse_share " a:ident b:ident : command => liftTermElabM do
  let d₁ ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo a)
  let d₂ ← getConstInfo (← realizeGlobalConstNoOverloadWithInfo b)
  if d₁.name == d₂.name then throwError "select two distinct declarations"
  if d₁.levelParams != d₂.levelParams then throwError "universe parameter lists differ"
  let some v₁ := d₁.value? true | throwError "left body unavailable"
  let some v₂ := d₂.value? true | throwError "right body unavailable"
  let xs := (← (sites v₁).run {}).1
  let ys := (← (sites v₂).run {}).1
  let base := #[d₁.type, v₁, d₂.type, v₂].foldl (fun r e => adjust r e true) {}
  let key := fun (x : Expr) => ((⟨x.getAppFn⟩ : ExprStructEq), x.getAppNumArgs)
  let index := ys.foldl (init := ({} : Std.HashMap (ExprStructEq × Nat) (Array Expr))) fun m y =>
    m.insert (key y) ((m.getD (key y) #[]).push y)
  let mut name := `_reverseShareCandidate
  while (← getEnv).contains name do name := name.appendAfter "_"
  let ref := mkConst name (d₁.levelParams.map Level.param)
  let mut exacts : Bucket := {}
  let mut param : Bucket := {}
  for x in xs do
    for y in index.getD (key x) #[] do
      if let some c ← extract v₁ v₂ x y ref base then
        if c.left.isEmpty then exacts := exacts.add base.size c else param := param.add base.size c
  let cs := (exacts.rows ++ param.rows).qsort (fun x y => x.after < y.after)
  let env ← getEnv
  let modName := fun (n : Name) =>
    ((env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!).getD env.header.mainModule
  let result := Json.mkObj [
    ("left_module", toJson (modName d₁.name).toString), ("right_module", toJson (modName d₂.name).toString),
    ("left", toJson d₁.name.toString), ("right", toJson d₂.name.toString),
    ("left_body_hash", toJson (toString (hash v₁))), ("right_body_hash", toJson (toString (hash v₂))),
    ("dag_before", toJson base.size), ("exact_count", toJson exacts.hits),
    ("parameterized_count", toJson param.hits), ("pp_is_diagnostic", toJson true),
    ("candidates", Json.arr (← cs.mapM (row · base.size)))]
  logInfo result.compress

end ReverseShare
