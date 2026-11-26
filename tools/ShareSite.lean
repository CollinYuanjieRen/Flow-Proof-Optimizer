module
public meta import Lean
public meta section

open Lean Meta Elab Tactic

/-- Inspect one original proof in its elaboration context. Only used during discovery. -/
elab "share_site " tag:str scope:str " => " body:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← goal.getType
  evalTactic body
  let v ← instantiateMVars (mkMVar goal)
  try
    let result ← Closure.mkValueTypeClosure type v false
    let opts := (← getOptions).set `pp.width (110 : Nat) |>.set `pp.funBinderTypes true
    let mut binders := #[]
    let mut premises := #[]
    let localInsts ← getLocalInstances
    for arg in result.exprArgs do
      let decl ← arg.fvarId!.getDecl
      let raw := decl.userName.eraseMacroScopes.toString
      let inaccessible := decl.userName.hasMacroScopes || raw.startsWith "_"
      let binder := if inaccessible then "arg" ++ toString binders.size else raw
      let argType ← withOptions (fun _ => opts.set `pp.universes true) <| ppExpr decl.type
      let argType := argType.pretty
      if ← isProof arg then
        if let some n := decl.type.consumeMData.getAppFn.constName? then
          premises := premises.push n.toString
      -- Unnamed letI/haveI locals can all print as "this", with default binder info.
      let head := if raw == "this" && localInsts.any (·.fvar == arg) then "[" ++ argType ++ "]"
        else if decl.binderInfo == .instImplicit then "[" ++ binder ++ " : " ++ argType ++ "]"
        else "(" ++ binder ++ " : " ++ argType ++ ")"
      binders := binders.push head
    let typ ← instantiateMVars type
    -- A caller can supply its premise as an expression inside the target, without
    -- first binding it to a local name. Preserve the spelling of such proof arguments.
    let mut embedded := #[]
    let parts ← IO.mkRef #[]
    typ.forEach fun e => do
      if e.isApp && !e.hasLooseBVars && (e.getAppFn.isConst || e.getAppFn.isFVar) then parts.modify (·.push e)
    for part in ← parts.get do
      if ← isProof part then
        if let some head := (← inferType part).consumeMData.getAppFn.constName? then
          let pretty ← withOptions (fun o => o.set `pp.proofs true) <| ppExpr part
          embedded := embedded.push (head.toString, pretty.pretty)
    let env ← getEnv
    let imports := (scope.getString.splitOn " ").filter fun n => (env.getModuleIdx? n.toName).isSome
    let goalText ← withOptions (fun _ => opts) <| ppExpr typ
    let row := Json.mkObj [
      ("id", toJson tag.getString), ("goal", toJson goalText.pretty), ("binders", toJson binders), ("imports", toJson imports),
      ("premises", toJson premises), ("embedded", toJson embedded),
      ("symbols", toJson ((typ.getUsedConstants.map Name.toString).qsort (· < ·)))]
    logInfo m!"SHARE_SITE {row.compress}"
  catch _ =>
    logInfo m!"SHARE_SITE_FAIL {tag.getString}"
