import Lean
open Lean

/-- Run with `lake env lean --run LinkedRoots.lean` in a built project.
Read a JSON object with modules, roots, and an optional rootModule (default
Main) from stdin. Each output row is
[name, [module recorded by Lean, project names used by its type and value]].
External modules terminate traversal. Source-only uses and registrations
are outside this graph. -/
private structure Request where
  rootModule : Option String
  modules : Array String
  roots : List String
  deriving FromJson

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let request : Request ← IO.ofExcept (Json.parse (← (← IO.getStdin).readToEnd) >>= fromJson?)
  let project := Std.HashSet.ofList (request.modules.toList.map String.toName)
  let env ← importModules #[{module := (request.rootModule.getD "Main").toName}] {}
  let moduleNames := env.header.moduleNames
  let isProject := moduleNames.map project.contains
  let owner (n : Name) := do
    let i ← env.getModuleIdxFor? n
    if isProject[i.toNat]! then some moduleNames[i.toNat]! else none
  let mut todo := request.roots.map String.toName
  let mut seen : Std.HashSet Name := {}
  while let n :: rest := todo do
    todo := rest
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | throw <| IO.userError s!"missing {n}"
    let some m := owner n | throw <| IO.userError s!"outside project {n}"
    let edges := c.getUsedConstantsAsSet.toList.filter (fun u => (owner u).isSome)
    todo := edges ++ todo
    IO.println (toJson (n.toString, m.toString, edges.map Name.toString)).compress
