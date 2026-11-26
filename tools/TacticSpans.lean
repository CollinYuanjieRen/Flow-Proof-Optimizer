module
import Lean
import all Lean.Shell

open Lean Elab Frontend

/-- Elaborate the source in order and collect tactic information only in the command
containing the requested line. Byte offsets refer to the unmodified UTF-8 file. -/
private def inspect (line : Nat) : FrontendM Unit := do
  let ctx ← getInputContext
  repeat
    let s ← getCommandState
    let ps ← getParserState
    let scope := s.scopes.head!
    let parserCtx := { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
                       openDecls := scope.openDecls : Parser.ParserModuleContext }
    let (cmd, next, messages) := Parser.parseCommand ctx parserCtx ps s.messages
    if Parser.isTerminalCommand cmd then throw <| IO.userError "no declaration at line"
    let finish := ctx.fileMap.toPosition (cmd.getTailPos?.getD next.pos)
    let selected := finish.line >= line
    updateCmdPos
    setParserState next
    setCommandState { s with messages, infoState := { enabled := selected } }
    elabCommandAtFrontend cmd
    let state ← getCommandState
    if state.messages.hasErrors then
      for msg in state.messages.toList do
        if msg.severity == .error then IO.eprintln (← msg.toString)
      throw <| IO.userError "source elaboration failed"
    if selected then
      for tree in state.infoState.substituteLazy.get.trees do
        tree.visitM' (postNode := fun _ info _ => do
          let .ofTacticInfo t := info | return
          let some r := t.stx.getRange? (canonicalOnly := true) | return
          unless t.stx.getHeadInfo matches .original .. do return
          let row := Json.mkObj [("start", toJson r.start.byteIdx), ("end", toJson r.stop.byteIdx),
            ("kind", toJson t.stx.getKind.toString),
            ("before", toJson (t.goalsBefore.map (·.name.toString))),
            ("after", toJson (t.goalsAfter.map (·.name.toString)))]
          IO.println row.compress)
      return

public unsafe def main (args : List String) : IO Unit := do
  let path :: moduleName :: line :: settings := args
    | throw <| IO.userError "expected: file module line [option=value ...]"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let ctx := Parser.mkInputContext (← IO.FS.readFile path) path
  let opts ← settings.foldlM setConfigOption {}
  let opts := opts.setBool `Elab.async false
  let (header, ps, msgs) ← Parser.parseHeader ctx
  let (env, msgs) ← processHeader header opts msgs ctx (mainModule := moduleName.toName)
  let cmd := Command.mkState env msgs opts
  let some n := line.toNat? | throw <| IO.userError "expected a line number"
  discard <| ((inspect n).run { inputCtx := ctx }).run
    { commandState := cmd, parserState := ps, cmdPos := ps.pos }
