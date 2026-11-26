/-
The steps of one proof, as Lean sees them.

  lake env lean --run Steps.lean <source file> <declaration name>

Lean only knows what is left to prove at each point of a proof while it checks that proof;
the compiled library does not keep it. So this program checks the source file again, command
by command, with recording switched on, stops at the declaration asked for, and prints one
line of JSON:

  {"name": …, "steps": [{"start", "stop", "kind", "text", "before": [goal], "after": [goal]}]}
  goal = {"id", "case", "target", "hyps": [{"name", "type", "inst", "prop"}]}

Among the steps, with kind "@const" and a "name": each identifier in the proof that Lean
resolved to a declaration, with that declaration's full name. This is how a reader of
`rw [sub_eq_zero]` can be shown what `sub_eq_zero` says.

or {"name": …, "error": …}. Every recorded tactic step is given, containers included (a
`by` block, a whole `rw [a, b]` next to its parts): lib/steps.js chooses what to show.
-/
import Lean
open Lean Elab Meta

def goalJson (goal : MVarId) : MetaM Json := goal.withContext do
  let mut hyps : Array Json := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let type ← instantiateMVars d.type
    hyps := hyps.push <| Json.mkObj [
      ("name", if d.userName.hasMacroScopes then s!"{d.userName.eraseMacroScopes}✝" else d.userName.toString),
      ("type", (← ppExpr type).pretty 100000),
      ("inst", toJson d.binderInfo.isInstImplicit),
      ("prop", toJson (← isProp type))]
  let target ← instantiateMVars (← goal.getType)
  return Json.mkObj [
    ("id", goal.name.toString),
    ("case", (← goal.getTag).toString),
    ("target", (← ppExpr target).pretty 100000),
    ("hyps", Json.arr hyps)]

/-- Checks commands one at a time until `decl` exists; the record of the command that made it. -/
partial def recordOf (decl : Name) : Frontend.FrontendM (Option (PersistentArray InfoTree)) := do
  modify fun s => { s with commandState.infoState.trees := {} }
  let done ← Frontend.processCommand
  let state := (← get).commandState
  if state.env.contains decl then return some state.infoState.trees
  if done then return none
  recordOf decl

unsafe def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let say (j : Json) : IO Unit := do out.putStrLn j.compress; out.flush
  let [file, asked] := args | say (Json.mkObj [("error", "usage: Steps.lean <file> <name>")])
  let decl := asked.toName
  let fail (why : String) := say (Json.mkObj [("name", asked), ("error", why)])
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← try IO.FS.readFile file catch _ => return (← fail "no such source file")
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  -- one thread, so that the record of a proof is complete when its command returns
  let options : Options := ({} : Options).setBool `Elab.async false
  let commandState := { Command.mkState env messages options with infoState.enabled := true }
  let (trees?, _) ← (recordOf decl |>.run { inputCtx }).run { commandState, parserState, cmdPos := parserState.pos }
  let some trees := trees? | fail "not declared in this file"
  let stepsRef ← IO.mkRef (#[] : Array Json)
  for tree in trees do
    tree.visitM' (postNode := fun ctx info _ => do
      if ctx.parentDecl? != some decl then return
      if let .ofTermInfo term := info then
        if term.stx.isIdent then
          if let (some range, some const) := (term.stx.getRange? (canonicalOnly := true), term.expr.getAppFn.constName?) then
            stepsRef.modify (·.push <| Json.mkObj [
              ("start", range.start.byteIdx), ("stop", range.stop.byteIdx),
              ("kind", "@const"), ("text", ""), ("name", const.toString),
              ("before", Json.arr #[]), ("after", Json.arr #[])])
        return
      let .ofTacticInfo step := info | return
      let some range := step.stx.getRange? (canonicalOnly := true) | return
      -- as in the statements: a coercion is printed with the type it lands in, a bound variable with its type
      let options := ctx.options.setBool `pp.coercions.types true |>.setBool `pp.funBinderTypes true
      let goals (mctx : MetavarContext) (ids : List MVarId) : IO Json := do
        try
          -- names in full, as in the statements, whatever namespace the proof was written in
          return Json.arr (← ({ ctx with mctx, options, currNamespace := .anonymous, openDecls := [] }).runMetaM {} (ids.toArray.mapM goalJson))
        catch _ => return Json.arr #[]
      let before ← goals step.mctxBefore step.goalsBefore
      let after ← goals step.mctxAfter step.goalsAfter
      stepsRef.modify (·.push <| Json.mkObj [
        ("start", range.start.byteIdx), ("stop", range.stop.byteIdx),
        ("kind", step.stx.getKind.toString),
        ("text", String.Pos.Raw.extract input range.start range.stop),
        ("before", before), ("after", after)]))
  say (Json.mkObj [("name", asked), ("steps", Json.arr (← stepsRef.get))])
