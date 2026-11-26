/-
Prints the full statement of Mathlib declarations, as Lean itself understands them:
every type inferred, every implicit variable written out.

It reads declaration names on standard input, one per line, and answers each with one
line of JSON on standard output:

  {"name": "Real.continuousOn_cos", "signature": "Real.continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s"}
  {"name": "No.such.thing", "error": "unknown declaration"}

A line "uses <name>" is answered with what that declaration refers to, separately for its
statement and for its proof (or, for a definition, its body):

  {"name": "…", "statement": ["Real.cos", "ContinuousOn", …], "proof": ["Real.continuous_cos", …]}

A line "role <name>" is answered with whether the theorem is proved by reflexivity alone:

  {"name": "…", "rfl": true}

The first line it prints, once Mathlib is loaded, is {"ready": true}.

Run it from a Mathlib checkout whose compiled files are present:

  cd data/mathlib4 && lake env lean --run ../../lean/Signatures.lean
-/
import Lean

open Lean Meta

/-- The statement of `name`, printed the way `#check` prints it. -/
def signature (name : Name) : MetaM String := do
  let fmt ← PrettyPrinter.ppSignature name
  return fmt.fmt.pretty (width := 1000000)

/-- The proof with its leading `fun x => …` and annotations removed. -/
partial def proofCore (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => proofCore b
  | .mdata _ b => proofCore b
  | e => e

/-- Whether a theorem's proof is just reflexivity: Lean accepts the statement by unfolding
definitions, with no argument at all. -/
def provedByRfl (info : ConstantInfo) : Bool :=
  match info with
  | .thmInfo v =>
    match (proofCore v.value).getAppFn with
    | .const n _ => n == ``rfl || n == ``Eq.refl || n == ``Iff.rfl || n == ``Iff.refl || n == ``HEq.rfl || n == ``HEq.refl
    | _ => false
  | _ => false

/-- Namespaces whose scoped notation is switched on before printing. -/
def notationScopes : List Name := [
  `Real, `NNReal, `ENNReal, `Nat, `BigOperators, `Topology, `Filter, `Uniformity, `Interval,
  `EuclideanGeometry, `RealInnerProductSpace, `InnerProductSpace, `ComplexConjugate,
  `MeasureTheory, `ProbabilityTheory, `Polynomial, `Matrix, `Kronecker, `Pointwise, `Finset,
  `ContDiff, `Manifold, `symmDiff, `DirectSum, `TensorProduct, `Cardinal, `Ordinal, `NumberField]

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  -- Notation is printed by code that lives in the imported files: let it run.
  enableInitializersExecution
  let env ← importModules #[{ module := `Mathlib }] {} (trustLevel := 0) (loadExts := true)
  -- A coercion is printed with the type it lands in: `(↑(r / s) : ℂ)`, not a bare `↑(r / s)`.
  -- Without that, a statement such as `↑(r / s) = ↑r / ↑s` does not say what it is about.
  let options : Options := ({} : Options).setBool `pp.coercions.types true |>.setBool `pp.funBinderTypes true
  let ctx : Core.Context := { fileName := "<signatures>", fileMap := default, maxHeartbeats := 0, options }
  -- Much of Mathlib's notation is switched on per file with `open scoped …`. Switch the common
  -- ones on here, so that statements are printed as their authors wrote them: `π`, `∠ A B C`,
  -- `⟪x, y⟫_ℝ`, `𝓝 a`, `ℝ≥0`, `n !`, rather than `Real.pi`, `EuclideanGeometry.angle A B C`, …
  let (_, opened) ← (notationScopes.forM activateScoped : CoreM Unit).toIO ctx { env }
  let env := opened.env
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn (Json.mkObj [("ready", true)]).compress
  stdout.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break -- end of input
    let trimmed := line.trimAscii
    let text : String := trimmed.copy
    if text.isEmpty then continue
    -- "role <name>": is this theorem proved by `rfl`, that is, true by unfolding definitions?
    if text.startsWith "role " then
      let asked : String := (text.drop 5).copy
      let name := (text.drop 5).toName
      let reply := match env.find? name with
        | none => Json.mkObj [("name", asked), ("error", "unknown declaration")]
        | some info => Json.mkObj [("name", asked), ("rfl", provedByRfl info)]
      stdout.putStrLn reply.compress
      stdout.flush
      continue
    -- "uses <name>": which declarations its statement mentions, and which its proof or body.
    if text.startsWith "uses " then
      let asked : String := (text.drop 5).copy
      let name := (text.drop 5).toName
      let names (e : Expr) : Json := Json.arr (e.getUsedConstants.map fun n => Json.str n.toString)
      let reply := match env.find? name with
        | none => Json.mkObj [("name", asked), ("error", "unknown declaration")]
        | some info =>
          let body : Option Expr := match info with
            | .thmInfo v => some v.value
            | .defnInfo v => some v.value
            | .opaqueInfo v => some v.value
            | _ => none
          Json.mkObj [("name", asked), ("statement", names info.type), ("proof", (body.map names).getD (Json.arr #[]))]
      stdout.putStrLn reply.compress
      stdout.flush
      continue
    let name := trimmed.toName
    let reply ← try
        if env.contains name then
          let (sig, _) ← (signature name).run'.toIO ctx { env }
          pure (Json.mkObj [("name", text), ("signature", sig)])
        else
          pure (Json.mkObj [("name", text), ("error", "unknown declaration")])
      catch e =>
        pure (Json.mkObj [("name", text), ("error", toString e)])
    stdout.putStrLn reply.compress
    stdout.flush
