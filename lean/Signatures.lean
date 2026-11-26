/-
Prints the full statement of Mathlib declarations, as Lean itself understands them:
every type inferred, every implicit variable written out.

It reads declaration names on standard input, one per line, and answers each with one
line of JSON on standard output:

  {"name": "Real.continuousOn_cos", "signature": "Real.continuousOn_cos {s : Set ℝ} : ContinuousOn Real.cos s"}
  {"name": "No.such.thing", "error": "unknown declaration"}

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
  let ctx : Core.Context := { fileName := "<signatures>", fileMap := default, maxHeartbeats := 0 }
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
