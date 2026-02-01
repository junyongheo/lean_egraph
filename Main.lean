import Leanegraph.core
import Leanegraph.framework
-- import Leanegraph.languages.prop
-- import Leanegraph.tests.proptests
-- import Leanegraph.tests.egraphtests
import Leanegraph.tests.mathtest



def main : IO Unit := do
  /-
  let _ ← runBatchTests EGraphOperationTests

  IO.println s!"Proposition Tests"

  let _ ← runTest testContrapositive "Contrapositive"
  let _ ← runTest testProveChain     "Chain"
  let _ ← runTest testConstFold      "Constant Fold"
  -/
  -- let _ ← runTest testAnalysisCF "CF"
  let ts← IO.monoMsNow
  let _ ← runTest integ_part1 "Folds"
  let te← IO.monoMsNow
  IO.println s!"Test IntegPt1: {te - ts} ms"
  let ts← IO.monoMsNow
  let _ ← runTest integ_part3 "intpt3"
  let te← IO.monoMsNow
  IO.println s!"Test IntegPt3: {te - ts} ms"
  let ts← IO.monoMsNow
  let _ ← runTest math_simplify_factor "mathsimplifyfactor"
  let te← IO.monoMsNow
  IO.println s!"Test MathSimpFac: {te - ts} ms"
  let ts← IO.monoMsNow
  let _ ← runTest diff_power_simple "diffpowersimple"
  let te← IO.monoMsNow
  IO.println s!"Test DiffPowSimp: {te - ts} ms"
  let ts← IO.monoMsNow
  let _ ← runTest math_simplify_root "mathsimplifyroot"
  let te← IO.monoMsNow
  IO.println s!"Test MathSimpRoot: {te - ts} ms"
-- #eval runTest groupTest


-- #eval runTest diff_power_simple
/-
math_simplify_factor
math_diff_same
math_diff_simple1
diff_power_simple
integ_part1
integ_part3
-/
