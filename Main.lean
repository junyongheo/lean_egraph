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
  let _ ← runTest integ_part1 "Folds"
  let _ ← runTest integ_part3 "intpt3"
  let _ ← runTest math_simplify_factor "mathsimplifyfactor"
  let _ ← runTest diff_power_simple "diffpowersimple"
  let _ ← runTest math_simplify_root "mathsimplifyroot"
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
