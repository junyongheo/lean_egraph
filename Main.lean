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
  -- let _ ← runTest integ_part1 "Folds"
  -- let _ ← runTest integ_part3 "aehea"
  -- let _ ← runTest math_simplify_factor "ateha"
  let _ ← runTest diff_power_simple
-- #eval runTest groupTest
