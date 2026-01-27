import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.framework.macros
import Leanegraph.languages.addmul
import Leanegraph.languages.lambda
-- import Leanegraph.languages.prop
-- import Leanegraph.tests.proptests
import Leanegraph.tests.egraphtests
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
  let _ ← runTest integ_part2 "aehea"
  let _ ← runTest integ_part3 "ateha"
