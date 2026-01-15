import Leanegraph.core.egraphs
import Leanegraph.core.rewrite
import Leanegraph.framework.helpers
import Leanegraph.framework.macros
-- import Leanegraph.languages.addmul
-- import Leanegraph.languages.lambda
import Leanegraph.languages.prop
import Leanegraph.tests.proptests



def main : IO Unit := do
  IO.println s!"Tests Time..."

  let _ ← runTest testContrapositive "Contrapositive"
  let _ ← runTest testProveChain     "Chain"
  let _ ← runTest testConstFold      "Constant Fold"
