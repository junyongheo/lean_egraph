import Leanegraph.tests.rewritetests

open EGraph

def simpleCost : costFn AddMul
  | .lit _ => 1
  | .var _ => 1
  | .add   => 1
  | .mul   => 1

-- 2. The Extraction Test
def testExtraction : EGraphIO Unit := do
  IO.println "\nTest: Extraction (x * 0 → 0)"

  let mulZero : Rule AddMul := r* (?"x") === mulP (?"x") (litP 0)

  -- x * 0 → 0
  -- such beautifully lined up things
  let x  ← runLine <| push { head := .var "x", args := []     }
  let z  ← runLine <| push { head := .lit 0,   args := []     }
  let st ← runLine <| push { head := .mul,     args := [x, z] }

  eqSat [mulZero]
  printEGraph
  -- Get the cost extraction map
  let eg ← get
  let costMap := extract eg simpleCost

  --
  let canonID := eg.uf.find! st |>.snd

  match costMap.get? canonID with
  | none => IO.println "not found error..."
  | some (cost, node) =>
    IO.println s!"Lowest Cost: {cost}"
    IO.println s!"Best Node: {repr node}\n"

#eval runTest testExtraction "Extraction Test"
