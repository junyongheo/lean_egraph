import Leanegraph.egraphs
import Leanegraph.rewrite


-- Constraints on α
variable {α : Type _} [DecidableEq α] [BEq α] [Hashable α]


/-
  Tests for the EGraph implementation
-/


open EGraph

/-
  Allows the user to define a language for testing
  The monstrosity below was a curious test. Luckily for us it doesn't work.
-/
abbrev EGraphGenericIO := (λL [DecidableEq L][Hashable L][BEq L] ↦ StateT (EGraph L) IO)
-- abbrev EGraphGenericIO:= (λc [DecidableEq c][Hashable c] ↦ ((λa ↦ StateT a IO) <| (λb [DecidableEq b][Hashable b] => EGraph b) <| c))

/-
  We define a language for basic tests on the e-graph.
  We further define a ToString instance for better debug/print-ability.
  The EGraph is bundled together with IO in a StateT
  TODO: understand why IO can be passed as a state...
-/
inductive AddMul where
| const : Nat → AddMul
| var   : String → AddMul
| add   : AddMul
| mul   : AddMul
deriving DecidableEq, Hashable, BEq, Repr

instance : ToString AddMul where
  toString
  | .const n => s!"{n}"
  | .var s   => s
  | .add     => "+"
  | .mul     => "*"

-- A version of EGraphM that allows IO (printing)
-- abbrev EGraphTest := StateT (EGraph AddMul) IO
abbrev EGraphIO := EGraphGenericIO AddMul





/-
  Helper Functions for Testing
  runLine
    - Executes one line at a time.
    - Gets state → runs one line → sets state → returns new egraph
  checkSameClass
    - Takes two E-Class Ids and an optional test name. Checks if the two E-Class IDs map to the same canonical ID.
  printEGraph
    - ...
  runTest
    - Takes a test
    - Creates a new EGraph, then runs the test
-/

def checkSameClass (id1 id2 : EClassId) (test : String := "") : EGraphM α <| EClassId := do
  let c1 ← lookupCanonicalEClassId id1
  let c2 ← lookupCanonicalEClassId id2
  if c1 ≠ c2 then
    panic! s!"Test Failed: {test} | Expected {c1} == {c2}"
  else
    return c1

-- I'm not too worried about for loops anymore...
def printEGraph : EGraphIO Unit := do
  let eg ← get
  IO.println "=== E-Graph State ==="
  IO.println s!"Size: {eg.uf.size}"

  for (id, eclass) in eg.ecmap.toList do
    IO.println s!"ID {id} :: Nodes: {repr eclass.nodes}"

  IO.println "====================\n"
  -- IO.println "\n\n"

def runLine (line : EGraphM α <| EClassId) : EGraphGenericIO α <| EClassId  := do
  let s ← get
  let (res, s') := line.run s
  set s'
  return res

def runTest (test : EGraphGenericIO α <| Unit) (testName: String := ""): IO Unit := do
  let emptyGraph : EGraph α := EGraph.empty
  let _ ← test.run emptyGraph
  IO.println s!"Test {testName} Completed"



/-
  Example tests and how to run them
  These tests are NOT generic and only work on the AddMul language
  For any other languages, please write your own tests
  Individual tests can be run using the #eval runTest {your_test_here} command
  Tests can be ran in bulk by defining a list of tests and passing it to runAllTests (see below)
-/

-- Tests push operation.
-- Expect: 3 classes with 1 term each
def testPushOperation : EGraphIO Unit := do

  IO.println "Test Push"
  printEGraph

  let _ ← runLine <| push { head := AddMul.var "a", args := []}
  let _ ← runLine <| push { head := AddMul.var "b", args := []}
  let _ ← runLine <| push { head := AddMul.var "c", args := []}

  printEGraph

#eval runTest testPushOperation "Push"

-- Tests union operation.
-- Expect: 2 classes, with 1 and 2 terms respectively.
def testUnionOperation : EGraphIO Unit := do

  IO.println "Test Union"
  IO.println "\nBefore: "
  printEGraph

  let a ← runLine <| push { head := AddMul.var "a", args := [] }
  let b ← runLine <| push { head := AddMul.var "b", args := [] }
  let _ ← runLine <| push { head := AddMul.var "c", args := [] }

  let _ ← runLine <| union a b

  let c1 ← runLine <| checkSameClass a b "Union Test"

  printEGraph

  IO.println s!"Variables {a} and {b} both in class {c1}"

#eval runTest testUnionOperation "Union"


def listOfTests := [
  testPushOperation,
  testUnionOperation,
]

def runAllTests (allTests : List (EGraphIO Unit)) : IO Unit := do
  for test in allTests do
    runTest test
    IO.println "======\nNEXT TEST\n======"

#eval runAllTests listOfTests
