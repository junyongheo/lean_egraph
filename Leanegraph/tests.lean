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
  ~~TODO: understand why IO can be passed as a state...~~
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



/-
  Pass your language like so
-/
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

def runRebuild : EGraphGenericIO α <| Unit := do
  let s ← get
  let (res, s') := rebuild.run s
  set s'
  return res

def runTest (test : EGraphGenericIO α <| Unit) (testName: String := ""): IO Unit := do
  let emptyGraph : EGraph α := EGraph.empty
  let _ ← test.run emptyGraph
  -- IO.println s!"Test {testName} Completed"
  IO.println "Test Completed"



/-
  Example tests and how to run them
  These tests are NOT generic and only work on the AddMul language
  For any other languages, please write your own tests
  Individual tests can be run using the #eval runTest {your_test_here} command
  Tests can be ran in bulk by defining a list of tests and passing it to runBatchTests (see below)
  TODO: i wonder if we can write a generic test for all languages (sounds unnecessary, don't do, just wonder)

  IMPORTANT:
    Currently the rebuild operation is deferred and batched
    Therefore the user needs to call rebuild whenever needed

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

  -- Panics if not same class
  let c1 ← runLine <| checkSameClass a b "Union Test"

  printEGraph

  IO.println s!"Variables {a} and {b} in class {c1}"

#eval runTest testUnionOperation "Union"


/-
  How to run multiple tests at once
-/
def listOfTests := [
  testPushOperation,
  testUnionOperation,
]

def runBatchTests (allTests : List (EGraphIO Unit)) : IO Unit := do
  for test in allTests do
    runTest test
    IO.println "======\nNEXT TEST\n======"

#eval runBatchTests listOfTests


/-
  Test HashCons
  In other words, if we push var "a" twice, does it get hashcons'd or duplicated?
-/
def testHashCons : EGraphIO Unit := do
  IO.println "Test Hashconsing"

  let a₁ ← runLine <| push { head := AddMul.var "a", args := [] }
  let a₂ ← runLine <| push { head := AddMul.var "a", args := [] }

  let _ ← runLine <| checkSameClass a₁ a₂ "HashCons"

  printEGraph

#eval runTest testHashCons "HashCons"


/-
  Tests Congruence
  If a ≡ b, then f(a) ≡ f(b)
-/
def testCongruence : EGraphIO Unit := do
  IO.println "Test Congruence Closure"

  let a ← runLine <| push { head := AddMul.var "a", args := [] }
  let b ← runLine <| push { head := AddMul.var "b", args := [] }

  printEGraph

  let fa ← runLine <| push { head := AddMul.add, args := [a] }
  let fb ← runLine <| push { head := AddMul.add, args := [b] }

  printEGraph

  let _ ← runLine <| union a b

  let _ ← runRebuild

  printEGraph

  let _ ← runLine <| checkSameClass fa fb "Congruence"

  printEGraph

#eval runTest testCongruence "Congruence"

/-
  Test if congruence propagates
  Have variables a and b
  Have fa, fb with a, b as argument
  Have ga, gb with a, b as argument

  We saw in the previous test(s) that if union a b
  (a ≡ b) and (f(a) ≡ f(b))

  Test if union a b also propagates to g(f(a)) ≡ g(f(b))
-/
def testCongruencePropagation : EGraphIO Unit := do
  IO.println "Test Nested Congruence"

  let a ← runLine <| push { head := AddMul.var "a", args := [] }
  let b ← runLine <| push { head := AddMul.var "b", args := [] }

  let fa ← runLine <| push { head := AddMul.add, args := [a] }
  let fb ← runLine <| push { head := AddMul.add, args := [b] }

  let ga ← runLine <| push { head := AddMul.mul, args := [fa] }
  let gb ← runLine <| push { head := AddMul.mul, args := [fb] }

  let _ ← runLine <| union a b

  let _ ← runRebuild

  let _ ← runLine <| checkSameClass ga gb "Nested congruence"

  printEGraph

#eval runTest testCongruencePropagation "Nested Congruence"

/-
  Test if (a ≡ b) → (b ≡ c) → (a ≡ c)
-/
def testUnionTransitive : EGraphIO Unit := do
  IO.println "Test Union Transitivity"

  let a ← runLine <| push { head := AddMul.var "a", args := [] }
  let b ← runLine <| push { head := AddMul.var "b", args := [] }
  let c ← runLine <| push { head := AddMul.var "c", args := [] }

  let _ ← runLine <| union a b
  let _ ← runLine <| union b c

  let _ ← runRebuild

  let _ ← runLine <| checkSameClass a c "Union transitive"

  printEGraph

#eval runTest testUnionTransitive

def EGraphOperationTests := [
  testPushOperation,
  testUnionOperation,
  testHashCons,
  testCongruence,
  testCongruencePropagation,
  testUnionTransitive,
]

#eval runBatchTests EGraphOperationTests
