import Leanegraph.core
import Leanegraph.framework
import Leanegraph.languages.addmul

open EGraph

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

  let _ ← runLine <| pushRun { head := AddMul.var "a", args := []}
  let _ ← runLine <| pushRun { head := AddMul.var "b", args := []}
  let _ ← runLine <| pushRun { head := AddMul.var "c", args := []}

  printEGraph

#eval runTest testPushOperation "Push"

-- Tests union operation.
-- Expect: 2 classes, with 1 and 2 terms respectively.
def testUnionOperation : EGraphIO Unit := do
  IO.println "Test Union"
  IO.println "\nBefore: "
  printEGraph

  let a ← runLine <| pushRun { head := AddMul.var "a", args := [] }
  let b ← runLine <| pushRun { head := AddMul.var "b", args := [] }
  let _ ← runLine <| pushRun { head := AddMul.var "c", args := [] }

  let _ ← runLine <| unionRun a b

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
  In other words, if we pushRun var "a" twice, does it get hashcons'd or duplicated?
-/
def testHashCons : EGraphIO Unit := do
  IO.println "Test Hashconsing"

  let a₁ ← runLine <| pushRun { head := AddMul.var "a", args := [] }
  let a₂ ← runLine <| pushRun { head := AddMul.var "a", args := [] }

  let _ ← runLine <| checkSameClass a₁ a₂ "HashCons"

  printEGraph

#eval runTest testHashCons "HashCons"


/-
  Tests Congruence
  If a ≡ b, then f(a) ≡ f(b)
-/
def testCongruence : EGraphIO Unit := do
  IO.println "Test Congruence Closure"

  let a ← runLine <| pushRun { head := AddMul.var "a", args := [] }
  let b ← runLine <| pushRun { head := AddMul.var "b", args := [] }

  printEGraph

  let fa ← runLine <| pushRun { head := AddMul.add, args := [a] }
  let fb ← runLine <| pushRun { head := AddMul.add, args := [b] }

  printEGraph

  let _ ← runLine <| unionRun a b

  let _ ← runLineUnit <| rebuildRun

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

  let a ← runLine <| pushRun { head := AddMul.var "a", args := [] }
  let b ← runLine <| pushRun { head := AddMul.var "b", args := [] }

  let fa ← runLine <| pushRun { head := AddMul.add, args := [a] }
  let fb ← runLine <| pushRun { head := AddMul.add, args := [b] }

  let ga ← runLine <| pushRun { head := AddMul.mul, args := [fa] }
  let gb ← runLine <| pushRun { head := AddMul.mul, args := [fb] }

  let _ ← runLine <| unionRun a b

  let _ ← runLineUnit <| rebuildRun

  let _ ← runLine <| checkSameClass ga gb "Nested congruence"

  printEGraph

#eval runTest testCongruencePropagation "Nested Congruence"

/-
  Test if (a ≡ b) → (b ≡ c) → (a ≡ c)
-/
def testUnionTransitive : EGraphIO Unit := do
  IO.println "Test Union Transitivity"

  let a ← runLine <| pushRun { head := AddMul.var "a", args := [] }
  let b ← runLine <| pushRun { head := AddMul.var "b", args := [] }
  let c ← runLine <| pushRun { head := AddMul.var "c", args := [] }

  let _ ← runLine <| unionRun a b
  let _ ← runLine <| unionRun b c

  let _ ← runLineUnit <| rebuildRun

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

-- TODO: fancy tests that make the egraphs unhappy

-- Just curious if this works
def testCycle : EGraphIO Unit := do
  let a ← runLine <| pushRun { head := AddMul.var "a", args := []}
  let o ← runLine <| pushRun { head := AddMul.lit 1, args := []}
  let b ← runLine <| pushRun { head := AddMul.add, args := [a,o]}

  printEGraph

  let _ ← runLine <| unionRun a b

  printEGraph

  let _ ← runLineUnit <| rebuildRun

  printEGraph

#eval runTest testCycle
