import Leanegraph.core.egraphs
import Leanegraph.core.rewrite

/-
  This file contains the helper functions and framework for running tests.
  This file does not contain any tests
  Refer to egraphtests.lean and rewritetests.lean
-/

-- Constraints on α
variable {α : Type _} [DecidableEq α] [BEq α] [Hashable α]

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
| lit : Nat → AddMul
| var   : String → AddMul
| add   : AddMul
| mul   : AddMul
deriving DecidableEq, Hashable, BEq, Repr

instance : ToString AddMul where
  toString
  | .lit n => s!"{n}"
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

def runLineUnit (line : EGraphM α <| Unit) : EGraphGenericIO α <| Unit  := do
  let s ← get
  let (res, s') := line.run s
  set s'
  return

/-
-- Deprecated: pass rebuild to "runLineUnit <| rebuild"
def runRebuild : EGraphGenericIO α <| Unit := do
  let s ← get
  let (res, s') := rebuild.run s
  set s'
  return res
-/

def runTest (test : EGraphGenericIO α <| Unit) (testName: String := ""): IO Unit := do
  let emptyGraph : EGraph α := EGraph.empty
  let _ ← test.run emptyGraph
  IO.println s!"Test {testName} Completed"
  IO.println "Test Completed"




/-

-/

def runSchedule
      {α : Type _} [DecidableEq α] [BEq α] [Hashable α]
      (rules : List (Rule α))
      (limit : Nat := 10)
    :  EGraphGenericIO α <| Unit := do -- this is some ugly formatting
  let mut i := 0
  while i < limit do
    let egStart ← get
    let sizeStart := egStart.size

    -- Apply all rules
    for r in rules do
      runLineUnit <| rewrite (α := α) (r := r)

    let egEnd ← get
    let sizeEnd := egEnd.size

    if sizeStart == sizeEnd then
      -- Fixed point reached (graph didn't grow)
      -- Note: In a real system we'd check if *new classes* were added,
      -- matching size is a rough proxy for "nothing happened".
      return ()

    i := i + 1

/-
  Note for horrendous type bug in case it happens again
  '''
  Application type mismatch: The argument
  r
  has type
    Rule α
  of sort `Type` but is expected to have type
    Type
  of sort `Type 1` in the application
    rewrite r
  '''

  Was fixed by rewrite (α := α) (r := r)
  or just
  Because rewrite r makes lean think that i'm passing r as the type
-/
