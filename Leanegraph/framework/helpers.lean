import Leanegraph.core
import Leanegraph.framework.parser
/-
  This file contains the helper functions and framework for execution and running tests.
-/

-- Constraints on α
variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [Inhabited D]

open EGraph

/-
  Allows the user to define a language for testing
  The monstrosity below was a curious test. Luckily for us it doesn't work.
-/
abbrev EGraphGenericIO := (λ L D [DecidableEq L][Hashable L] ↦ StateT (EGraph L D) IO)
-- abbrev EGraphGenericIO:= (λc [DecidableEq c][Hashable c] ↦ ((λa ↦ StateT a IO) <| (λb [DecidableEq b][Hashable b] => EGraph b) <| c))


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

def checkSameClass (id1 id2 : EClassId) (test : String := "") : EGraphM α D <| EClassId := do
  let c1 ← lookupCanonicalEClassId id1
  let c2 ← lookupCanonicalEClassId id2
  if c1 ≠ c2 then
    panic! s!"Test Failed: {test} | Expected {c1} == {c2}"
  else
    return c1



-- I'm not too worried about for loops anymore...
def printEGraph : EGraphGenericIO α (D := D) <| Unit := do
  let eg ← get
  IO.println "=== E-Graph State ==="
  IO.println s!"Size: {eg.uf.size}"

  for (id, eclass) in eg.ecmap.toList do
    IO.println s!"ID {id} :: Nodes: {repr eclass.nodes}"

  IO.println "====================\n"
  -- IO.println "\n\n"

def runLine (line : EGraphM α D <| EClassId) : EGraphGenericIO α (D := D) <| EClassId  := do
  let s ← get
  let (res, s') := line.run s
  set s'
  return res

def runLineUnit (line : EGraphM α D <| Unit) : EGraphGenericIO α (D := D) <| Unit  := do
  let s ← get
  let (_res, s') := line.run s
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

def runTest (test : EGraphGenericIO α (D := D) <| Unit) (testName: String := ""): IO Unit := do
  let emptyGraph : EGraph α D := EGraph.empty
  let _ ← test.run emptyGraph
  IO.println s!"Test {testName} Completed"
  IO.println "Test Completed"




/-

-/
def eqSat
      {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
      {D : Type _}
      [Analysis α D]
      [Inhabited D]
      (rules : List (Rule α D))
      (limit : Nat := 10)
    : EGraphGenericIO α (D := D) Unit := do
  let mut i := 0
  while i < limit do
    let egStart ← get

    let numClassesStart := egStart.uf.size
    let numNodesStart   := egStart.size

    for r in rules do
      runLineUnit <| rewrite (α := α) (D := D) (r := r)

    runLineUnit <| rebuild (Analysis.join (α := α)) (Analysis.modify)

    -- printEGraph

    let egEnd ← get
    let numClassesEnd := egEnd.uf.size
    let numNodesEnd   := egEnd.size
    if numClassesStart == numClassesEnd && numNodesStart == numNodesEnd then
      return ()

    i := i + 1

open ExprParser

/-
  Idea: Since SExpr is structured as a list holding lists or atoms
  If encounter atom: push the appropriate term onto the graph
  If encounter list: get the op and the args, and recurse on the args

  Since we recurse on the args with the function, and the atoms return with a push,
  we should be returning EClassId (what push returns)

  Using an EGraphM, we pass the state along the recursions. Make sure to call ← get.

-/
def buildEGFromSExpr (sx : SExpr) : EGraphM α D EClassId := do
  match sx with
  /-
    Atom is all op and arg
  -/
  | .atom s =>

    sorry
  | .list [] =>
    -- lift the arg strings into the appropriate versions
    sorry
  -- Parse elements of the list...
  | .list (head :: tail) =>
    match head with
    | .atom op =>
      -- match FromOp op with
      -- runLine <| pushRun {head := op, args := (map buildEGFromSExpr to tail)}
      sorry
    | _        => panic! s!"Head of list {sx} is {head} but should be op..?"
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
