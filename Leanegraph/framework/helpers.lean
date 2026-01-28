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

def checkDiffClass (id1 id2 : EClassId) (test : String := "") : EGraphM α D <| EClassId := do
  let c1 ← lookupCanonicalEClassId id1
  let c2 ← lookupCanonicalEClassId id2
  if c1 = c2 then
    panic! s!"Test Failed: {test} | Expected {c1} ≠ {c2}"
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

def getMatches

  {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
  {D : Type _}
  [Analysis α D]
  [Inhabited D]
  [Inhabited (Pattern α)]

  (rules : Array (Rule α D))
  : EGraphM α D <| Array (Rule α D × EClassId × Dict α) := do


  -- let eg ← get
  -- let mut allMatches : Array (EClassId × Dict α) := #[]
  /-
  for r in rules do
    let myMatches ← rewrite_search (α := α) (D := D) (r := r)
  -/

  return ← rules.flatMapM (λ r => do
     rewrite_search (α := α) (D := D) (r := r)
  )

def writeMatches

    {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
    {D : Type _}
    [Analysis α D]
    [Inhabited D]
    [Inhabited (Pattern α)]

    (ruleMatches : Array (Rule α D × EClassId × Dict α))
    : EGraphM α D <| Unit := do

  let joinFn := Analysis.join (α := α) (D := D)
  for (curRule, curECID, curSub) in ruleMatches do
      let rhsId ← instantiate curRule.rhs curSub
      let _     ← union curECID rhsId joinFn



def eqSat
      {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
      {D : Type _}
      [Analysis α D]
      [Inhabited D]
      [Inhabited (Pattern α)]
      (rules : List (Rule α D))
      (limit : Nat := 10)
      -- (nodeLimit : Option Nat := none)
      (nodeLimit : Nat := 0)
    : EGraphGenericIO α (D := D) Unit := do
  let mut i := 0
  let arrules := rules.toArray
  let _ ← runLineUnit <| rebuild (Analysis.join (α := α) (D := D)) Analysis.modify
  while i < limit do

    let _ ← runLineUnit <| rebuildOpMap

    let egStart ← get

    let numClassesStart := egStart.uf.size
    let numNodesStart   := egStart.size

    -- search phase
    let (ruleMatches, egSearch) := (getMatches arrules).run egStart

    -- write phase
    let (_, egWrite) := (writeMatches ruleMatches).run egSearch



    let (_, egEnd) := (rebuild (Analysis.join (α := α)) (Analysis.modify)).run egWrite

    -- printEGraph

    set egEnd

    let numClassesEnd := egEnd.uf.size
    let numNodesEnd   := egEnd.size
    if numClassesStart == numClassesEnd && numNodesStart == numNodesEnd then
      return ()
    if (nodeLimit > 0 ∧ egEnd.size > nodeLimit) then return ()

    -- IO.println s!"Jebal jom {i}"
    i := i + 1



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



/-

-/
open ExprParser

/-
  Idea: Since SExpr is structured as a list holding lists or atoms
  If encounter atom: push the appropriate term onto the graph
  If encounter list: get the op and the args, and recurse on the args

  Since we recurse on the args with the function, and the atoms return with a push,
  we should be returning EClassId (what push returns)

  Using an EGraphM, we pass the state along the recursions. Make sure to call ← get.
  CANCELLED:
    extensive generic interface
  NEW:
    Just make the user define it, it's their problem.
-/


class ParseExpr (α : Type _) where
  parse : SExpr → Option (α × List SExpr)

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α] [ParseExpr α]

partial def buildEGFromSExprGeneric [Analysis α D] (sx : SExpr) : EGraphM α D EClassId := do
  match ParseExpr.parse (α := α) sx with
  | some (op, args) =>
    let argIds ← args.mapM buildEGFromSExprGeneric
    pushRun {head := op, args := Array.mk argIds}
  | none =>
    panic! s!"Failed to parse argument"


-- I'm running out of proper names
-- or proper formatting
def test_fn
    [Analysis α D]
    [Inhabited (Pattern α)]
    -- (testName: String := "")
    (lhs : String)
    (rhs : List String)
    (rules : List <| Rule α D)
    (iterLimit : Nat := 10)
    (printLeft : Bool := false)
    (printRight : Bool := false)
  : EGraphGenericIO α D Unit := do




  let st ← (
    match (ExprParser.SExprParser.run lhs) with
    | .ok expr => runLine <| buildEGFromSExprGeneric expr
    | .error e => panic! s!"Error with {e}"
  )

  if printLeft then printEGraph
  eqSat rules iterLimit
  if printRight then printEGraph

  for rh in rhs do
  -- build the rhs, cant use the predefined macros in macros.lean
    let t1 ← ( match (ExprParser.SExprParser.run rh) with
                          | .ok expr => runLine <| buildEGFromSExprGeneric expr
                          | .error e => panic! s!"Error with {e}")
    let _ ← runLine <| checkSameClass st t1
    IO.println s!"{lhs} and {rh} are same class"


def test_fn_self
    [Analysis α D]
    [Inhabited (Pattern α)]
    (testName: String := "")
    (lhs : String)
    (rhs : List String)
    (rules : List <| Rule α D)
    (iterLimit : Nat := 10)
    (printLeft : Bool := false)
    (printRight : Bool := false)
  -- : EGraphGenericIO α D Unit := do
  : IO Unit := do

  let emptyGraph : EGraph α D := EGraph.empty

  IO.println s!"Starting Test {testName}"

  let _ ← (do
    let st ← (
      match (ExprParser.SExprParser.run lhs) with
      | .ok expr => runLine <| buildEGFromSExprGeneric expr
      | .error e => panic! s!"Error with {e}"
    )

    if printLeft then printEGraph
    eqSat rules iterLimit
    if printRight then printEGraph

    for rh in rhs do
    -- build the rhs, cant use the predefined macros in macros.lean
      let t1 ← ( match (ExprParser.SExprParser.run rh) with
                            | .ok expr => runLine <| buildEGFromSExprGeneric expr
                            | .error e => panic! s!"Error with {e}")
      let _ ← runLine <| checkSameClass st t1
      IO.println s!"{lhs} and {rh} are same class"
  ).run emptyGraph

  IO.println s!"Test {testName} Completed"


/-
  Non-Option Case
  TODO: Think which one better?

partial def buildEGFromSExprGeneric [Analysis α D] (sx : SExpr) : EGraphM α D EClassId := do
  let (op, args) := (ParseExpr.parse (α := α) sx)
  let argIds ← args.mapM buildEGFromSExprGeneric
  pushRun {head := op, args := argIds}
-/
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
