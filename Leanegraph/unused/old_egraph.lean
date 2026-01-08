import Batteries.Data.UnionFind
import Lean.Data.AssocList

/-
  Implementations of E-Node, E-Class, E-Graph and functions that operate on them
-/

/-
  Seems like Fin n is more common option
  Fin n is a set(?)/type that holds all n strictly smaller than n
  Unless Fin n is strictly required by UF, we try with Nat first
-/

abbrev EClassId := Nat

/-
  Similar to term, but with EClassIds instead
  EClassIds and not term because we want to represent operations between a group of equivalent expressions
-/
inductive ENode where
| var : String → ENode
| nat : Nat → ENode
| add : EClassId → EClassId → ENode
| mul : EClassId → EClassId → ENode
deriving BEq, Hashable, Repr

#eval ENode.var "x"
#eval ENode.nat 3
#eval ENode.add 3 5

inductive ENode' where
| head : String → ENode'
| args : String → List ENode' → ENode'



/-
  Performance is not an issue yet, lists instead of array for easier implementation
-/
structure EClass where
  nodes : List ENode
  parents : List (ENode × EClassId)
  -- do we need this if following egg?
  -- we do i misunderstood
deriving Repr

/-
  Do I really need 3 constructors? Probably not
  Eh maybe... idk think about it
  TODO: Cleanup (think about)
  Makes an instance of an EClass
-/
def EClass.empty : EClass :=
  {
    nodes := []
    parents := []
  }

def EClass.fromNode (en : ENode) : EClass :=
  {
    nodes := [en]
    parents := []
  }

def EClass.fromList (listnode : List ENode) : EClass :=
  {
    nodes := listnode
    parents := []
  }

/-
  Adds an E-Node to an existing instance of an E-Class
-/

def EClass.addNode (curClass : EClass) (ec : ENode) : EClass :=
  fromList (curClass.nodes.cons ec)


instance : Inhabited EClass where
  default := {
    nodes := []
    parents := []
  }

/-
def EClass.merge (ec₁ ec₂ : EClass) : EClass × EClass :=
  (EClass.fromList (ec₁.nodes ++ ec₂.nodes), EClass.empty)
-/

def EClass.merge (ec₁ ec₂ : EClass) : EClass :=
  {
    -- this will NOT remove duplicates
    -- so we will have LOTS OF DUPLICATES
    -- which will give us S L O W D O W N S
    nodes   := ec₁.nodes ++ ec₂.nodes
    parents := ec₁.parents ++ ec₂.parents
  }

-- #eval (EClass.constWithList [ENode.var "x", ENode.nat 3]).addNode (ENode.nat 5)
-- Can add using accessor notation or with standard notation

/-
  An e-graph is a tuple (U,M,H) of
    Union-find U - Equivalence relation over *e-class ids*
    E-class Map M - Map of *e-class ids to e-classes*
    Hashcons H - Map of *e-nodes to e-class ids*
-/
structure EGraph where
  uf    : Batteries.UnionFind
  ecmap : Std.HashMap EClassId EClass -- EClassId → EClass
  --ecmap : Lean.AssocList EClassId EClass
  hcons : Std.HashMap ENode EClassId -- ENode → EClassId
  --ufSize : n = uf.size -- try without this
  dirty : List EClassId

-- Is there a benefit to using the λ notation I wonder... readability? 범용성ability?
def EGraph.size (eg : EGraph) : Nat :=
  eg.uf.size

/-
  Constructor for an empty instance. Use the nil/empty constructors for each component.
  For the hashcons, empty is deprecated so emptyWithCapacity is used as per suggestion
-/
def EGraph.empty : EGraph :=
  {
    uf    := Batteries.UnionFind.empty,
    ecmap := Std.HashMap.emptyWithCapacity,
    -- ecmap := Lean.AssocList.nil
    hcons := Std.HashMap.emptyWithCapacity
    dirty := []
  }

def EGraph.construct : EGraph :=
  EGraph.empty


abbrev EGraphM := StateM (EGraph)

-- I'm not sure about this one
def lookupEClass (id : EClassId) : EGraphM <| EClass := do
  -- TODO: i could use find! here to panic
  -- TODO2: i could use an option to return, but i guess a new eclass might be needed THINK
  let eg ← get
  if h : id < eg.uf.size then
    let ⟨uf', ⟨res,_⟩⟩ := eg.uf.find ⟨id, h⟩ -- ⟨id, h⟩ makes a fin -- the _ is a h but I just don't want to see the unused var warning
    let _ ← set { eg with uf := uf' }
    match eg.ecmap.get? res with
    | some eclass => pure eclass
    | none        => pure EClass.empty
  else
    pure EClass.empty

def lookupEClassPanic (id : EClassId) : EGraphM <| EClass := do
  let eg ← get
  let ⟨uf', res⟩ := eg.uf.find! id
  let _ ← set { eg with uf := uf' }
  match eg.ecmap.get? res with
  | some eclass => pure eclass
  | none        => pure EClass.empty

def lookupCanonicalEClassId (id : EClassId) : EGraphM <| EClassId := do
  let eg ← get
  if h : id < eg.uf.size then
    let ⟨uf', ⟨res,_⟩⟩ := eg.uf.find ⟨id,h⟩ -- the _ is a h but I just don't want to see the unused var warning
    let _ ← set { eg with uf := uf' }
    return res
  else
    return id

#check (EGraph.empty).hcons.get (ENode.var "x")
/-
-- Takes two ENodes, checks equivalence in graph then returns bool
-- Not sure if this should return EGraph × Bool or just Bool, ask -- I assume path compresion as usual, just do it
def sameClass (eg: EGraph) (ec1 : ENode) (ec2 : ENode) : Bool :=
  match (eg.hcons.get? ec1), (eg.hcons.get? ec2) with
  -- for some reason .get? works well with the option id but .get return id ∈ EClass → EClassId type so there's more work needed
  | some id1, some id2 =>
    if h1 : id1 < eg.size then
      if h2 : id2 < eg.size then
        (eg.uf.checkEquiv ⟨id1, h1⟩ ⟨id2, h2⟩).snd
      else false
    else false
  | _, _ => false
-/

-- The one above but has a × type instead of just bool
-- Preserves path compression works

def sameClass (eg: EGraph) (ec1 : ENode) (ec2 : ENode) : EGraph × Bool :=
  match (eg.hcons.get? ec1), (eg.hcons.get? ec2) with
  -- for some reason .get? works well with the option id but .get return id ∈ EClass → EClassId type so there's more work needed
  | some id1, some id2 =>
    if h : id1 < eg.size ∧ id2 < eg.size then
    --if h1 : id1 < eg.size then
    --  if h2 : id2 < eg.size then
      let res := (eg.uf.checkEquiv ⟨id1, h.1⟩ ⟨id2, h.2⟩)
      ({ eg with uf := res.fst }, res.snd)
    -- else panicWith (eg, false)
    else (eg, false)
  | _, _ => (eg, false)

-- Do I really have to write -ize and not -ise
-- Does Lean support aliasing
def canonicalise : ENode → EGraphM ENode
  -- I think we can just use a map function to apply find root to node in list node
  -- However in my basic language we don't have one pattern (head + args)
  -- use monad map in final implementation. Here, we do it for each individual
| ENode.var var =>
  pure (ENode.var var)
| ENode.nat nat =>
  pure (ENode.nat nat)
| ENode.add eid₁ eid₂ =>
  do
    let eid₁' ← lookupCanonicalEClassId eid₁
    let eid₂' ← lookupCanonicalEClassId eid₂
    return ENode.add eid₁' eid₂'
| ENode.mul eid₁ eid₂ =>
  do
    let eid₁' ← lookupCanonicalEClassId eid₁
    let eid₂' ← lookupCanonicalEClassId eid₂
    return ENode.mul eid₁' eid₂'


def findClass (en : ENode) : EGraphM (Option EClassId) := do
  let en' ← canonicalise en
  let eg ← get
  match eg.hcons.get? en' with
  | some eClassId =>
    -- HCons operation so I don't believe a set is needed
    -- Why is a get needed then hm.... TODO: re-think that
    let eClassId' ← lookupCanonicalEClassId eClassId eg
    -- let eClassId' ← lookupCanonicalEClassId eClassId -- do we need the eg or not? TODO: some testing later
    return some eClassId'.fst
  | none =>
    return none

def updateParents (ecmap : Std.HashMap EClassId EClass) (en : ENode) (eid : EClassId) : Std.HashMap EClassId EClass :=
  match en with
  | ENode.add a b
  | ENode.mul a b =>
    let parent := (en, eid)
    let ec₁ := ecmap.get! a
    let ecmap' := ecmap.insert a ({ ec₁ with parents := parent :: ec₁.parents })

    let ec₂ := ecmap'.get! b
    ecmap'.insert b ({ ec₂ with parents := parent :: ec₂.parents})

  | _ =>
    ecmap

-- ~~I don't think a monad is necessary here, we can just return a × with EGraph and ID~~
-- That is untrue!! Because of the previous wrappers I think we're stuck with a monad
-- I guess ask
def push (en : ENode) : EGraphM (EClassId) := do
  let en' ← canonicalise en
  let canonId ← findClass en'
  let eg ← get
  match canonId with
  | some ecId =>
    return ecId
  | none =>
    let curSize := eg.size
    let uf' := eg.uf.push
    /-
    -- maybe try with a helper function
    -- im starting to think working with a full langauge would be cleaner
    match en with
    | ENode.add arg₁ arg₂
    | ENode.mul arg₁ arg₂ =>
      let parentVal := (en, curSize)
      let arg₁' := eg.ecmap.get! arg₁
      let arg₁' := { arg₁' with parents := parentVal :: arg₁'.parents }
      let arg₂' := eg.ecmap.get! arg₂
      let arg₂' := { arg₂' with parents := parentVal :: arg₂'.parents }
      -- ok this makes naming not the best
      let mutecmap' := (eg.ecmap.insert arg₁ arg₁').insert arg₂ arg₂'
    | _ =>
      ()
    -/
    let ecmap' := updateParents eg.ecmap en curSize

    let ecmap'' := ecmap'.insert curSize (EClass.fromNode en)
    let hcons' := eg.hcons.insert en curSize
    set { eg with
            uf := uf',
            ecmap := ecmap'',
            hcons := hcons'
        }
    return curSize




-- I believe Unit is like void, and since we only need to keep track of a modified egraph state
-- and not return any value, we can pass unit here
-- or would it be beneficial to return a boolean or so to indicate something?
-- TODO: look back at this later - hegg (haskell) returns eclassid, sounds good
-- Similar question to the above, are we bound to a do-block because of the union-find here?
-- Do do-blocks make it harder to prove anything?
-- TODO: do i have to ensure the invariant holds before and after?
-- https://hackage-content.haskell.org/package/hegg-0.6.0.0/docs/src/Data.Equality.Graph.html#merge
-- Hegg impl above
-- TODO: i think we can extract a lot of these into smaller pure helper functions
-- the merge eclasses, hashcons
def union (id₁ id₂ : EClassId) : EGraphM (EClassId) := do
  -- Get canonical classes for the inputs
  let id₁' ← lookupCanonicalEClassId id₁
  let id₂' ← lookupCanonicalEClassId id₂
  let eg   ← get
  -- In same class, nothing more to do
  if id₁' = id₂' then
    return id₁'
  -- In different class, we do work
  else
    -- Update union find
    let uf' := eg.uf.union! id₁' id₂'



    -- let _ ← set { eg with uf := uf' }
    -- let leaderClassId ← lookupCanonicalEClassId id₁' -- TODO: can i do this without the set previous
    -- let (uf', leaderClassId) := (eg.uf.union! id₁' id₂').find! id₁'
    let (uf'', leaderClassId) := uf'.find! id₁'
    -- Update EClass, EClassMap and Hashcons with new UF canonies
    /-
    match mergedId with
    | id₁' => sorry
    | id₂' => sorry
    -/
    /-
    if id₁' = leaderClassId then
      let fromId := id₂'
    else
      let fromId := id₁'
    -/
    let fromId := if id₁' = leaderClassId then id₂' else id₁'
    -- merge std hashmap union
    let leaderClass := EClass.merge (eg.ecmap.get! leaderClassId)  (eg.ecmap.get! fromId)

     -- Re-canonicalise my nodes
    let newHcons := eg.hcons.fold (init := eg.hcons) (λ hcons' en id =>
                      if id = fromId then hcons'.insert en leaderClassId else hcons')

    let _ ← set {
                  eg with
                  uf := uf''
                  ecmap := (Std.HashMap.insert (Std.HashMap.erase eg.ecmap fromId) leaderClassId leaderClass)
                  hcons := newHcons
                  dirty := leaderClassId :: eg.dirty
                }
    return leaderClassId

def repair (id : EClassId) : EGraphM (Unit) := do
  -- oh no my functions require MORE MONADS
  let eg ← get
  let eClass := eg.ecmap.get! id

  -- Loop 1...
  let updateHCons ← eClass.parents.foldlM (init := eg.hcons) (λ hcons' (p : (ENode × EClassId)) => do
      /-
      let canon ← canonicalise p.1
      let canonId ← lookupCanonicalEClassId p.2
      return hcons'.erase p.1 |>.insert (canon) canonId
      -/
      return hcons'.erase p.1 |>.insert (← canonicalise p.1) (← lookupCanonicalEClassId p.2)
  )
  let eg ← get
  let _ ← set { eg with hcons := updateHCons }
  -- a bit inefficient and confusing to do list, better a map/set or something with better tracking. hashmap can be converted to list
  /-
  let newParents ← eClass.parents.foldlM (init := ([] : List (ENode × EClassId)) (λ parents' (p : (ENode × EClassId)) => do
    let canon ← canonicalise p.1
    match parents'.get? p.1 with
    | some enode => sorry
    | none => return
  -/


  -- Loop 2...
  -- can these two loops be merged?
  let newParents ← eClass.parents.foldlM (init := Std.HashMap.emptyWithCapacity) (λ parents' (p : (ENode × EClassId)) => do
    let canon ← canonicalise p.1
    let canonId ← lookupCanonicalEClassId p.2
    match parents'.get? p.1 with
    | some en =>
      let _ ← union en p.2 -- i guess this is automatically updated
      return parents'
    | none    =>
      return parents'.insert canon canonId
  )
  let eg' ← get
  let _ ← set { eg' with ecmap := eg'.ecmap.insert id { eClass with parents := newParents.toList },  }

-- I don't think this can be written with proof of termination so we will have to mark partial
partial def rebuild : EGraphM (Unit) := do
  let eg ← get
  let todo := eg.dirty
  if todo.isEmpty then return else

  let _ ← set { eg with dirty := [] }
  let repairList := (← todo.mapM lookupCanonicalEClassId).eraseDups

  for item in repairList do
    repair item

  rebuild

  /-
  let nextIter ← eg.dirty.foldlM (init := ([] : List EClassId) (λ nextDirty id => do
    let eg' ← get
    let canonId ← lookupCanonicalEClassId id

  )
  -/








/-
def pureCanonicalise (uf : Batteries.UnionFind) : ENode → ENode
| ENode.var x => ENode.var x
| ENode.nat n => ENode.nat n
| ENode.add a b => ENode.add (uf.find! a).2 (uf.find! b).2
| ENode.mul a b => ENode.mul (uf.find! a).2 (uf.find! b).2

def updateHCons (eg : EGraph) (id : EClassId) : EGraphM (Std.HashMap ENode EClassId) := do
  let pList := (eg.ecmap.get! id).parents
  pList.foldlM (init := eg.hcons) (λ hcons' (p : (ENode × EClassId)) =>
                (hcons'.erase p.1).insert p.1 (lookupCanonicalEClassId )

                )


  sorry




#eval   List.map (λ /-(a : ENode × EClassId)-/ a => (a.fst, a.snd + 1)) [(ENode.nat 1, 2), (ENode.nat 1, 3), (ENode.nat 1, 4)]


def myHM : Std.HashMap String Nat :=
  Std.HashMap.emptyWithCapacity

def hashmapOne : Std.HashMap String Nat :=
  -- let h1 := myHM
  -- let h2 := myHM
  (myHM.insert "a" 1).insert "aa" 2

def hashmapTwo : Std.HashMap String Nat :=
  (myHM.insert "b" 1).insert "bb" 2

#check Std.HashMap.union hashmapOne hashmapTwo
-/
