import Batteries.Data.UnionFind

/-
  Implementations of E-Node, E-Class, E-Graph and functions that operate on them
-/
variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [Inhabited D]

namespace EGraph

/-
  A Nat is used instead of Fin n for non-dependent typing reasons
-/
abbrev EClassId := Nat

structure ENode (α : Type _ ) where
  head : α
  args : Array EClassId
deriving Hashable, DecidableEq, Repr

/-
  EClasses hold a Array of equivalent nodes and a Array of parents
  Performance is not an issue yet, Arrays instead of array for easier implementation
  TODO: switch to array (...eventually)
-/
structure EClass (α : Type _) (D : Type _) where
  nodes : Array (ENode α)
  parents : Array (ENode α × EClassId)
  data : D
deriving Repr

/-
  An e-graph is a tuple (U,M,H) of
    Union-find U - Equivalence relation over *e-class ids*
    E-class Map M - Map of *e-class ids to e-classes*
    Hashcons H - Map of *e-nodes to e-class ids*
-/
structure EGraph (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] where
  uf    : Batteries.UnionFind
  ecmap : Std.HashMap EClassId (EClass α D)
  hcons : Std.HashMap (ENode α) EClassId
  dirty : Array EClassId
  -- For performance reasons, add a mapping of all terms by operator
  opmap : Std.HashMap α (Array EClassId)

instance [Inhabited α] : Inhabited (ENode α) where
  default := {
    head := default
    args := #[]
  }

instance [Inhabited D] : Inhabited (EClass α D) where
  default := {
    nodes := Array.empty
    parents := Array.empty
    data := default
  }

class Analysis (α : Type _) (D : Type _)  [DecidableEq α][Hashable α] where
  /- When a new e-node 𝑛 is added to 𝐺 into a new,
  singleton e-class 𝑐, construct a new value 𝑑𝑐 ∈ 𝐷
  to be associated with 𝑛’s new e-class,
  typically by accessing the associated data of 𝑛’s children. -/
  -- make(𝑛) → 𝑑𝑐
  make : (en : ENode α) → Array D → D




  -- join(𝑑𝑐1,𝑑𝑐2) →𝑑𝑐
  /-
    Whene-classes𝑐1,𝑐2 arebeingmergedinto𝑐,join𝑑𝑐1,𝑑𝑐2
    intoanew value 𝑑𝑐 to be associated with the new e-class 𝑐.
  -/
  join : D → D → D

  -- modify(𝑐) → 𝑐′
  /-
    Modify the *e-class* c based on dc.
    Should be idempotent (modify(modify(c))) = modify(c)
    TODO: another look at this...
    Option 1: Take E-Graph, lookup and modify E-Class, return E-Graph
    Option 2: Take E-Class, modify, return, then calling function sets
    -- Preferably Option 2?
    -- *Adds Nodes*, so is the single e-class enough? Perhaps not. Option 1 then.
  -/
  modify : EGraph α D → EClassId → EGraph α D

-- https://stackoverflow.com/questions/6071951/best-algorithm-for-delete-duplicates-in-array-of-strings
def dedupArray [BEq α] [Hashable α] (myArray : Array α) : Array α :=
  myArray.foldl (init := ((Std.HashSet.emptyWithCapacity, Array.empty) : (Std.HashSet α × Array α)))
  (λ (hashset, newarray) el =>
    if hashset.contains el then (hashset, newarray) else (hashset.insert el, newarray.push el)
  ) |>.2 -- return newarray

instance : Inhabited (Analysis α Unit) where
  default := {
    make    _  _ := (),
    join    _  _ := (),
    modify  eg _ := eg
  }

instance : Analysis α Unit where
  make _ _ := ()
  join _ _ := ()
  modify eg _ := eg


/-
  Makes an instance of an EClass, either empty of from a Node

-/
def EClass.empty [Inhabited D] {α : Type _} : EClass α D :=
  {
    nodes := Array.empty
    parents := Array.empty
    data := default
  }

def EClass.fromNode {α : Type _} (en : ENode α) (data : D) : EClass α D :=
  {
    nodes := Array.singleton en
    parents := Array.empty
    data := data
  }


def EClass.merge (ec₁ ec₂ : EClass α D) (join : D → D → D) : EClass α D:=
  {
    -- TODO: think.. do we need to dedup here also?
    -- Just do it
    -- nodes   := (ec₁.nodes ++ ec₂.nodes).eraseDups
    -- ok look this is kinda stupid
    nodes :=  ec₁.nodes.append ec₂.nodes
    parents := ec₁.parents ++ ec₂.parents

    -- Analysis?
    -- Without the α, lean complains
    -- But if I do α and d, it complains again
    -- Not sure why, TODO: make sure this is working as expected
    -- Since lean calls @Analysis
    data := join (ec₁.data) (ec₂.data)
  }




-- Is there a benefit to using the λ notation I wonder... readability? versatility?
def EGraph.size (eg : EGraph α D) : Nat :=
  eg.uf.size

/-
  Constructor for an empty instance. Use the nil/empty constructors for each component.
  For the hashcons, empty is deprecated so emptyWithCapacity is used as per suggestion
-/
def EGraph.empty : EGraph α D:=
  {
    uf    := Batteries.UnionFind.empty
    ecmap := Std.HashMap.emptyWithCapacity
    hcons := Std.HashMap.emptyWithCapacity
    dirty := Array.empty
    opmap := Std.HashMap.emptyWithCapacity
  }



/-
  State monad for e-graph
-/
abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] := StateM (EGraph α D)

/-
-- I think a runtime panic is better since we know something is wrong instead
-- unless introduce checks but that's not always possible
def lookupCanonicalEClassId' (id : EClassId) : EGraphM α <| EClassId := do
  let eg ← get
  if h : id < eg.uf.size then
    let ⟨uf', ⟨res,_⟩⟩ := eg.uf.find ⟨id,h⟩ -- the _ is a h but I just don't want to see the unused var warning
    let _ ← set { eg with uf := uf' }
    return res
  else
    return id

-- not used
def sameClass (eg: EGraph α) (ec1 : ENode α) (ec2 : ENode α) : EGraph α × Bool :=
  match (eg.hcons.get? ec1), (eg.hcons.get? ec2) with
  | some id1, some id2 =>
    if h : id1 < eg.size ∧ id2 < eg.size then
      let res := (eg.uf.checkEquiv ⟨id1, h.1⟩ ⟨id2, h.2⟩)
      ({ eg with uf := res.fst }, res.snd)
    else (eg, false)
  | _, _ => (eg, false)
-/

/-
  Lookup Canonical E-Class Id
  Uses find!
-/
def lookupCanonicalEClassId (id : EClassId) : EGraphM α D <| EClassId := do
  let eg ← get
  let ⟨uf', res⟩ := eg.uf.find! id
  let _ ← set { eg with uf := uf' }
  return res





-- Do I really have to write -ize and not -ise
-- Realisation: no one will call this except me
-- I am freeeeee
def canonicalise (en : ENode α) : EGraphM α D (ENode α) := do
  let newargs : Array EClassId ← en.args.mapM lookupCanonicalEClassId
  return { en with args := newargs}

-- Do it anyway... :'(
-- abbrev canonicalize (en : ENode α) := canonicalise en

def findClass (en : ENode α) : EGraphM α D (Option EClassId) := do
  let en' ← canonicalise en
  let eg ← get
  match eg.hcons.get? en' with
  | some eClassId =>
  /-
    -- TODO: I initially did this, but I don't understand why..?
    -- I guess because of a red squiggly line but TODO: think
    -- It doesn't break any tests so far
    let eClassId' ← lookupCanonicalEClassId eClassId eg
    return some eClassId'.fst
  -/
    let eClassId' ← lookupCanonicalEClassId eClassId
    return some eClassId'
  | none =>
    return none

/-
  Update Parents of an E-Class
  Run a fold over the arguments of the term (EClassId type)
  For each argument, add the current node to their parents Array
  None should not be reachable but for completion
  TODO: replace with .get! ?
-/
def updateParents (ecmap : Std.HashMap EClassId (EClass α D)) (en : ENode α) (eid : EClassId) : Std.HashMap EClassId (EClass α D) :=
  en.args.foldl (init := ecmap) (λ ecmap' argId =>
    match ecmap'.get? argId with
    | some cls =>
      let parent := (en, eid)
      let ec     := {cls with parents := cls.parents.push parent} -- is this faster? -- parent :: cls.parents}
      ecmap'.insert argId ec
    | none     => panic! "updateParents none should not be reachable"-- ecmap' -- if not reachable better warning i guess
  )

/-
  -- This is not used and doesn't type check anymore
  def canonicaliseParents (par: Array (ENode α × EClassId)) : EGraphM α D (Array (ENode α × EClassId)) := do
    let par' ← par.mapM (λ (en,id) => do
      let en' ← canonicalise en
      let id' ← lookupCanonicalEClassId id
      return (en', id')
    )
    return par'.eraseDups
-/
-- NOT TRUE: I don't think a monad is necessary here, we can just return a × with EGraph and ID
-- That is untrue!! Because of the previous wrappers I think we're stuck with a monad
-- Ask: is it normal to have so many do blocks because everything is monadic

/-
  Adds a node to the egraph
  If it exists, does nothing and returns ID
  If it doesn't, add it to the UF, E-Class Map, HCons
  Returns the new ID (which is the size of the E-Graph)
-/
def push {D : Type _} [Inhabited (EClass α D)] (en : ENode α) (make : ENode α → Array D → D): EGraphM α D (EClassId) := do
  let en' ← canonicalise en
  let canonId ← findClass en'
  match canonId with
  | some ecId =>
    return ecId
  | none =>
    let eg ← get
    let curSize := eg.size
    let uf' := eg.uf.push

    let ecmap' := updateParents eg.ecmap en' curSize

    let childData := en'.args.map (λ id =>
      (eg.ecmap.get! id).data
    )


    let ecmap'' := ecmap'.insert curSize (EClass.fromNode en' (make en' childData))
    let hcons' := eg.hcons.insert en' curSize

    -- Operator Map
    -- TODO: Lean Docs say:
    -- The notation m[a]! is preferred over calling this function directly.
    -- over get!
    -- In any case, use getD to specify a default
    -- TODO: I think we can use getD to change some of the other code

    let curArray:= eg.opmap.getD en'.head Array.empty
    let opmap' := eg.opmap.insert en'.head (curArray.push curSize)
    set { eg with
            uf := uf',
            ecmap := ecmap'',
            hcons := hcons',
            opmap := opmap'
            dirty := eg.dirty.push curSize
        }
    return curSize

-- I never use the return value here but hegg (haskell egg) returns eclassid, keep that for now
-- Similar question to the above, are we bound to a do-block because of the union-find here?
-- Do do-blocks make it harder to prove anything?
-- TODO: do i have to ensure the invariant holds before and after?
-- https://hackage-content.haskell.org/package/hegg-0.6.0.0/docs/src/Data.Equality.Graph.html#merge
-- TODO: i think we can extract a lot of these into smaller pure helper functions
-- the merge eclasses, hashcons
def union (id₁ id₂ : EClassId) (join : D → D → D) : EGraphM α D (EClassId) := do

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
    let (uf''', leaderClassId) := uf'.find! id₁'
    -- more path compression........?
    let (uf'',  _) := uf'''.find! id₂'
    -- Update EClass, EClassMap and Hashcons with new UF canonies
    let fromId := if id₁' = leaderClassId then id₂' else id₁'


    -- merge std hashmap union
    -- also touch parents -- not in egg style deferred
    let leaderClass := EClass.merge (eg.ecmap.get! leaderClassId) (eg.ecmap.get! fromId) join
    let _ ← set {
                  eg with
                  uf := uf''
                  ecmap := (Std.HashMap.insert (Std.HashMap.erase eg.ecmap fromId) leaderClassId leaderClass)
                  dirty :=  eg.dirty.push leaderClassId
                }
    return leaderClassId



def rebuildOpMap : EGraphM α D Unit := do
  let eg ← get
  let mut newOpMap : Std.HashMap α (Array EClassId) := Std.HashMap.emptyWithCapacity

  for (id, eclass) in eg.ecmap.toList do
    for node in eclass.nodes do
      let head := node.head
      let currentArr := newOpMap.getD head #[]
      newOpMap := newOpMap.insert head (currentArr.push id)

  set { eg with opmap := newOpMap }


/-
  Helper for Rebuild
  Repairs one EClass
  Structure follows closely that in fig. 4 from egg paper
  TODO: I think the two loops can be merged..?
  Hegg does away with one loop completely
-/
def repair (id : EClassId) (join : D → D → D) : EGraphM α D (Unit) := do

  let canonId ← lookupCanonicalEClassId id
  let eg ← get
  match eg.ecmap.get? canonId with
  | some _ => pure () -- no op it exists go on
  | none   => return () -- don't panic all is well


  let eClass := eg.ecmap.get! canonId

  -- Loop 1...
  let (updateHCons, collisions) ← eClass.parents.foldlM (init := (eg.hcons, [])) (λ (hcons', collisions') (p : (ENode α × EClassId)) => do
      let canon ← canonicalise p.1
      let canonId ← lookupCanonicalEClassId p.2
      let det := hcons'.erase p.1
      match det.get? canon with
      | some key => return (det, (canonId, key) :: collisions') -- keeps track of things to merge without collisions
      | none     => return (det.insert canon canonId, collisions')
  )

  let eg ← get
  let _ ← set { eg with hcons := updateHCons }

  for (id₁, id₂) in collisions do
    let _ ← union id₁ id₂ join

  let curNodes ← eClass.nodes.mapM canonicalise
  let newNodes := dedupArray curNodes

  -- Loop 2...
  let newParents ← eClass.parents.foldlM (init := Std.HashMap.emptyWithCapacity) (λ parents' (p : (ENode α × EClassId)) => do
    let canon ← canonicalise p.1
    let canonId ← lookupCanonicalEClassId p.2
    match parents'.get? canon with
    | some eid =>
      let _ ← union eid canonId join
      return parents'
    | none    =>
      return parents'.insert canon canonId
  )
  let eg' ← get
  let canonId' ←  (lookupCanonicalEClassId canonId)
  let eClassFinal := eg'.ecmap.get! canonId' -- needs to be canonicalised again

  let eClassFinal' := { eClassFinal with nodes := (← eClassFinal.nodes.mapM canonicalise), }
  let _ ← set { eg' with ecmap := eg'.ecmap.insert canonId' { eClassFinal' with parents := dedupArray newParents.toArray },}


/-
  I don't think this can be written with proof of termination so we will have to mark partial
  Rebuilds the egraph by iterating over the dirty Array
  Recursively calls rebuild until everything is empty
-/

partial def rebuild (join : D → D → D) (modify : EGraph α D → EClassId → EGraph α D) : EGraphM α D (Unit) := do
  let eg ← get
  let todo := eg.dirty
  if todo.isEmpty then return else

  let _ ← set { eg with dirty := Array.empty }
  let repairArray := (← todo.mapM lookupCanonicalEClassId)

  for item in (dedupArray repairArray) do
    repair item join

    let eg' ← get
    let eg'' := modify eg' (← lookupCanonicalEClassId item) -- canonicalise after repair!!!
    let _ ← set eg''

  rebuild join modify

/-
  For Testing And Execution
  TODO: macros
-/

def pushRun [Analysis α D] (en : ENode α) : EGraphM α D EClassId := do
  let id ← push en Analysis.make
  return id

def unionRun [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := do
  let id ← union id₁ id₂ (Analysis.join (α := α) (D := D))
  return id

def rebuildRun [Analysis α D] : EGraphM α D (Unit) := do
  rebuild (Analysis.join (α := α)) Analysis.modify

/-
-- Cannot update hcons so union in loop 2 will not be updated, better to keep track of collisions
def repair (id : EClassId) : EGraphM α (Unit) := do
  let eg ← get
  let eClass := eg.ecmap.get! id
  let hcArray := eg.hcons.toArray

  let updateHCArray ← eClass.parents.foldlM (init := hcArray) (λ hcArray' (p: (ENode α × EClassId)) => do
    let canon ← canonicalise p.1
    let canonId ← lookupCanonicalEClassId p.2
    return hcArray'.erase (p.1, p.2) |>.insert (canon, canonId)
  )

  let newParents ← eClass.parents.foldlM (init := updateHCArray) (λ updateHCArray' (p : ()))



  sorry
-/

/-
-- ISSUE: HashSet doesn't allow duplicates, therefore collisions == overwrite
-- the original egg paper doesn't specify the DS, but given that deduplication is in Loop 2
-- and not Loop 1, I assume that Loop 1 is one that allows duplicates. Solution, use Array, then convert to HashSet later
def repair (id : EClassId) : EGraphM α (Unit) := do
  -- oh no my functions require MORE MONADS
  let eg ← get
  let eClass := eg.ecmap.get! id



  -- Loop 1...
  let updateHCons ← eClass.parents.foldlM (init := eg.hcons) (λ hcons' (p : (ENode α × EClassId)) => do
      /-
      let canon ← canonicalise p.1
      let canonId ← lookupCanonicalEClassId p.2
      return hcons'.erase p.1 |>.insert (canon) canonId
      -/
      return hcons'.erase p.1 |>.insert (← canonicalise p.1) (← lookupCanonicalEClassId p.2)
  )
  let eg ← get
  let _ ← set { eg with hcons := updateHCons }
  -- a bit inefficient and confusing to do Array, better a map/set or something with better tracking. hashmap can be converted to Array

  -- Loop 2...
  -- can these two loops be merged?
  let newParents ← eClass.parents.foldlM (init := Std.HashMap.emptyWithCapacity) (λ parents' (p : (ENode α × EClassId)) => do
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
  let _ ← set { eg' with ecmap := eg'.ecmap.insert id { eClass with parents := newParents.toArray },  }
-/
