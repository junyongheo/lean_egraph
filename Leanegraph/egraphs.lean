import Batteries.Data.UnionFind

/-
  Implementations of E-Node, E-Class, E-Graph and functions that operate on them
-/
variable {α : Type _} [DecidableEq α] [BEq α][Hashable α]

namespace EGraph

/-
  A Nat is used instead of Fin n for non-dependent typing reasons
-/
abbrev EClassId := Nat

structure ENode (α : Type _ ) where
  head : α
  args : List EClassId
deriving Hashable, DecidableEq, BEq, Repr

/-
  EClasses hold a list of equivalent nodes and a list of parents
  Performance is not an issue yet, lists instead of array for easier implementation
  TODO: switch to array (...eventually)
-/
structure EClass (α : Type _) where
  nodes : List (ENode α)
  parents : List (ENode α × EClassId)
deriving Repr

instance : Inhabited (EClass α) where
  default := {
    nodes := []
    parents := []
  }

/-
  Makes an instance of an EClass, either empty of from a Node

-/
def EClass.empty {α : Type _} : EClass α :=
  {
    nodes := []
    parents := []
  }

def EClass.fromNode {α : Type _} (en : ENode α) : EClass α:=
  {
    nodes := [en]
    parents := []
  }

def EClass.merge (ec₁ ec₂ : EClass α) : EClass α :=
  {
    -- TODO: think.. do we need to dedup here also?
    nodes   := ec₁.nodes ++ ec₂.nodes
    parents := ec₁.parents ++ ec₂.parents
  }

/-
  An e-graph is a tuple (U,M,H) of
    Union-find U - Equivalence relation over *e-class ids*
    E-class Map M - Map of *e-class ids to e-classes*
    Hashcons H - Map of *e-nodes to e-class ids*
-/
structure EGraph (α : Type _) [DecidableEq α][BEq α] [Hashable α] where
  uf    : Batteries.UnionFind
  ecmap : Std.HashMap EClassId (EClass α)
  hcons : Std.HashMap (ENode α) EClassId
  dirty : List EClassId
  -- For performance reasons, add a mapping of all terms by operator
  opmap : Std.HashMap α (List EClassId)


-- Is there a benefit to using the λ notation I wonder... readability? versatility?
def EGraph.size (eg : EGraph α) : Nat :=
  eg.uf.size

/-
  Constructor for an empty instance. Use the nil/empty constructors for each component.
  For the hashcons, empty is deprecated so emptyWithCapacity is used as per suggestion
-/
def EGraph.empty : EGraph α :=
  {
    uf    := Batteries.UnionFind.empty
    ecmap := Std.HashMap.emptyWithCapacity
    hcons := Std.HashMap.emptyWithCapacity
    dirty := []
    opmap := Std.HashMap.emptyWithCapacity
  }



/-
  State monad for e-graph
-/
abbrev EGraphM α [DecidableEq α] [BEq α] [Hashable α] := StateM (EGraph α)

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
def lookupCanonicalEClassId (id : EClassId) : EGraphM α <| EClassId := do
  let eg ← get
  let ⟨uf', res⟩ := eg.uf.find! id
  let _ ← set { eg with uf := uf' }
  return res





-- Do I really have to write -ize and not -ise
-- Realisation: no one will call this except me
-- I am freeeeee
def canonicalise (en : ENode α) : EGraphM α (ENode α) := do
  let newargs : List EClassId ← en.args.mapM lookupCanonicalEClassId
  return { en with args := newargs}

-- Do it anyway... :'(
abbrev canonicalize (en : ENode α) := canonicalise en

def findClass (en : ENode α) : EGraphM α (Option EClassId) := do
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
  For each argument, add the current node to their parents list
  None should not be reachable but for completion
  TODO: replace with .get! ?
-/
def updateParents (ecmap : Std.HashMap EClassId (EClass α)) (en : ENode α) (eid : EClassId) : Std.HashMap EClassId (EClass α) :=
  en.args.foldl (init := ecmap) (λ ecmap' argId =>
    match ecmap'.get? argId with
    | some cls =>
      let parent := (en, eid)
      let ec     := {cls with parents := parent :: cls.parents}
      ecmap'.insert argId ec
    | none     => ecmap'
  )

-- NOT TRUE: I don't think a monad is necessary here, we can just return a × with EGraph and ID
-- That is untrue!! Because of the previous wrappers I think we're stuck with a monad
-- Ask: is it normal to have so many do blocks because everything is monadic

/-
  Adds a node to the egraph
  If it exists, does nothing and returns ID
  If it doesn't, add it to the UF, E-Class Map, HCons
  Returns the new ID (which is the size of the E-Graph)
-/
def push (en : ENode α) : EGraphM α (EClassId) := do
  let en' ← canonicalise en
  let canonId ← findClass en'
  let eg ← get
  match canonId with
  | some ecId =>
    return ecId
  | none =>
    let curSize := eg.size
    let uf' := eg.uf.push

    let ecmap' := updateParents eg.ecmap en curSize

    let ecmap'' := ecmap'.insert curSize (EClass.fromNode en)
    let hcons' := eg.hcons.insert en curSize

    -- Operator Map
    -- TODO: Lean Docs say:
    -- The notation m[a]! is preferred over calling this function directly.
    -- over get!
    -- In any case, use getD to specify a default
    -- TODO: I think we can use getD to change some of the other code

    let curlist:= eg.opmap.getD en.head []
    let opmap' := eg.opmap.insert en.head (curSize :: curlist)
    set { eg with
            uf := uf',
            ecmap := ecmap'',
            hcons := hcons',
            opmap := opmap'
        }
    return curSize



-- I never use the return value here but hegg (haskell egg) returns eclassid, keep that for now
-- Similar question to the above, are we bound to a do-block because of the union-find here?
-- Do do-blocks make it harder to prove anything?
-- TODO: do i have to ensure the invariant holds before and after?
-- https://hackage-content.haskell.org/package/hegg-0.6.0.0/docs/src/Data.Equality.Graph.html#merge
-- TODO: i think we can extract a lot of these into smaller pure helper functions
-- the merge eclasses, hashcons
def union (id₁ id₂ : EClassId) : EGraphM α (EClassId) := do

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
    let (uf'', leaderClassId) := uf'.find! id₁'
    -- Update EClass, EClassMap and Hashcons with new UF canonies
    let fromId := if id₁' = leaderClassId then id₂' else id₁'

    -- merge std hashmap union
    let leaderClass := EClass.merge (eg.ecmap.get! leaderClassId) (eg.ecmap.get! fromId)

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

/-
  Helper for Rebuild
  Repairs one EClass
  Structure follows closely that in fig. 4 from egg paper
  TODO: I think the two loops can be merged..?
  Hegg does away with one loop completely
-/
def repair (id : EClassId) : EGraphM α (Unit) := do
  let eg ← get
  let eClass := eg.ecmap.get! id

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
    let _ ← union id₁ id₂

  -- Loop 2...
  let newParents ← eClass.parents.foldlM (init := Std.HashMap.emptyWithCapacity) (λ parents' (p : (ENode α × EClassId)) => do
    let canon ← canonicalise p.1
    let canonId ← lookupCanonicalEClassId p.2
    match parents'.get? p.1 with
    | some eid =>
      let _ ← union eid p.2
      return parents'
    | none    =>
      return parents'.insert canon canonId
  )
  let eg' ← get
  let _ ← set { eg' with ecmap := eg'.ecmap.insert id { eClass with parents := newParents.toList },  }
/-
-- Cannot update hcons so union in loop 2 will not be updated, better to keep track of collisions
def repair (id : EClassId) : EGraphM α (Unit) := do
  let eg ← get
  let eClass := eg.ecmap.get! id
  let hcList := eg.hcons.toList

  let updateHCList ← eClass.parents.foldlM (init := hcList) (λ hcList' (p: (ENode α × EClassId)) => do
    let canon ← canonicalise p.1
    let canonId ← lookupCanonicalEClassId p.2
    return hcList'.erase (p.1, p.2) |>.insert (canon, canonId)
  )

  let newParents ← eClass.parents.foldlM (init := updateHCList) (λ updateHCList' (p : ()))



  sorry
-/

/-
-- ISSUE: HashSet doesn't allow duplicates, therefore collisions == overwrite
-- the original egg paper doesn't specify the DS, but given that deduplication is in Loop 2
-- and not Loop 1, I assume that Loop 1 is one that allows duplicates. Solution, use list, then convert to HashSet later
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
  -- a bit inefficient and confusing to do list, better a map/set or something with better tracking. hashmap can be converted to list

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
  let _ ← set { eg' with ecmap := eg'.ecmap.insert id { eClass with parents := newParents.toList },  }
-/



/-
  I don't think this can be written with proof of termination so we will have to mark partial
  Rebuilds the egraph by iterating over the dirty list
  Recursively calls rebuild until everything is empty
-/
partial def rebuild : EGraphM α (Unit) := do
  let eg ← get
  let todo := eg.dirty
  if todo.isEmpty then return else

  let _ ← set { eg with dirty := [] }
  let repairList := (← todo.mapM lookupCanonicalEClassId).eraseDups

  for item in repairList do
    repair item

  -- rebuild


end EGraph
