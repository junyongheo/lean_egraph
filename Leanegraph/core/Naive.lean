import Batteries.Data.UnionFind


/-
  Implementations of E-Node, E-Class, E-Graph and functions that operate on them
-/
variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [BEq D] [Inhabited D]

namespace Naive

abbrev EClassId := Nat


structure ENode (α : Type _ ) where
  head : α
  args : List EClassId
deriving Hashable, DecidableEq, Repr

structure EClass (α : Type _) (D : Type _) where
  nodes : List (ENode α)
  parents : List (ENode α × EClassId)
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
  ecmap : List <| EClassId × (EClass α D)
  hcons : List <| ENode α × EClassId -- TODO: does this make it less readable?
  dirty : List <| EClassId × ENode α  -- hegg's version, keeps 2
  aldrt : List <| EClassId × ENode α
  opmap : List <| α × (List EClassId)


instance [Inhabited α] : Inhabited (ENode α) where
  default := {
    head := default
    args := []
  }

instance [Inhabited D] : Inhabited (EClass α D) where
  default := {
    nodes := []
    parents := []
    data := default
  }

class Analysis (α : Type _) (D : Type _)  [DecidableEq α][Hashable α] where
  make : (en : ENode α) → List D → D
  join : D → D → D
  modify : EGraph α D → EClassId → EGraph α D

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
    nodes := []
    parents := []
    data := default
  }

def EClass.fromNode {α : Type _} (en : ENode α) (data : D) : EClass α D :=
  {
    nodes := [en]
    parents := []
    data := data
  }


def EClass.merge (ec₁ ec₂ : EClass α D) (join : D → D → D) : EClass α D:=
  {
    nodes :=  ec₁.nodes.append ec₂.nodes |>.eraseDups
    parents := ec₁.parents ++ ec₂.parents
    data := join (ec₁.data) (ec₂.data)
  }


def updateEClassParents (en : ENode α) (eid : EClassId) (cur : EClassId × EClass α D) : EClassId × EClass α D :=
  (cur.1, ec) where
    parent := (en, eid)
    ec     := {cur.2 with parents := parent :: cur.2.parents}

def updateParents (ecmap : List <| EClassId × EClass α D) (en : ENode α) (eid : EClassId)
  : List <| EClassId × (EClass α D) :=
  ecmap.map
    (λ el@(id, _) =>
      if id ∈ en.args then
        updateEClassParents en eid el
      else
        el
    )

def EGraph.size (eg : EGraph α D) : Nat :=
  eg.uf.size

def EGraph.empty : EGraph α D:=
  {
    uf    := Batteries.UnionFind.empty
    ecmap := []
    hcons := []
    dirty := []
    aldrt := []
    opmap := []
  }

abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] := StateM (EGraph α D)

def lookupCanonicalEClassId (id : EClassId) : EGraphM α D <| EClassId := do
  let eg ← get
  let ⟨uf', res⟩ := eg.uf.find! id
  let _ ← set { eg with uf := uf' }
  return res

def canonicalise (en : ENode α) : EGraphM α D (ENode α) := do
  let newargs : List EClassId ← en.args.mapM lookupCanonicalEClassId
  return { en with args := newargs}

def findClass (en : ENode α) : EGraphM α D (Option EClassId) := do
  let en' ← canonicalise en
  let eg ← get
  match eg.hcons.lookup en' with
  | some eClassId =>
    return some eClassId
  | none =>
    return none

/-
  Adds a node to the egraph
  If it exists, does nothing and returns ID
  If it doesn't, add it to the UF, E-Class Map, HCons
  Returns the new ID (which is the size of the E-Graph)
-/
def push {D : Type _} [Inhabited (EClass α D)] [Inhabited D] (en : ENode α) (make : ENode α → List D → D): EGraphM α D (EClassId) := do
  let en' ← canonicalise en
  match ← findClass en' with
  | some ecId =>
    return ecId
  | none =>
    let eg ← get
    let curSize := eg.size
    let ecmap' := updateParents eg.ecmap en' curSize
    let childData := en'.args.map (λ id =>
      ((eg.ecmap.lookup id).getD EClass.empty).data
    )


    let ecmap'' := (curSize, (EClass.fromNode en' (make en' childData))) :: ecmap'
    let hcons' := eg.hcons.insert (en', curSize)

    let curList := (eg.opmap.lookup en'.head).getD []
    set { eg with
            uf := eg.uf.push,
            ecmap := ecmap'',
            hcons := hcons',
            opmap := (en'.head, curSize :: curList) :: eg.opmap
            dirty := (curSize, en') :: eg.dirty
            aldrt := (curSize, en') :: eg.aldrt
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
  -- In same class, nothing more to do
  if id₁' = id₂' then
    return id₁'
  -- In different class, we do work
  else
    -- moved this here for less operations?
    let eg ← get
    -- Update union find
    let uf' := eg.uf.union! id₁' id₂'
    let (uf''', leaderClassId) := uf'.find! id₁'
    -- more path compression........?
    let (uf'',  _) := uf'''.find! id₂'
    -- Update EClass, EClassMap and Hashcons with new UF canonies
    let fromId := if id₁' = leaderClassId then id₂' else id₁'
    -- merge std hashmap union
    -- also touch parents -- not in egg style deferred
    let lCls := (eg.ecmap.lookup leaderClassId).getD EClass.empty
    let sCls := (eg.ecmap.lookup fromId).getD EClass.empty
    let mergedClass := EClass.merge lCls sCls join

    let newEcmap := (leaderClassId, mergedClass) :: eg.ecmap.filter (λ (id, _) => id ≠ fromId && id ≠ leaderClassId)

    let newDirty := (sCls.parents.map Prod.swap) ++ eg.dirty

    let newData := join lCls.data sCls.data
    let nAnlDrt :=
      (if newData != sCls.data then (sCls.parents.map Prod.swap) else [])
      ++
      (if newData != lCls.data then (lCls.parents.map Prod.swap) else [])
      ++
      eg.aldrt

    let _ ← set {
                  eg with
                  uf := uf''
                  ecmap := newEcmap
                  dirty := newDirty
                  aldrt := nAnlDrt
                }
    return leaderClassId





def rebuildOpMap : EGraphM α D Unit := do
  let eg ← get

  let newOpMap := eg.ecmap.foldl (λ opmap (id, eclass) =>
    eclass.nodes.foldl (λ opmap node =>
      let cur := (opmap.lookup node.head).getD []
      (node.head, id :: cur) :: opmap.filter (λ a => a.1 ≠ node.head)
    ) opmap
  ) []

  set { eg with opmap := newOpMap}

/-
  for (id, eclass) in eg.ecmap do
    for node in eclass.nodes do
      let head := node.head
      let currentArr := newOpMap.getD head []
      newOpMap := newOpMap.insert head (currentArr.push id)
-/
  set { eg with opmap := newOpMap }



def repairHegg (id : EClassId) (en : ENode α) [Analysis α D] : EGraphM α D <| Unit := do
  let eg ← get
  match eg.hcons.lookup en with
  | none =>
    let _ ← set {eg with hcons := eg.hcons.insert (en, id)}
  | some existing =>
    let _ ← set {eg with hcons := eg.hcons.insert (en, id)}
    let _ ← union existing id (Analysis.join (α := α) (D := D))

def repairAnalysisHegg (id : EClassId) (en : ENode α) [Analysis α D] : EGraphM α D <| Unit := do
  let eg ← get
  match eg.ecmap.lookup id with
  | none => return ()
  | some cls =>
    let childData := en.args.map λ argId =>
      ((eg.ecmap.lookup argId).getD EClass.empty).data
    let newData := Analysis.join (α := α) (D:= D) cls.data (Analysis.make en childData)
    if newData != cls.data then
      let cls'     := {cls with data := newData}
      let newAldrt := cls.parents.map Prod.swap ++ eg.aldrt
      let eg'      := {eg with
                        ecmap := (id, cls') :: eg.ecmap.filter (λ ec => ec.1 != id)
                        aldrt := newAldrt
                      }
      let _ ← set (Analysis.modify eg' id)

-- def repairAnalysisHegg ()

partial def rebuildHegg [Analysis α D] : EGraphM α D <| Unit := do
  let eg ← get
  if eg.dirty.isEmpty && eg.aldrt.isEmpty then return()

  let emptyEgr := {eg with dirty := [], aldrt := []}
  let _ ← set emptyEgr

  let findEmpty := λ id => emptyEgr.uf.find! id |>.2



  let wl := eg.dirty.map (λ p =>
                (findEmpty p.1, {p.2 with args := p.2.args.map findEmpty})
              ) |>.eraseDups


  wl.forM (λ p => repairHegg p.1 p.2)

  let eg' ← get
  let findEmpty' := λ id => eg'.uf.find! id |>.2
  let naldrt := eg.aldrt.map (λ p : EClassId × ENode α =>
    (findEmpty' p.1, {p.2 with args := p.2.args.map findEmpty'})) |>.eraseDups

  naldrt.forM (λ p => repairAnalysisHegg p.1 p.2)

  rebuildHegg

/-
partial def rebuildHegg : EGraphM α D <| Unit := do
  let eg ← get
  if eg.dirty.isEmpty then return()

  let emptiedEgr := EGOps.emptyDirty eg
  let _ ← set emptiedEgr

  let wl := EGOps.dedupDirty <| EGOps.mapDirty
              (λ (id, node) =>
                (
                  EGOps.findEmpty emptiedEgr id,
                  EGOps.setArgs node (EGOps.mapArgs (EGOps.findEmpty emptiedEgr) (EGOps.getArgs node))
              ))
            (EGOps.getDirty eg)

  EGOps.forMDirty wl fun (id, node) => repairHegg id node

  rebuildHegg

-/
/-
  For Testing And Execution
  TODO: macros
-/

def pushRun [Analysis α D] (en : ENode α) : EGraphM α D EClassId := do
  let id ← push en Analysis.make
  rebuildHegg
  return id

def unionRun [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := do
  let id ← union id₁ id₂ (Analysis.join (α := α) (D := D))
  rebuildHegg
  return id

def rebuildRun [Analysis α D] : EGraphM α D (Unit) := do
  rebuildHegg

end Naive
