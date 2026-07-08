import Leanegraph.core.SharedDefs
import Leanegraph.core.ListAsMaps
import Leanegraph.core.UnionFind
import Leanegraph.core.NaiveDefs

/-
  Naive.lean consists of most of the EGraph operations used in the
-/
variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

/-
  Define Helper Functions
-/
-- def ecmapLookup (eg : EGraph α D) : EClassId → Option (EClass α D) :=
--  λ id => eg.ecmap.lookup id
  -- eg.ecmap.lookup -- why doesn't this work? by some greek-letter-reduction
  -- is it not the same thing?

def ecmapLookup (eg : EGraph α D) :=
  eg.ecmap.lookup -- now it does with the new defs

def hcLookup (eg : EGraph α D) : ENode α → Option EClassId :=
  λ en => eg.hcons.lookup en

-- def insertHCons (hc : List <| ENode α × EClassId) (k : ENode α) (v : EClassId) : List <| ENode α × EClassId :=
--  uniqueInsert hc k v

def insertHCons (hc : ListMap (ENode α) EClassId): ENode α → EClassId → ListMap (ENode α) (EClassId) :=
  λ k v => hc.insert k v

def insertECMap (ec : ListMap EClassId (EClass α D)) (k : EClassId) (v : EClass α D) : ListMap EClassId (EClass α D) :=
  ec.insert k v

-- def insertECMap (ec : List <| EClassId × EClass α D) (k : EClassId) (v : EClass α D) : List <| EClassId × EClass α D :=
--  uniqueInsert ec k v




def EGraph.size (eg : EGraph α D) : Nat :=
  List.length eg.uf

def numCanonClasses (eg : EGraph α D) : Nat :=
  eg.uf.filter (λ (id, cid) => id == cid) |>.length

def numClasses (eg : EGraph α D) : Nat :=
  eg.uf.map Prod.snd |>.eraseDups |>.length

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


def EClass.merge [Analysis α D] (ec₁ ec₂ : EClass α D) : EClass α D:=
  {
    nodes :=  ec₁.nodes.append ec₂.nodes-- |>.eraseDups
    parents := ec₁.parents ++ ec₂.parents-- |>.eraseDups
    data := Analysis.join (α := α) (D := D) (ec₁.data) (ec₂.data)
  }

def EGraph.empty : EGraph α D:=
  {
    uf    := []
    ecmap := ⟨[], by simp[KeysUnique]⟩
    hcons := ⟨[], by simp[KeysUnique]⟩ -- ListMap.empty
    dirty := []
    aldrt := []
  }




/-
  Update Parents in an E-Class. Two versions available, a fold and a map.
  Maps seem to be easier to reason about, so use the map and do a performance check
  to figure out which one to use for the optimised version
  or think about the best way to do it
  Calls:
    - N/A
  Called By:
    - Push (en is canonicalised already, no need to canonicalise again)
  Invariants:
    - ?
  Also it doesn't touch the Prod.fst which we have a lemma for (or can adapt)
-/
/-
def updateEClassParents (en : ENode α) (eid : EClassId) (cur : EClassId × EClass α D) : EClassId × EClass α D :=
  (cur.1, ec) where
    parent := (en, eid)
    ec     := {cur.2 with parents := parent :: cur.2.parents}
-/

def updateEClassParents (en : ENode α) (eid : EClassId) (ec : EClass α D) : EClass α D :=
  { ec with parents := (en, eid) :: ec.parents}


def updateParents (ecmap : ListMap EClassId (EClass α D)) (en : ENode α) (eid : EClassId)
  : ListMap EClassId (EClass α D) :=
  ecmap.map
    (λ id cls =>
      if id ∈ en.args then
        updateEClassParents en eid cls
      else
        cls
    )
/-
def updateParents (ecmap : List <| EClassId × EClass α D) (en : ENode α) (eid : EClassId)
  : List <| EClassId × (EClass α D) :=
  en.args.foldl (λ acc argId =>
    match acc.lookup argId with
    | some ec =>
        let updatedEc := { ec with parents := (en, eid) :: ec.parents }
        insertECMap acc argId updatedEc
    | none => acc
  ) ecmap
-/



/-
  lookupCanonicalEClassId:
    - Finds the representative of the ECID in the UF
  Calls: - N/A
  Called By:
    Repair(s), Rebuild, Union, Canonicalise
  Notes: Seems to be overused in these functions, maybe cut down
-/
def lookupCanonicalEClassId (eg : EGraph α D) (id : EClassId) : EClassId :=
  eg.uf.find id

def lookupCanonicalReturnsValid (eg : EGraph α D) (id : EClassId) (hID : eg.uf.isValidID id) (hUF : eg.uf.wellFormed):
    eg.uf.isValidID (lookupCanonicalEClassId eg id) :=
  by
    unfold UF.isValidID
    simp[lookupCanonicalEClassId]
    rw[UF.find]
    have valid := UF.findReturnsValid eg.uf hUF.left id hID
    exact valid


/-
  Canonicalise:
    - Canonicalises a node by replacing the arg ids with their canonical ids
  Calls: lookupCanonicalEClassId
  Called By: Push, Repair
-/
def canonicalise (eg : EGraph α D) (en : ENode α) : ENode α :=
  {en with args := en.args.map (lookupCanonicalEClassId eg)}


/-
  findClass:
    - Lookup the E-Node in the HashCons
  Calls:
    - N/A
  Called By:
    - Push (node canonicalised before call, no need to canon it again)
  Do we need to lookupCanonicalEClassId the hcons lookup?
-/
-- def findClass (eg : EGraph α D) (en : ENode α) : Option EClassId :=
  -- hcLookup eg en




/-
  Adds a node to the egraph
  If it exists, does nothing and returns ID
  If it doesn't, add it to the UF, E-Class Map, HCons
  Returns the new ID (which is the size of the E-Graph)

  ecmapLookup takes canonical arguments
  THINK:
    hclookup uses a canonicalised en' as key
    What is the state of the hashcons before this? -- can be anything, can't enforce anything
    doesn't make hashcons stale, either adds a new node as new class or no-op
-/
def push [Analysis α D] (eg : EGraph α D) (en : ENode α) : EGraph α D × EClassId :=
  let en' := canonicalise eg en
  match hcLookup eg en' with
  | some id => (eg, id)
  | none =>
    let (newUf, curSize) := eg.uf.push
    let ecmap'  := updateParents eg.ecmap en' curSize
    let childData := en'.args.map (λ id =>
      ((ecmapLookup eg id).getD EClass.empty).data
      -- technically says even if doesn't exist in ecmap we are fine?
      -- so should not do that
    )
    let ecmap'' := insertECMap ecmap' curSize (EClass.fromNode en' (Analysis.make en' childData))
    let hcons'  := insertHCons eg.hcons en' curSize

    (Analysis.modify {eg with
      uf := newUf,
      ecmap := ecmap'',
      hcons := hcons',
      dirty := curSize :: eg.dirty,
      aldrt := curSize :: eg.aldrt
    } curSize, curSize)

def union [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId) : EGraph α D × EClassId :=

  -- Get canonical classes for the inputs
  let id₁' := lookupCanonicalEClassId eg id₁
  let id₂' := lookupCanonicalEClassId eg id₂
  -- In same class, nothing more to do
  if id₁' = id₂' then
    (eg, id₁')
  -- In different class, we do work
  else

    -- Update union find
    let (uf', leaderClassId) := eg.uf.union id₁' id₂'
    -- Technically leader is always id₁' here
    -- but for readability we keep the names
    let toId := id₁'
    let frId := id₂'

    let lCls := (eg.ecmap.lookup toId).getD EClass.empty
    let sCls := (eg.ecmap.lookup frId).getD EClass.empty

    let newEClass := EClass.merge lCls sCls

    -- let ecmap'    := uniqueInsert (uniqueRemove eg.ecmap frId) leaderClassId newEClass

    -- Insert new leader class
    let ecmap'    := eg.ecmap.insert leaderClassId newEClass
    -- Replace old follower class with empty class for.... idk reasons (leave alone because I don't think deleting is good in array later)
    let ecmap''   := ecmap'.insert   frId          EClass.empty

    let newData   := newEClass.data
    let newDirty  := leaderClassId :: eg.dirty
    let newAldrt  :=
      (if newData != sCls.data then [leaderClassId] else [])
      ++
      (if newData != lCls.data then [leaderClassId] else [])
      ++
      eg.aldrt

    let eg' := {
      eg with
      uf    := uf',
      ecmap := ecmap'',
      dirty := newDirty,
      aldrt := newAldrt
    }

    (Analysis.modify eg' leaderClassId, leaderClassId)


def repairAnalysis [Analysis α D] (eg : EGraph α D) (id : EClassId) : EGraph α D :=
  let canonId := lookupCanonicalEClassId eg id

  match eg.ecmap.lookup canonId with
  | none => eg
  | some cls =>
    let newData := cls.nodes.map (λ en =>
      let canonArgs := en.args.map (lookupCanonicalEClassId eg)
      let childData := canonArgs.map (λ argId =>
        ((eg.ecmap.lookup argId).getD EClass.empty).data
      )
      Analysis.make en childData
    )

    let joinData := newData.foldl (Analysis.join (α := α) (D := D)) cls.data

    if joinData ≠ cls.data then
      let cls' := { cls with data := joinData}
      let parentIds := cls.parents.map Prod.snd
      let eg' := { eg with
        ecmap := insertECMap eg.ecmap canonId cls',
        aldrt := parentIds ++ eg.aldrt
      }

      Analysis.modify eg' canonId
    else eg

def repairLoop1 (eg : EGraph α D) (eCls : EClass α D) : EGraph α D  × List (EClassId × EClassId) :=
    let (updateHCons, collisions) := eCls.parents.foldl (init := (eg.hcons, [])) (λ (hcons', collisions') (node, pId) =>
    let canonNode := canonicalise eg node
    let canonId  := lookupCanonicalEClassId eg pId
    let det      := hcons'.remove node --hcons'.filter (λ hc => hc.1 ≠ node)
    match det.lookup canonNode with
    | some key => (det, (canonId, key) :: collisions')
    | none     => (det.insert canonNode canonId, collisions')
    )
  let eg' := {eg with hcons := updateHCons}

  (eg', collisions)

def repairLoop2 (eg : EGraph α D) (eCls : EClass α D) : EClass α D × List (EClassId × EClassId) :=
  let (_, pc) := eCls.parents.foldl (init := ([], [])) (λ (seen, pc) (p : (ENode α × EClassId)) =>
    let canon := canonicalise eg p.1
    let canonId := lookupCanonicalEClassId eg p.2
    match seen.lookup canon with
    | some eid => (seen, (eid, canonId) :: pc)
    | none     => ((canon, canonId) :: seen, pc)
  )

  let newNodes := eCls.nodes.foldl (init := []) (λ newN en =>
    let canonN := canonicalise eg en -- or eg'?
    -- if newN.any (λ a => a == canonN) then newN else canonN :: newN
    if newN.contains canonN then newN else canonN :: newN
  )

  let newParents := eCls.parents.foldl (init := []) (λ newP (en, eid) =>
    let canonN  := canonicalise eg en
    let canonId := lookupCanonicalEClassId eg eid
    if newP.any (λ (an, ac) => an == canonN && ac == canonId) then newP else (canonN, canonId) :: newP
  )

  ({nodes := newNodes, parents := newParents, data := eCls.data}, pc)


def repair (eg : EGraph α D) (id : EClassId) : EGraph α D × (List <| EClassId × EClassId) :=
  let canonId := lookupCanonicalEClassId eg id

  match ecmapLookup eg canonId with
  | none => (eg, []) --
  | some eCls =>

    -- Hashcons Repair Loop
    let (eg', collisions) := repairLoop1 eg eCls

    -- Loop 2...
    -- Repairs eClass
    let (eCls', pc) := repairLoop2 eg' eCls

    let eg'' := { eg' with
      ecmap := insertECMap eg'.ecmap canonId eCls'
    }

    (eg'', collisions ++ pc)


def rebuildTerminationBy (eg : EGraph α D) : Nat × Nat :=
  let work := eg.dirty.length + eg.aldrt.length
  let classes := numCanonClasses eg
  (classes, work)


def mergeCollisions [Analysis α D] (eg : EGraph α D) (collisions : List <| EClassId × EClassId)
    : EGraph α D :=
  collisions.foldl (λ acc (id₁, id₂) =>
    (union acc id₁ id₂).1) eg

def congruenceRepair [Analysis α D] (eg : EGraph α D) : EGraph α D :=
  let todo := eg.dirty.map (lookupCanonicalEClassId eg) |>.eraseDups
  let eg'  := {eg with dirty := []}

  -- Pass through dirty (congruence repair)
  -- extract the nested loop for readability
  let eg'' := todo.foldl (λ eg₁ id =>
    let (eg₂, collisions) := repair eg₁ id
    mergeCollisions eg₂ collisions
  ) eg'
    /-
    collisions.foldl (λ acc (id₁, id₂) =>
      (union acc id₁ id₂).1) eg₂
    ) eg'
    -/

  eg''

def analysisRepair [Analysis α D] (eg : EGraph α D) : EGraph α D :=
  -- Pass through aldrt (uh... analysis repair?)
  let atodo := eg.aldrt.map (lookupCanonicalEClassId eg) |>.eraseDups
  let eg'   := { eg with aldrt := [] }
  let eg''   := atodo.foldl repairAnalysis eg'

  eg''


def singleRebuildPass [Analysis α D] (eg : EGraph α D) : EGraph α D :=
  let eg' := congruenceRepair eg
  let eg'':= analysisRepair eg'
  eg''


partial def rebuild [Analysis α D] (eg : EGraph α D) : EGraph α D :=
  if eg.dirty.isEmpty && eg.aldrt.isEmpty then eg
  else
    let eg' := singleRebuildPass eg
    rebuild eg'




/-
  Exports for outside use
-/
abbrev EGraphM (α : Type _) (D : Type _) [DecidableEq α] [Hashable α] := StateM (EGraph α D)

def lookupCanonicalEClassIdM (id : EClassId) : EGraphM α D EClassId := do
  return lookupCanonicalEClassId (← get) id

def pushM [Analysis α D] (en : ENode α) : EGraphM α D EClassId := do
  let (eg', id) := push (← get) en
  discard <| set eg'
  return id

def unionM [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := do
  let (eg', leader) := union (← get) id₁ id₂
  set eg'
  return leader

def rebuildM [Analysis α D] : EGraphM α D Unit := do
  set (rebuild (← get))



























/-
def lookupCanonicalEClassId (id : EClassId) : EGraphM α D <| EClassId := do
  let eg ← get
  let ⟨uf', res⟩ := eg.uf.ufFind id
  let _ ← set { eg with uf := uf' }
  return res
-/
/-
def lookupCanonicalEClassIdM (id : EClassId) : EGraphM α D <| EClassId := do
  let eg ← get
  return eg.uf.find id

def canonicaliseM (en : ENode α) : EGraphM α D (ENode α) := do
  let newargs : List EClassId ← en.args.mapM lookupCanonicalEClassIdM
  return { en with args := newargs}
-/
/-
def betterCanonicaliseM? (en : ENode α) : EGraphM α D (ENode α) := do
  let eg ← get
  return canonicalise eg en
-/


/-
def findClassM (en : ENode α) : EGraphM α D (Option EClassId) := do
  -- let en' ← canonicalise en
  let eg ← get
  /-
  match eg.hcons.lookup en with
  | some eClassId =>
    return some eClassId
  | none =>
    return none
  -/
  -- return eg.hcons.lookup en
  return hcLookup eg en
-/



/-
termination_by rebuildTerminationBy eg -- (numClasses eg, eg.dirty.length + eg.aldrt.length)
decreasing_by
  simp_wf
  cases
  case pos => sorry
  case neg => sorry
  sorry
-/
-- https://leanprover-community.github.io/extras/well_founded_recursion.html
-- Bottom of the page has example on Nat × Nat

-- TODO: study:
-- https://web.archive.org/web/20250618125453/https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/
-- https://www.joachim-breitner.de/blog/817-F91_in_Lean
-- https://notch1p.xyz/fixpoint-comb (translate)
/-
termination_by λ eg : EGraph α D => rebuildTerminationBy eg
decreasing_by
  simp

  sorry
-/
/-
  For Testing And Execution
  TODO: macros
-/
/-
def pushRun [Analysis α D] (en : ENode α) : EGraphM α D EClassId := do
  let id ← push en Analysis.make
  return id

def unionRun [Analysis α D] (id₁ id₂ : EClassId) : EGraphM α D EClassId := do
  let id ← union id₁ id₂
  return id
-/

/-
  Props that might be needed eventually?
-/





/-
  ecmap : List <| EClassId × (EClass α D)
  hcons : List <| ENode α × EClassId
  dirty : List EClassId
  aldrt : List <| EClassId × ENode α
-/




end Naive
