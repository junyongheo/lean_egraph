import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps
import Leanegraph.core.Naive
import Leanegraph.core.NaiveDefs
import Leanegraph.core.SharedDefs

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

/-
  Props of E-Nodes
-/
-- An ENode is canonical if all arguments are canonical
def ENode.isCanonical (en : ENode α) (eg : EGraph α D) : Prop :=
  ∀ arg ∈ en.args, arg = lookupCanonicalEClassId eg arg
  -- en.args.map (lookupCanonicalEClassId eg) = en.args
  -- should be the same, figure out which one is better

-- Two ENodes are congruent if head is equal, all args are in same eclass
def ENode.isCongruent (en₁ en₂ : ENode α) (eg : EGraph α D) : Prop :=
-- Is there a zip in lean?
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Forall2.html This is pretty cool
-- Oh it's mathlib
-- Back to zip
  -- en₁.head = en₂.head ∧ (en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId a = lookupCanonicalEClassId b)
  en₁.head = en₂.head ∧
  en₁.args.length = en₂.args.length ∧
  (en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId eg a = lookupCanonicalEClassId eg b)



-- EGraph Components
-- ecmap, hcons always unique keys if the functions defined in ListAsMaps.lean are used


/-
  Props about the EGraph State
-/
def EGraph.isClean (eg : EGraph α D) : Prop :=
  eg.dirty.isEmpty ∧ eg.aldrt.isEmpty

/-
  That the dirty and aldrt (analysis dirty) lists hold only valid IDs
-/
def EGraph.dirtyValid (eg : EGraph α D) : Prop :=
  ∀ id ∈ eg.dirty, eg.uf.isValidID id

def EGraph.aldrtValid (eg : EGraph α D) : Prop :=
  ∀ id ∈ eg.aldrt, eg.uf.isValidID id


-- Hashcons is correct when all enodes in it are canonical and the enodes point to a canonical id
-- Hashcons can be stale, between union and rebuild
def hashconsCanonical (eg : EGraph α D) : Prop :=
  ∀ en id, eg.hcons.lookup en = some id → en.isCanonical eg ∧ lookupCanonicalEClassId eg id = id


-- every valid entry in hcons is valid in the ecmap (when canon id)
-- does this hold between union and rebuild
-- connects the 3 parts of the egr
def EGraph.hconsToEcmap (eg : EGraph α D) : Prop :=
  ∀ en id, hcLookup eg en = some id →
    ∃ cls, ecmapLookup eg (lookupCanonicalEClassId eg id) = some cls

/-
  Define the two main invariants for E-Graphs.
  1. Congruence Invariant
    The e-graph must ensure that congruent e-nodes are in the same e-class

  2. Hashcons Invariant
    From Egg: e-node 𝑛∈𝑀[𝑎] ⇐⇒ 𝐻[canonicalize(𝑛)]=find(𝑎)
    The hashcons 𝐻 must map all canonical e-nodes to their e-class ids
    enode en is in eclass (ecmap id₁) IFF hashcons.lookup(en) = uf.find id

  Bonus: Some analysis invariant?
    ∀𝑐∈𝐺. 𝑑𝑐=Ûmake(𝑛) and modify(𝑐)=𝑐 (copied egg pg.13, idk how to type that, TODO: )
-/
def EGraph.congruenceInvariant
    -- (eg : EGraph α D) (en₁ en₂ : ENode α) (id₁ id₂ : EClassId) : Prop := -- no need to specify
    (eg : EGraph α D) : Prop :=
      ∀ en₁ en₂ id₁ id₂, -- forall en/id ₁₂ where
        eg.hcons.lookup en₁ = some id₁ → -- id₁ is the canon class of en₁
        eg.hcons.lookup en₂ = some id₂ → -- and id₂ of en₂
        ENode.isCongruent en₁ en₂ eg →  -- and the two nodes are congruent
        lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂ -- the two nodes are in the same e-class


def inEClass (eg : EGraph α D) (en : ENode α) (id : EClassId) : Prop :=
  ∃ ecls, ecmapLookup eg id = some ecls ∧ en ∈ ecls.nodes

def EGraph.hashconsInvariant (eg : EGraph α D) : Prop :=
  ∀ (en : ENode α) (id : EClassId),
    -- e-node 𝑛∈𝑀[𝑎]
    inEClass eg en id
    ↔
    -- 𝐻[canonicalize(𝑛)]=find(𝑎)
    hcLookup eg (canonicalise eg en) = lookupCanonicalEClassId eg id
-- huh doesn't this imply the congruenceInvariant? In the ← direction?
-- TODO: go for this one first, I think?


-- Invariants that must always hold
def EGraph.alwaysInvariants (eg : EGraph α D) : Prop :=
  UF.wellFormed eg.uf ∧ -- all IDs are valid and is flat
  -- ecmap/hcons has unique keys, but that is from subtype, not mentioned here
  -- still keep that in mind, probably need
  eg.dirtyValid ∧
  eg.aldrtValid ∧
  eg.hconsToEcmap
  -- i think this is about it?
  -- hcons can go stale, ecmap can go stale
  -- uf is i think always valid?

theorem pushPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).1.alwaysInvariants := by
  sorry

theorem unionPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId) :
    (union eg id₁ id₂).1.alwaysInvariants := by
  sorry

theorem repairPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id : EClassId) :
    (repair eg id).1.alwaysInvariants := by
  sorry

theorem rebuildPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id : EClassId) :
    (singleRebuildPass eg).alwaysInvariants := by
  sorry



-- Invariants that are repaired by the rebuild process
def EGraph.afterRebuildInvariants (eg : EGraph α D) : Prop :=
  eg.alwaysInvariants ∧ eg.hashconsInvariant ∧ eg.congruenceInvariant ∧ eg.isClean
-- if hashconsInv → congruenceInv then this only needs to mention 3?

theorem rebuildRestoresInvariants [Analysis α D] (eg : EGraph α D)
    (h : eg.alwaysInvariants) : (rebuild eg).afterRebuildInvariants := by
  sorry


/-
theorem twoNodesInSameEClassMustBeCongruent [Analysis α D] (eg : EGraph α D)
    (h : eg.afterRebuildInvariants) (id₁ id₂ : EClassId) (en₁ en₂ : ENode α) :

  sorry
-/


-- Talk about the newly extracted mini-functions of repair and rebuild
theorem repairLoop1NoTouchUF (eg : EGraph α D) (eCls : EClass α D) :
    (repairLoop1 eg eCls).1.uf = eg.uf := by
  sorry

theorem repairLoop1HConsRepaired (eg : EGraph α D) (eCls : EClass α D) :
    ∀ (id₁ id₂ : EClassId), (id₁, id₂) ∈ (repairLoop1 eg eCls).2 →
      ∃ en, hcLookup eg en = some id₁ ∨ hcLookup eg en = some id₂ := by
  sorry


-- theorem repairLoop2UpdatesEClassOnly (eg : EGraph α D) (eCls : EClass α D) :
-- also a NoTouchUF, but also NoTouchHCons/ECMap/Anything
-- This doesn't touch eg
-- Doesn't even return an eg. What now?
--   (repairLoop2 eg eCls)

theorem mergeCollisionsPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
    (h : eg.alwaysInvariants) (collisions : List (EClassId × EClassId)) :
      (mergeCollisions eg collisions).alwaysInvariants := by
  sorry

theorem congruenceRepairPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D) (h : eg.alwaysInvariants) :
    (congruenceRepair eg).alwaysInvariants := by
  sorry

theorem analysisRepairPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D) (h : eg.alwaysInvariants) :
    (analysisRepair eg).alwaysInvariants := by
  sorry

theorem singleRebuildPassPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D) (h : eg.alwaysInvariants) :
    (singleRebuildPass eg).alwaysInvariants := by
  simp[singleRebuildPass]
  apply analysisRepairPreservesAlwaysInvariants
  apply congruenceRepairPreservesAlwaysInvariants
  apply h


-- Ultimate Theorem?
theorem egraphCorrect [Analysis α D] (eg : EGraph α D)
    (h : eg.afterRebuildInvariants) (en₁ en₂ : ENode α) (id₁ id₂ : EClassId)
      (h₁ : inEClass eg en₁ id₁) (h₂ : inEClass eg en₂ id₂) :
      -- two nodes are congruent iff same class
        eg.uf.find id₁ = eg.uf.find id₂ ↔ ENode.isCongruent en₁ en₂ eg := by
  sorry

end Naive
