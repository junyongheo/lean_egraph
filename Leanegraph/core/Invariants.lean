import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps
import Leanegraph.core.Naive
import Leanegraph.core.NaiveDefs
import Leanegraph.core.SharedDefs
import Leanegraph.core.MathlibJjajibgi

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

/-
  Helpers
-/
def inEClass (eg : EGraph α D) (en : ENode α) (id : EClassId) : Prop :=
  ∃ ecls, ecmapLookup eg id = some ecls ∧ en ∈ ecls.nodes


/-
  Represented
-/

mutual
/-
def nodeRepresentsTerm (eg : EGraph α D) (en : ENode α) (t : Term α) : Prop :=
  en.head = t.head ∧ Forall₂ (classRepresentsTerm eg) en.args t.args
-/
inductive nodeRepresentsTerm (eg : EGraph α D) : ENode α → Term α → Prop where
  | node :
      ∀ (en : ENode α) (t : Term α),
           en.head = t.head →
           Forall₂ (classRepresentsTerm eg) en.args t.args →
           nodeRepresentsTerm eg en t

inductive classRepresentsTerm (eg : EGraph α D) : EClassId → Term α → Prop where
  | cls :
      ∀ (id : EClassId) (t : Term α),
          (en : ENode α) →
          inEClass eg en id →
          nodeRepresentsTerm eg en t →
          classRepresentsTerm eg id t
end

def egraphRepresentsTerm (eg : EGraph α D) (t : Term α) : Prop :=
  ∃ id, classRepresentsTerm eg id t


/-
  Equivalences
-/

def EquivECId (eg : EGraph α D) (id₁ id₂ : EClassId) : Prop :=
  lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂

def EquivENode (eg : EGraph α D) (en₁ en₂ : ENode α) : Prop :=
  ∃ id, inEClass eg en₁ id ∧ inEClass eg en₂ id

def EquivTerm (eg : EGraph α D) (t₁ t₂ : Term α) : Prop :=
  ∃ (id : EClassId),
    classRepresentsTerm eg id t₁ ∧ classRepresentsTerm eg id t₂




/-
  Props of E-Nodes
-/
-- An ENode is canonical if all arguments are canonical
def ENode.isCanonical (en : ENode α) (eg : EGraph α D) : Prop :=
  ∀ arg ∈ en.args, arg = lookupCanonicalEClassId eg arg
  -- en.args.map (lookupCanonicalEClassId eg) = en.args
  -- should be the same, figure out which one is better

-- Two ENodes are congruent if head is equal, all args are in same eclass ≅
def ENode.congrRel (en₁ en₂ : ENode α) (eg : EGraph α D) : Prop :=
-- Is there a zip in lean?
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Forall2.html This is pretty cool
-- Oh it's mathlib
-- Back to zip
  -- en₁.head = en₂.head ∧ (en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId a = lookupCanonicalEClassId b)

  en₁.head = en₂.head ∧
    Forall₂ (λ a b => EquivECId eg a b) en₁.args en₂.args
  --en₁.args.length = en₂.args.length ∧
  --(en₁.args.zip en₂.args).all (λ (a, b) ↦ lookupCanonicalEClassId eg a = lookupCanonicalEClassId eg b)



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
  Congruence Closure

-- on node equivalence, we want a relation R (EquivENode), two ENodes (feed as args)
-- within the context of the egraph (feed as arg), which handles eclasses so
-- only EGraph → ENode → ENode → Prop?
--
  From egg (paraphrased): Congruence closure is the smallest superset of ≣node that is
  also the smallest superset of ≅
  To build congruence closure therefore we start with both of these as a base relation

-/

/-
  Try 1:
-/
inductive CongruenceClosure (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            CongruenceClosure eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel en₁ en₂ eg →
            CongruenceClosure eg en₁ en₂
| refl  : (en  : ENode α) →
            CongruenceClosure eg en  en
| symm  : (en₁ : ENode α) → (en₂ : ENode α) → CongruenceClosure eg en₁ en₂ →
            CongruenceClosure eg en₂ en₁
| trans : (en₁ : ENode α) → (en₂ : ENode α) → (en₃ : ENode α) → CongruenceClosure eg en₁ en₂ → CongruenceClosure eg en₂ en₃ →
            CongruenceClosure eg en₁ en₃

/-
  Try 2:
-/
inductive SingleStepOfCongruence (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            SingleStepOfCongruence eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel en₁ en₂ eg →
            SingleStepOfCongruence eg en₁ en₂


inductive CongruenceClosure2 (eg : EGraph α D) : ENode α → ENode α → Prop where
| refl  : (en          : ENode α) → CongruenceClosure2 eg en en
| symm  : (en₁ en₂     : ENode α) → CongruenceClosure2 eg en₁ en₂ → CongruenceClosure2 eg en₂ en₁
| trans : (en₁ en₂ en₃ : ENode α) → CongruenceClosure2 eg en₁ en₂ → CongruenceClosure2 eg en₂ en₃ → CongruenceClosure2 eg en₁ en₃


/-
  Try 3:
-/
inductive SingleStepOfCongruence' (eg : EGraph α D) : ENode α → ENode α → Prop where
| equiv : (en₁ : ENode α) → (en₂ : ENode α) → EquivENode eg en₁ en₂ →
            SingleStepOfCongruence' eg en₁ en₂
| struc : (en₁ : ENode α) → (en₂ : ENode α) → ENode.congrRel en₁ en₂ eg →
            SingleStepOfCongruence' eg en₁ en₂
-- | refl  : (en  : ENode α) → SingleStepOfCongruence' eg en en -- technically same as CC3.refl
| symm  : (en₁ : ENode α) → (en₂ : ENode α) → SingleStepOfCongruence' eg en₁ en₂ → SingleStepOfCongruence' eg en₂ en₁



inductive CongruenceClosure3 (eg : EGraph α D) : ENode α → ENode α → Prop where
| refl  : (en          : ENode α) → CongruenceClosure3 eg en  en
| chain : (en₁ en₂ en₃ : ENode α) → CongruenceClosure3 eg en₁ en₂ → SingleStepOfCongruence' eg en₂ en₃ → CongruenceClosure3 eg en₁ en₃


/-
-- doesn't work as well as the above?
inductive CongruenceClosure (eg : EGraph α D) (en₁ : ENode α) (en₂ : ENode α) : Prop where
| equiv : EquivENode eg en₁ en₂        → CongruenceClosure eg en₁ en₂
| congr : ENode.isCongruent en₁ en₂ eg → CongruenceClosure eg en₁ en₂
| symm  : CongruenceClosure eg en₁ en₂ → CongruenceClosure eg en₂ en₁ -- doesn't work
-/
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

/-
def EGraph.congruenceInvariant
    -- (eg : EGraph α D) (en₁ en₂ : ENode α) (id₁ id₂ : EClassId) : Prop := -- no need to specify
    (eg : EGraph α D) : Prop :=
      ∀ en₁ en₂ id₁ id₂, -- forall en/id ₁₂ where
        eg.hcons.lookup en₁ = some id₁ → -- id₁ is the canon class of en₁
        eg.hcons.lookup en₂ = some id₂ → -- and id₂ of en₂
        ENode.isCongruent en₁ en₂ eg →  -- and the two nodes are congruent
        lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂ -- the two nodes are in the same e-class
-/

def EGraph.congruenceInvariant (eg : EGraph α D) : Prop :=
  ∀ (en₁ en₂ : ENode α),
    EquivENode eg en₁ en₂ ↔ CongruenceClosure3 eg en₁ en₂

def EGraph.uniqueContained (eg : EGraph α D) : Prop :=
  ∀ (en : ENode α) (id₁ id₂ : EClassId),
    hcLookup eg en = some id₁ →
    hcLookup eg en = some id₂ →
    lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂


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
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm⟩
  rcases hUfWf with ⟨hUfv, hUfc⟩
  repeat constructor
  · -- isValid
    -- show that pushing does not change the validity of the unionfind
    -- do we not have this already?
    have isValid := UF.pushPreservesValid _ hUfv

    unfold push
    dsimp
    split
    ·
      exact hUfv
    case h_2 optEid noneLookup =>
      simp[isValid]
  · -- isCanon
    -- show that pushing does not change the canonicity of the unionfind
    have isCanon := UF.pushPreservesCanon _ hUfc hUfv
    unfold push
    dsimp
    split
    case h_1 ecId id lookupSome =>
      simp[hUfc]
    case h_2 eid lookupNone =>
      exact isCanon
  · -- hconsToECmap?
    constructor
    ·
      unfold push
      dsimp
      split
      case h_1 opeid id lookupSome =>
        exact hDv
      case h_2 oid lookupNone =>
        simp only
        unfold EGraph.dirtyValid
        intro id hmem
        dsimp at *
        unfold UF.isValidID
        have hmem' := List.mem_cons.mp hmem
        rcases hmem' with hnew | hold
        ·
          simp[hnew, UF.push, UF.size]
        ·
          simp[UF.push, UF.size]
          simp[UF.push, UF.size] at hmem
          rcases hmem with rfl | hold
          ·
            simp
          ·
            have hid := hDv id hold
            simp[UF.isValidID] at hid
            simp[UF.size] at hid
            have hpo : id < List.length eg.uf + 1 := Nat.lt_trans hid (Nat.lt_add_one _)
            exact hpo
    ·
      constructor
      ·
        -- exactly the same as the above branch, which makes me
        -- feel like im doing something wrong?
        unfold push
        dsimp only
        split
        case h_1 oeid id lookupSome =>
          exact hAv
        case h_2 oeid lookupNone =>
          simp only
          unfold EGraph.aldrtValid
          intro id hmem
          dsimp at *
          unfold UF.isValidID
          have hmem' := List.mem_cons.mp hmem
          rcases hmem' with hnew | hold
          ·
            simp[hnew, UF.push, UF.size]
          ·
            simp[UF.push, UF.size]
            simp[UF.push, UF.size] at hmem
            rcases hmem with rfl | hold
            ·
              simp
            ·
              have hid := hAv id hold
              simp[UF.isValidID, UF.size] at hid
              exact Nat.lt_trans hid (Nat.lt_add_one _)
      ·
        unfold push
        dsimp only
        split
        case h_1 oid id lookupSome =>
          simpa
        case h_2 oid lookupNone =>
          simp only
          unfold EGraph.hconsToEcmap
          intro en₁ id₁ hLookup
          simp[hcLookup] at hLookup
          sorry

theorem unionPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.alwaysInvariants := by
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc⟩
  rcases hUfwf with ⟨hv, hc⟩
  repeat constructor
  · -- isValid
    simp[UF.isValid]
    intro id cid hmem

    constructor
    ·
      simp[UF.isValidID]
      simp[UF.isValid] at hv
      have yeah := hv id cid _
      sorry
      /-
      dsimp[union] at hmem
      split at hmem
      case isTrue aa =>
        simp at hmem

        sorry
      case isFalse hh =>
        dsimp at hmem

        sorry
      -/
    ·

      sorry

  · -- isCanon
    have hUPC := UF.unionPreservesCanon eg.uf hc id₁ id₂
    dsimp[union]
    split
    case isTrue aa =>
      exact hc
    case isFalse bb =>
      simp[lookupCanonicalEClassId] at *
      simp[UF.union]
      simp[UF.findIdempotent eg.uf hc id₁] at *
      simp[UF.findIdempotent eg.uf hc id₂] at *
      simpa[UF.union, bb] using hUPC
      /-
      dsimp[UF.union]
      simp[lookupCanonicalEClassId] at *
      simp[UF.findIdempotent eg.uf hc, bb]
      simp [UF.isCanon] at hc
      -/
  repeat constructor -- it is obviously possible why did you stop
  · -- dirtyValid
    simp[EGraph.dirtyValid]
    intro id hmem
    simp[UF.isValidID]
    unfold union
    dsimp
    split
    case isTrue wasEq =>
      unfold EGraph.dirtyValid at hDv
      simp[union, wasEq] at hmem
      have valid := hDv id hmem
      simp[UF.isValidID] at *
      exact valid
    case isFalse nEq =>
      --simp[union, nEq] at hmem
      unfold union at hmem
      dsimp at hmem
      simp[nEq] at hmem
      simp at *
      have noLength := UF.unionPreservesSize eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
      simp[noLength]
      rcases hmem with hnew | hold
      ·
        simp[hnew]
        -- have hlv' := UF.unionLeaderValid eg.uf id₁ id₂ h₁ h₂ hv
        have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁ -- idk what goes in _ actually lol
        have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
        have hlv := UF.unionLeaderValid eg.uf
          (lookupCanonicalEClassId eg id₁)
          (lookupCanonicalEClassId eg id₂)
          v₁ v₂ hv
        exact hlv
      ·
        unfold EGraph.dirtyValid at hDv
        exact hDv id hold

  repeat constructor
  · -- aldrtValid
    simp[EGraph.aldrtValid]
    intro id hmem
    simp[UF.isValidID]
    unfold union
    dsimp
    split
    case isTrue wasEq =>
      unfold EGraph.aldrtValid at hAv
      simp[union, wasEq] at hmem
      have valid := hAv id hmem
      simp[UF.isValidID] at *
      exact valid
    case isFalse nEq =>
      unfold union at hmem
      dsimp at hmem
      simp[nEq] at hmem
      simp
      have noLength := UF.unionPreservesSize eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
      simp[noLength]
      rcases hmem with hnew | hold
      ·
        simp[hnew]
        have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
        have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
        exact UF.unionLeaderValid eg.uf
          (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
          v₁ v₂ hv
      ·
        rcases hold
        case inr.inl h =>
          rcases h with ⟨_, b⟩
          have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
          have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
          have aaa := UF.unionLeaderValid eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) v₁ v₂ hv
          simpa[←b] using aaa -- does simpa help readability
        case inr.inr h =>
          -- have aaa := UF.unionPreservesSize eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
          -- simp[aaa] at *
          simp[EGraph.aldrtValid] at hAv
          exact hAv id h


  · -- hconsToECMap
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
        lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂ ↔ CongruenceClosure3 eg en₁ en₂ := by
  sorry

end Naive

theorem foo : 1 + 1 = 2 := by
  exact
  by
    exact
    by
      exact
      by
        exact
        by
          exact
          by
            exact
            by
              exact
              by
                exact
                by
                  exact
                  by
                    exact
                    by
                      rfl
