import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps
import Leanegraph.core.Naive
import Leanegraph.core.NaiveDefs
import Leanegraph.core.SharedDefs
import Leanegraph.core.Invariants

variable {α : Type _} [DecidableEq α] [Hashable α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

theorem pushPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).1.alwaysInvariants := by
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  constructor
  constructor
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
  constructor
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
  constructor
  · -- hasRep
    sorry
  · -- isComplete
    sorry
  constructor
  · -- dirtyValid
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
  constructor
  · -- aldrtValid
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
  · -- hconsToECMap
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





/-
theorem pushPreservesAlwaysInvariants'' [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).1.alwaysInvariants := by
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  repeat constructor
  constructor
  constructor
  ·
    sorry
  constructor
  ·
    sorry
    ·
      constructor
      ·
        -- exactly the same as the above branch, which makes me
        -- feel like im doing something wrong?
-/

theorem unionPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.alwaysInvariants := by
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  repeat constructor
  · -- isValid
    simp[UF.isValid]
    intro id cid hmem

    constructor
    ·
      simp[UF.isValidID]
      --have hps := UF.unionPreservesSize eg.uf id₁ id₂
      dsimp[union] at hmem
      split at hmem
      case isTrue aa =>
        simp at hmem
        have ⟨hV, hC⟩ := hv id cid hmem
        simp[union, aa]
        simp[UF.isValidID] at hV
        exact hV

      case isFalse bb =>
        simp at hmem
        simp[union, bb]
        have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
        have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
        have hvs := UF.unionPreservesValid eg.uf hv (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) v₁
        -- have ⟨hl, _⟩ := hvs id cid hmem
        exact (hvs id cid hmem).1

    ·
      simp[UF.isValidID]
      dsimp[union] at hmem
      split at hmem
      case isTrue aa =>
        simp at hmem
        have ⟨hV, hC⟩ := hv id cid hmem
        simp[union, aa]
        exact hC
      case isFalse bb =>
        simp at hmem
        simp[union, bb]
        have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
        have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
        have hvs := UF.unionPreservesValid eg.uf hv (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) v₁
        exact (hvs id cid hmem).2
  constructor
  · -- isCanon
    -- have hUPC := UF.unionPreservesCanon eg.uf hc (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
    dsimp[union]
    split
    case isTrue aa =>
      exact hc
    case isFalse bb =>
      simp[lookupCanonicalEClassId] at *
      exact UF.unionPreservesCanon eg.uf hc (eg.uf.find id₁) (eg.uf.find id₂)
      -- interesting that the proof got shorter?

      -- simp[UF.union]
      -- simp[UF.findIdempotent eg.uf hc id₁] at *
      -- simp[UF.findIdempotent eg.uf hc id₂] at *
      -- simpa[UF.union, bb] using hUPC
      -- simp only [bb]
      --unfold changeLeader

      /-
      dsimp[UF.union]
      simp[lookupCanonicalEClassId] at *
      simp[UF.findIdempotent eg.uf hc, bb]
      simp [UF.isCanon] at hc
      -/
  repeat constructor -- it is obviously possible why did you stop
  · -- hasRep
    dsimp[union]
    split
    case isTrue aa =>
      simp[hR]
    case isFalse bb =>
      simp only
      have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
      have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
      exact UF.unionPreservesReps eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) hwf v₁ v₂
  constructor
  · -- isComplete
    dsimp[union]
    split
    case isTrue aa =>
      simp[hCmp]
    case isFalse bb =>
      simp only
      exact UF.unionPreservesComplete eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) hwf
  · -- uniqueKeys
    dsimp[union]
    split
    case isTrue aa =>
      simp[hU]
    case isFalse bb =>
      simp only
      exact UF.unionPreservesUniqueKeys eg.uf hU (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
  constructor
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

theorem rebuildOncePreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) :
    (singleRebuildPass eg).alwaysInvariants := by
  sorry

-- TODO: needed but idk how to structure files
/-
theorem rebuildPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) :
    (rebuild eg).alwaysInvariants := by
  unfold rebuild
  split
  case isTrue _ =>
    assumption
  case isFalse cond =>
    simp only
    have hSingleLoop := rebuildOncePreservesAlwaysInvariants eg h
    -- simp[hSingleLoop]
    -- need induction on this...

    sorry



-- Invariants that are repaired by the rebuild process
def EGraph.afterRebuildInvariants (eg : EGraph α D) : Prop :=
  eg.alwaysInvariants ∧ eg.hashconsInvariant ∧ eg.congruenceInvariant ∧ eg.isClean
-- if hashconsInv → congruenceInv then this only needs to mention 3?

theorem rebuildRestoresInvariants [Analysis α D] (eg : EGraph α D)
    (h : eg.alwaysInvariants) : (rebuild eg).afterRebuildInvariants := by
  simp[EGraph.afterRebuildInvariants]
  refine ⟨rebuildPreservesAlwaysInvariants eg h, ?_⟩
  sorry
-/

/-
theorem twoNodesInSameEClassMustBeCongruent [Analysis α D] (eg : EGraph α D)
    (h : eg.afterRebuildInvariants) (id₁ id₂ : EClassId) (en₁ en₂ : ENode α) :

  sorry
-/


-- Talk about the newly extracted mini-functions of repair and rebuild
omit [DecidableEq D] [Inhabited D] in
theorem repairLoop1NoTouchUF (eg : EGraph α D) (eCls : EClass α D) :
    (repairLoop1 eg eCls).1.uf = eg.uf := by
  unfold repairLoop1
  simp


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

/--
-- Ultimate Theorem?
theorem egraphCorrect [Analysis α D] (eg : EGraph α D)
    (h : eg.afterRebuildInvariants) (en₁ en₂ : ENode α) (id₁ id₂ : EClassId)
      (h₁ : inEClass eg en₁ id₁) (h₂ : inEClass eg en₂ id₂) :
      -- two nodes are congruent iff same class
        lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂ ↔ CongruenceClosure3 eg en₁ en₂ := by
  sorry
-/

-- end Naive

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
