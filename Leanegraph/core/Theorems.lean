import Leanegraph.core.UnionFind
import Leanegraph.core.ListAsMaps
import Leanegraph.core.Naive
import Leanegraph.core.NaiveDefs
import Leanegraph.core.SharedDefs
import Leanegraph.core.Invariants

variable {α : Type _} [DecidableEq α] [Hashable α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive

theorem lookupAfterUnionSome [Analysis α D] (eg : EGraph α D) (en : ENode α) (id₁ id₂ id : EClassId)
    (hcsome : eg.hcons.lookup en = some id):
      (union eg id₁ id₂).fst.hcons.lookup en = some id := by
  simp[union]
  split
  case isTrue h =>
    simp[hcsome]
  case isFalse h =>
    simp[hcsome]

theorem lookupBeforeUnionSome [Analysis α D] (eg : EGraph α D) (en : ENode α) (id₁ id₂ id : EClassId)
    (hcsome : (union eg id₁ id₂).fst.hcons.lookup en = some id)
    : eg.hcons.lookup en = some id
    := by
  simp[union] at hcsome
  split at hcsome
  case isTrue h =>
    simpa using hcsome
  case isFalse h =>
    simpa using hcsome

theorem unionDoesntChangeHCLookupSome [Analysis α D] (eg : EGraph α D) (en : ENode α) (id₁ id₂ id : EClassId) :
    eg.hcons.lookup en = some id ↔  (union eg id₁ id₂).fst.hcons.lookup en = some id := by
  apply Iff.intro
  exact lookupAfterUnionSome eg en id₁ id₂ id
  exact lookupBeforeUnionSome eg en id₁ id₂ id

omit [DecidableEq D] [Inhabited D] in
theorem canonicaliseIdem [Analysis α D] (eg : EGraph α D) (en : ENode α) (h : eg.uf.isCanon) :
    (canonicalise eg en) = canonicalise eg (canonicalise eg en) := by
  simp[canonicalise]
  intro ecid mem
  simp[lookupCanonicalEClassId]
  have hidemp := UF.findIdempotent eg.uf h ecid
  exact hidemp.symm

omit [DecidableEq D] in
theorem pushEnEqPushCanonEn [Analysis α D] (eg : EGraph α D) (en : ENode α) (h : eg.alwaysInvariants) :
    push eg en = push eg (canonicalise eg en) := by
  unfold push
  simp only
  have pushpush := canonicaliseIdem eg en h.1.2.1
  rw[←pushpush] -- interesting that rw[pushpush] did not work despite them should be equal?

omit [DecidableEq α] [Hashable α] [DecidableEq D] [Inhabited D] in
theorem updateParents_lookup (ecmap : ListMap EClassId (EClass α D)) (en : ENode α) (id k : EClassId) :
    (updateParents ecmap en id).lookup k =
      if k ∈ en.args then
        (ecmap.lookup k).map (updateEClassParents en id)
      else
        ecmap.lookup k
    := by
  unfold updateParents
  simp[ListMap.lookup, ListMap.map]
  induction ecmap.val with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨k', cls⟩
    simp[List.map, List.lookup]
    by_cases eq : k = k'
    ·
      simp[eq]
      -- already equal though, just some (if a else b) and if (some a) else (some b)
      -- cant find a theorem
      by_cases hm : k' ∈ en.args
      <;> simp[hm]
    ·
      have hnq : ¬(k == k') := by simp[eq]
      simp[hnq, ih]



theorem lookupAfterPushECMap [Analysis α D] (eg : EGraph α D) (en : ENode α) (id : EClassId)
    (h : id = eg.uf.push.snd) :
    eg.ecmap.lookup id = (push eg en).fst.ecmap.lookup id := by
  simp[push]
  split
  case h_1 oid ecid hSome =>
    simp
  case h_2 oid hNone =>
    simp[insertECMap]
    simp[ListMap.insert]

    simp[uniqueInsert]

    simp[h]

    simp[ListMap.lookup]




    sorry

omit [DecidableEq D] in
theorem lookupAfterPushECMapNE [Analysis α D] (eg : EGraph α D) (en : ENode α) (id : EClassId)
    (h : ¬id = eg.uf.push.snd) (hnm : id ∉ (canonicalise eg en).args) :
    eg.ecmap.lookup id = (push eg en).fst.ecmap.lookup id := by
  unfold push
  simp
  split
  case h_1 oid ecid hSome =>
    rfl
  case h_2 oid hNone =>
    unfold insertECMap
    simp
    /-
    have aa := ListMap.lookupAfterInsertNE eg.ecmap eg.uf.push.snd (EClass.fromNode (canonicalise eg en)
          (Analysis.make (canonicalise eg en)
            (List.map (fun id => ((ecmapLookup eg id).getD EClass.empty).data) (canonicalise eg en).args))) id h
    -/
    simp[ListMap.lookupAfterInsertNE _ _ _ _ h] -- thanks lean for the inference
    rw[updateParents_lookup]
    simp[hnm]

/-
  Section 1: AlwaysInvariants
-/

/-
  Section 1.1: Push Operation Preserves EGraph alwaysInvariants
  - UF: isValid, isCanon, hasRep, isComplete, uniqueKeys
  - The other EGraph ones, TODO: name them later because I'll keep adding to them
-/
omit [DecidableEq D] in
theorem EGraph.pushPreservesIsValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.isValid := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  -- isValid
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

omit [DecidableEq D] in
theorem EGraph.pushPreservesIsCanon [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.isCanon := by
    have hinvar := h
    unfold EGraph.alwaysInvariants at h
    rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
    rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
    -- isCanon
    -- show that pushing does not change the canonicity of the unionfind
    have isCanon := UF.pushPreservesCanon _ hUfc hUfv
    unfold push
    dsimp
    split
    case h_1 ecId id lookupSome =>
      simp[hUfc]
    case h_2 eid lookupNone =>
      exact isCanon

omit [DecidableEq D] in
theorem EGraph.pushPreservesHasRep [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.hasRep := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  have hasRep := UF.pushPreservesReps eg.uf hR
  unfold push
  dsimp
  split
  case h_1 ecId id lookupSome =>
    simp[hR]
  case h_2 eid lookupNone =>
    exact hasRep

omit [DecidableEq D] in
theorem EGraph.pushPreservesIsComplete [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.isComplete := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  have hComp := UF.pushPreservesComplete eg.uf hinvar.1
  unfold push
  dsimp
  split
  case h_1 ecId id lookupSome =>
    simp[hCmp]
  case h_2 eid lookupNone =>
    simp[hComp]


omit [DecidableEq D] in
theorem EGraph.pushPreservesUniqueKeys [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.uniqueKeys := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  have hPuk := UF.pushPreservesUniqueKeys eg.uf hinvar.1
  unfold push
  dsimp
  split
  case h_1 ecId id lookupSome =>
    simp[hU]
  case h_2 eid lookupNone =>
    simp[hPuk]

omit [DecidableEq D] in
theorem EGraph.pushPreservesWellFormed [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.uf.wellFormed :=
  ⟨
    eg.pushPreservesIsValid h en,
    eg.pushPreservesIsCanon h en,
    eg.pushPreservesHasRep h en,
    eg.pushPreservesIsComplete h en,
    eg.pushPreservesUniqueKeys h en
  ⟩

omit [DecidableEq D] in
theorem EGraph.pushPreservesDirty [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.dirtyValid := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
-- dirtyValid
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

omit [DecidableEq D] in
theorem EGraph.pushPreservesAldrt [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.aldrtValid := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
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

omit [DecidableEq D] in
theorem EGraph.pushPreservesHConsValidity [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.hconsValidity := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  unfold push
  dsimp only
  -- simp[EGraph.hconsValidity] at *
  intro en' id' hex
  split
  case h_1 oid id hSome =>
    simp[hSome] at hex
    simp only
    unfold EGraph.hconsValidity at hhcv
    exact hhcv en' id' hex
  case h_2 oid hNone =>
    simp[hNone] at hex
    simp
    by_cases heq : en' = (canonicalise eg en)
    ·
      subst heq
      have lai := ListMap.lookupAfterInsert eg.hcons (canonicalise eg en) eg.uf.push.snd
      unfold insertHCons at hex
      rw[lai] at hex
      rw[hex] at lai
      injection hex with eq
      rw[←eq]
      have ans := UF.pushReturnsValidID eg.uf
      exact ans
    ·
      have lain := ListMap.lookupAfterInsertNE eg.hcons (canonicalise eg en) eg.uf.push.snd en' heq
      simp[insertHCons] at hex
      rw[lain] at hex
      -- unfold EGraph.hconsValidity at hhcv
      exact UF.pushPreservesValidID eg.uf id' (hhcv en' id' hex)
  /-
    -- en' doesn't exist in hashcons, id' is therefore nonexistent
    -- until we push it in that is
    simp[hNone] at hex
    simp only
    unfold EGraph.hconsValidity at hhcv
    unfold insertHCons at hex -- need a lemma saying lookupAfterInsert returns inserted
    have hex' := eg.hcons.lookupAfterInsert (canonicalise eg en) id'
    -- rw[hex'] at hex
    by_cases heq : en' = (canonicalise eg en)
    case pos =>
      subst heq
      have ans := hhcv (canonicalise eg en) id'
      have fnd := ListMap.lookupAfterInsert eg.hcons (canonicalise eg en) eg.uf.push.snd
      simp[fnd] at hex
      rw[hex] at fnd
      subst hex


      sorry
    case neg =>

      sorry
  -/

omit [DecidableEq D] [Inhabited D] in
theorem updateParentsByCases [Analysis α D] (eg : EGraph α D)
    (en : ENode α) (new_id : EClassId) (id : EClassId) (new_cls : EClass α D) :
    (updateParents eg.ecmap en new_id).lookup id = some new_cls →
    ∃ old_cls, eg.ecmap.lookup id = some old_cls ∧
      ∀ p, p ∈ new_cls.parents → p ∈ old_cls.parents ∨ p = (en, new_id) := by
  intro hlookup
  rw[updateParents_lookup] at hlookup
  by_cases harg : id ∈ en.args
  case pos =>
    simp[harg] at hlookup
    rcases hlookup with ⟨oldCls, hOld, hEq⟩
    exists oldCls
    constructor
    exact hOld
    intro p hp
    rw [← hEq] at hp
    simp [updateEClassParents] at hp
    rcases hp
    case right.inl hp =>
      unfold updateEClassParents at hEq
      rcases hEq with ⟨aaaaa⟩
      right
      exact hp
    ·
      left
      assumption
  ·
    simp[harg] at hlookup
    exists new_cls
    constructor
    exact hlookup
    intro p hp
    left
    exact hp

omit [DecidableEq D] in
theorem EGraph.pushPreservesECMapParentsValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).fst.ecmapParentsValid := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  intro id cls hlookup p pmem
  unfold push
  dsimp
  -- have aa := updateParentsByCases eg en (push eg en).snd id cls
  -- have bb := updateParentsByCases eg (canonicalise eg en) eg.uf.push.snd id cls
  -- have cc := updateParents_lookup eg.ecmap (canonicalise eg en) eg.uf.push.snd id
  -- simp[push] at hlookup

  split
  case h_1 oid eid heq =>
    simp
    simp[push, heq] at hlookup pmem
    exact hepv id cls hlookup p pmem
  case h_2 eid hnq =>
    simp
    simp[push, hnq, insertECMap] at hlookup pmem
    by_cases hideq : id = eg.uf.push.snd
    ·
      rw[hideq] at hlookup
      rw[ListMap.lookupAfterInsert] at hlookup
      rw[Option.some.injEq] at hlookup
      rw[←hlookup] at pmem
      unfold EClass.fromNode at pmem
      simp at pmem
    ·
      simp[ListMap.lookupAfterInsertNE _ _ _ _ hideq] at hlookup
      have upc := updateParentsByCases eg (canonicalise eg en) eg.uf.push.snd id cls hlookup
      rcases upc with ⟨old, hold, hpc⟩
      have pc := hpc p pmem
      cases pc
      case neg.inl h =>
        -- case p was from the old parents
        have oldhepv := hepv id old hold p h
        exact UF.pushPreservesValidID eg.uf p.snd oldhepv
      case neg.inr h =>
        -- case p was a new node (did not exist in parents)
        have hp2 : p.snd = eg.uf.push.snd := by
          rw[h]
        rw[hp2]
        exact UF.pushReturnsValidID eg.uf


  -- do i split here?
  /-
  unfold ecmapParentsValid
  intro id cls lookupSome p pmem
  unfold push
  dsimp
  split
  case h_1 oid ecid hSome =>
    simp
    unfold hcLookup at hSome
    /-
      If you unfold push at lookupSome, you see that node is canonicalised before pushing
      and we see that push also adds it to the hcons
      Therefor (push eg en) adds a canonicalised en (call it c_en) to both hcons and ecmap
      So then we can see that ecmap.lookup returns a class
      and hSome returns an ecid
      so canonical rep of ecls is ecid?
      But that's not what we want

      Try again

      Is this supposed to be an induction proof? no

      idea 1: show that push eg en is equal to push eg (canonicalise eg en)
      then we can rewrite something
      i had this idea in a dream but now i forgot what exactly it was
      also need to show idempotence of canonicalise, lets start with that
      ok

      where was i

      wait do i even need to do this

    -/

    have aa := hhcv p.1 p.snd
    have bb := hepv ecid cls
    sorry
  case h_2 oid hNone =>
    simp

    sorry
  -/
  /-
    idea 2: push doesn't touch parents at all
    try and get that idea through
    idea 2 sucks, it does touch parents
    tip: re-read definitions if you forgot
  -/
  /-
    idea 3: split on something else
    something like
    id_exists_in_parents_already_and_is_updated
    vs
    id_does_not_exist_and_need_to_be_added
    but cannot split on p ∈ cls.parents
    so i guess helper lemma?
  -/


theorem EGraph.unionPreservesECMapParentsValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId) :
    -- (h₁ : eg.uf.isValidID id₁) (h₂ : eg.uf.isValidID id₂) : -- why are h₁ h₂ unused? did i make life difficult?
    (union eg id₁ id₂).fst.ecmapParentsValid := by
  have hinvar := h
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  intro id cls hlookup p pmem

  unfold union
  dsimp

  split
  case isTrue heq =>
    -- no union done
    simp only
    simp[union, heq] at hlookup
    simp[UF.isValid] at hUfv
    simp[ecmapParentsValid] at hepv

    rcases p with ⟨a, b⟩
    simp[hepv id cls hlookup a b pmem]
  case isFalse hnq =>
    simp only
    simp[union, hnq] at hlookup
    simp[UF.union, lookupCanonicalEClassId]
    rw[UF.findIdempotent eg.uf hUfc id₁, UF.findIdempotent eg.uf hUfc id₂]
    rw[←lookupCanonicalEClassId, ←lookupCanonicalEClassId]
    simp[hnq]

    simp[UF.isValidID, UF.size]

    -- ⊢ p.snd < List.length eg.uf, so just need to show p.snd is valid
    -- have test : eg.uf.isValidID p.snd := by sorry

    rw[ecmapParentsValid] at hepv
    /-
    hepv : ∀ (id : EClassId) (cls : EClass α D),
              eg.ecmap.lookup id = some cls →
              ∀ (p : ENode α × EClassId), p ∈ cls.parents →
              eg.uf.isValidID p.snd

    Need: eg.ecmap.lookup id = some cls
    So simplify hlookup as usual
    -/

    /-
    wish this was possible
    let cid₂ := lookupCanonicalEClassId eg id₂
    let cid₁ := lookupCanonicalEClassId eg id₁

    rw[←cid₂, ←cid₁] at hlookup
    -/
    -- this was longer than i expected

    by_cases l₂ : id = (lookupCanonicalEClassId eg id₂)
    ·
      simp[l₂, ListMap.lookupAfterInsert] at hlookup
      simp[EClass.empty] at hlookup
      simp[←hlookup] at pmem
      -- contr.
    ·
      rw[ListMap.lookupAfterInsertNE _ _ _ _ l₂] at hlookup
      rw[lookupCanonicalEClassId, lookupCanonicalEClassId] at hlookup
      rw[unionOfCanonsReturnsFirstArg eg.uf id₁ id₂ hUfc] at hlookup

      by_cases hroot : id = lookupCanonicalEClassId eg id₁
      case pos =>
        simp[hroot, lookupCanonicalEClassId] at hlookup

        simp[ListMap.lookupAfterInsert] at hlookup

        simp[EClass.merge] at hlookup
        rw[←hlookup] at pmem
        simp[List.mem_append] at pmem
        cases pmem
        case inl from1 =>
          have lookup1 : eg.ecmap.lookup (eg.uf.find id₁) = some ((eg.ecmap.lookup (eg.uf.find id₁)).getD EClass.empty) := by
            simp[Option.getD]
            cases h : eg.ecmap.lookup (eg.uf.find id₁) with
            | none =>
              simp[h] at from1
              simp[EClass.empty] at from1
            | some x =>
              simp
          exact hepv (eg.uf.find id₁) _ lookup1 p from1
        case inr from2 =>
          have lookup2 : eg.ecmap.lookup (eg.uf.find id₂) = some ((eg.ecmap.lookup (eg.uf.find id₂)).getD EClass.empty) := by
            simp[Option.getD]
            cases h : eg.ecmap.lookup (eg.uf.find id₂) with
            | none =>
              simp[h] at *
              simp[EClass.empty] at from2
            | some x =>
              simp
          exact hepv _ _ lookup2 _ from2
      case neg =>
        rw[←lookupCanonicalEClassId] at hlookup
        rw[ListMap.lookupAfterInsertNE _ _ _ _ hroot] at hlookup
        exact hepv _ _ hlookup p pmem
      /-
      by_cases hroot : id = ((eg.uf.union (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)).snd)
      case pos =>
        simp[UF.union, lookupCanonicalEClassId] at hroot
        simp[UF.findIdempotent eg.uf hUfc id₁, UF.findIdempotent eg.uf hUfc id₂] at hroot
        rw[←lookupCanonicalEClassId, ←lookupCanonicalEClassId] at hroot
        simp[hnq] at hroot
        simp[hroot] at hlookup



        sorry
      case neg =>

        sorry
      -/





/-
  Yay!
-/

theorem EGraph.pushPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (en : ENode α) :
    (push eg en).1.alwaysInvariants := by
  have hinvar := h
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfWf, hDv, hAv, hHcEm, hhcv, hepv⟩
  rcases hUfWf with ⟨hUfv, hUfc, hR, hCmp, hU⟩
  constructor
  · -- wellformed
    exact eg.pushPreservesWellFormed hinvar en
  constructor
  · -- dirtyValid
    exact eg.pushPreservesDirty hinvar en
  constructor
  · -- aldrtValid
    exact eg.pushPreservesAldrt hinvar en
  constructor
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
  constructor-- hconsToECMap
  ·
    exact eg.pushPreservesHConsValidity hinvar en
  · -- ecmapparentsvalid
    exact eg.pushPreservesECMapParentsValid hinvar en





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

theorem EGraph.unionPreservesisValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.isValid := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
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




theorem EGraph.unionPreservesisCanon [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.isCanon := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  -- isCanon
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

theorem EGraph.unionPreservesHasReps [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.hasRep := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  -- hasRep
  dsimp[union]
  split
  case isTrue aa =>
    simp[hR]
  case isFalse bb =>
    simp only
    have v₁ := UF.findReturnsValid eg.uf hv id₁ h₁
    have v₂ := UF.findReturnsValid eg.uf hv id₂ h₂
    exact UF.unionPreservesReps eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) hwf v₁ v₂

theorem EGraph.unionPreservesisComplete [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.isComplete := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  dsimp[union]
  split
  case isTrue aa =>
    simp[hCmp]
  case isFalse bb =>
    simp only
    exact UF.unionPreservesComplete eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) hwf

theorem EGraph.unionPreservesUniqueKeys [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.uniqueKeys := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  dsimp[union]
  split
  case isTrue aa =>
    simp[hU]
  case isFalse bb =>
    simp only
    exact UF.unionPreservesUniqueKeys eg.uf hU (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)

theorem EGraph.unionPreservesUFWellFormed [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.uf.wellFormed :=
  ⟨
    eg.unionPreservesisValid h id₁ id₂ h₁ h₂,
    eg.unionPreservesisCanon h id₁ id₂ h₁ h₂,
    eg.unionPreservesHasReps h id₁ id₂ h₁ h₂,
    eg.unionPreservesisComplete h id₁ id₂ h₁ h₂,
    eg.unionPreservesUniqueKeys h id₁ id₂ h₁ h₂
  ⟩

theorem EGraph.unionPreservesDirtyValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.dirtyValid := by
  simp[EGraph.dirtyValid]
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
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


theorem EGraph.unionPreservesAldrtValid [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.aldrtValid := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
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

theorem EGraph.unionPreservesHConsValidity [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.hconsValidity := by
  unfold EGraph.alwaysInvariants at h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  simp[EGraph.hconsValidity]
  intro en id lookupIdSome

  simp[union]
  split
  case isTrue h =>
    simp
    exact hhcv en id (lookupBeforeUnionSome eg en id₁ id₂ id lookupIdSome)
  case isFalse h =>
    simp
    have bb := hhcv en id (lookupBeforeUnionSome eg en id₁ id₂ id lookupIdSome)
    have aa := UF.unionPreservesValidID eg.uf (lookupCanonicalEClassId eg id₁)
                (lookupCanonicalEClassId eg id₂) id bb
    exact aa


theorem unionPreservesAlwaysInvariants [Analysis α D] (eg : EGraph α D)
  (h : eg.alwaysInvariants) (id₁ id₂ : EClassId)
    (h₁ : id₁ < eg.uf.size) (h₂ : id₂ < eg.uf.size) :
      (union eg id₁ id₂).1.alwaysInvariants := by
  unfold EGraph.alwaysInvariants
  unfold EGraph.alwaysInvariants at h
  have hinvar := h
  rcases h with ⟨hUfwf, hDv, hAv, hHc, hhcv, hecp⟩
  have hwf := hUfwf
  rcases hUfwf with ⟨hv, hc, hR, hCmp, hU⟩
  constructor
  exact eg.unionPreservesUFWellFormed hinvar id₁ id₂ h₁ h₂
  constructor
  exact eg.unionPreservesDirtyValid hinvar id₁ id₂ h₁ h₂
  repeat constructor
  exact eg.unionPreservesAldrtValid hinvar id₁ id₂ h₁ h₂

  constructor
  · -- hconsToECMap
    sorry
  constructor
  exact eg.unionPreservesHConsValidity hinvar id₁ id₂ h₁ h₂
  exact eg.unionPreservesECMapParentsValid hinvar id₁ id₂

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
