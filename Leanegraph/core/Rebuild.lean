import Leanegraph.core.SharedDefs
import Leanegraph.core.ListAsMaps
import Leanegraph.core.UnionFind
import Leanegraph.core.NaiveDefs
import Leanegraph.core.Naive

variable {α : Type _} [DecidableEq α] [Hashable α] [Repr α]
variable {D : Type _} [DecidableEq D] [Inhabited D]

namespace Naive


omit [Repr α] in -- why tho
theorem unionNoOpPreservesDirty [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId)
  (h : lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂) :
    (union eg id₁ id₂).fst.dirty = eg.dirty ∧ (union eg id₁ id₂).fst.aldrt = eg.aldrt := by
  constructor <;> simp[union, h]

omit [Repr α] in
theorem unionOpReducesClasses [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId)
  (h₁ : eg.uf.isValidID id₁) (h₂ : eg.uf.isValidID id₂) (hWf : eg.uf.wellFormed)
  (h : ¬(lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂)) :
    numCanonClasses (union eg id₁ id₂).fst < numCanonClasses eg := by
  simp[union, h, numCanonClasses]
  have aa := UF.unionPreservesSize eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
  -- simp[UF.union]
  have oh : eg.uf.isCanon := hWf.2.1
  have hCont := UF.findIdempotent eg.uf oh
  simp[lookupCanonicalEClassId] at h
  have v₁ := UF.findReturnsValid eg.uf hWf.1 id₁ h₁
  have v₂ := UF.findReturnsValid eg.uf hWf.1 id₂ h₂
  /-
   ¬eg.uf.find id₁ = eg.uf.find id₂
but is expected to have type
  ¬eg.uf.find (lookupCanonicalEClassId eg id₁) = eg.uf.find (lookupCanonicalEClassId eg id₂)
  -/
  have hidem := (hCont id₁).symm
  have hidem₂ := (hCont id₂).symm
  rw[hidem] at h
  rw[hidem₂] at h
  have uRed := UF.unionReducesNumCanonClasses eg.uf
    (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)
    v₁ v₂ hWf h
  simp[UF.numCanonClasses] at uRed
  simp[uRed]

omit [Repr α] in
theorem unionNoOpPreservesNumClasses [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId)
    (h : lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂) :
      numCanonClasses (union eg id₁ id₂).fst = numCanonClasses eg := by
    simp[union, h]

omit [Repr α] in
theorem unionClassesNeverIncrease [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId)
    (h₁ : eg.uf.isValidID id₁) (h₂ : eg.uf.isValidID id₂) (hWf : eg.uf.wellFormed) :
      numCanonClasses (union eg id₁ id₂).fst ≤ numCanonClasses eg := by
  by_cases h : lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂
  case pos =>
    have eq := unionNoOpPreservesNumClasses eg id₁ id₂ h
    -- simp?[eq]
    rw[eq]
    exact Nat.le_refl (numCanonClasses eg)
    -- maybe "apply Nat.le_refl" is cleaner
  case neg =>
    have leq := unionOpReducesClasses eg id₁ id₂ h₁ h₂ hWf h
    exact Nat.le_of_lt leq
  /-
  split
  case isTrue  h =>
    simp[lookupCanonicalEClassId, hCont id₁, hCont id₂] at h
    contradiction
  case isFalse h =>
    simp only
    simp[lookupCanonicalEClassId, hCont id₁, hCont id₂] at *

    sorry
  -/

omit [Repr α] in
theorem unionOpPreservesUfWf [Analysis α D] (eg : EGraph α D) (id₁ id₂ : EClassId)
  (h₁ : eg.uf.isValidID id₁) (h₂ : eg.uf.isValidID id₂) (hWf : eg.uf.wellFormed) :
    (union eg id₁ id₂).fst.uf.wellFormed := by
  by_cases lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂
  case pos h =>
    simp[union, h]
    exact hWf
  case neg h =>
    simp[union, h]
    have v₁ := UF.findReturnsValid eg.uf hWf.1 id₁ h₁
    have v₂ := UF.findReturnsValid eg.uf hWf.1 id₂ h₂
    exact UF.unionPreservesWellFormed eg.uf hWf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) v₁ v₂

omit [Repr α] in theorem mergeCollisionsNeverIncreaseClasses [Analysis α D] (eg : EGraph α D) (l : List <| EClassId × EClassId)
     (hWf : eg.uf.wellFormed) (hvalid : ∀ p ∈ l, eg.uf.isValidID p.1 ∧ eg.uf.isValidID p.2) :
    numCanonClasses (mergeCollisions eg l) ≤ numCanonClasses eg := by
  induction l generalizing eg with
  | nil =>
    simp[mergeCollisions]
  | cons x xs ih =>
    let (id₁, id₂) := x

    have ⟨h₁, h₂⟩ := hvalid (id₁, id₂) (List.mem_cons_self (a := (id₁, id₂)) (l := xs))
    have hvalid' : ∀ p ∈ xs, eg.uf.isValidID p.1 ∧ eg.uf.isValidID p.2 :=
      fun p hp => hvalid p (List.mem_cons_of_mem _ hp)


    /-
      ∀ (p : EClassId × EClassId), p ∈ xs → eg.uf.isValidID p.fst ∧ eg.uf.isValidID p.snd
      but is expected to have type
      ∀ (p : EClassId × EClassId),
      p ∈ xs → (union eg id₁ id₂).fst.uf.isValidID p.fst ∧ (union eg id₁ id₂).fst.uf.isValidID p.snd
    -/



    by_cases lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂
    case pos h =>
      -- no operation
      simp[mergeCollisions, h]
      exact ih eg hWf hvalid'
    case neg h =>
      -- yes operation

      -- where do we get these? prove that every id in the egraph is valid?
      -- oh it's from dirtyValid, hook that up somehow...
      -- I think we have to move this to a different file then
      -- pass it as parameters now and deal with it at the upper level might be easier
      -- have h₁ : eg.uf.isValidID id₁ := by sorry
      -- have h₂ : eg.uf.isValidID id₂ := by sorry
      have uorc := unionOpReducesClasses eg id₁ id₂ h₁ h₂ hWf h
      have ucni := unionClassesNeverIncrease eg id₁ id₂ h₁ h₂ hWf

      simp[mergeCollisions, h]

      /-
        Application type mismatch: The argument
          ih eg hWf
        has type
          numCanonClasses (mergeCollisions eg xs) ≤ numCanonClasses eg
        but is expected to have type
          numCanonClasses (mergeCollisions (union eg id₁ id₂).fst xs) ≤ numCanonClasses (union eg id₁ id₂).fst
        in the application
          Nat.le_trans (ih eg hWf)
      -/

      have unionStillWellFormed := unionOpPreservesUfWf eg id₁ id₂ h₁ h₂ hWf

      /-
      have m := (ih (union eg id₁ id₂).fst unionStillWellFormed)
      have k := ucni
      have nmk := Nat.le_trans m k
      -/

      have hvalid : ∀ p ∈ xs, eg.uf.isValidID p.1 ∧ eg.uf.isValidID p.2 :=
        fun p hp => hvalid p (List.mem_cons_of_mem _ hp)
      -- might want to extract the union preserves validID into a separate lemma, although I think it was easily derivable so I didn't...
      have hvalid'' : ∀ p ∈ xs, (union eg id₁ id₂).fst.uf.isValidID p.fst ∧ (union eg id₁ id₂).fst.uf.isValidID p.snd := by
        intro p hp

        have ⟨hv1, hv2⟩ := hvalid' p hp
        unfold UF.isValidID at *
        simp at h₁
        simp at h₂

        have aaa := UF.unionPreservesSize eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂)

        rw[←aaa] at hv1
        rw[←aaa] at hv2

        constructor
        ·
          simp[union, h, hv1]
        ·
          simp[union, h, hv2]


      exact Nat.le_trans (ih (union eg id₁ id₂).fst unionStillWellFormed hvalid'') ucni

      /-
      -- this is not true
      have heq : (union eg id₁ id₂).fst = eg := by

        sorry

      rw[heq]
      exact ih eg hWf
      -/

omit [Repr α] in
theorem congruenceRepairFoldNeverIncreases [Analysis α D] (eg : EGraph α D) (todo : List EClassId)
    (hWf : eg.uf.wellFormed) (hvalid : True /- appropriate -/) :
    numCanonClasses (todo.foldl oneStepRepair eg) ≤ numCanonClasses eg := by
  induction todo generalizing eg with
  | nil => simp
  | cons id rest ih =>
    simp only [List.foldl_cons]
    -- oneStepRepair either strictly decreases or holds equal (from oneStepRepairMeasure)
    -- either way, ≤ holds for this step, and ih bounds the rest
    sorry

/-
theorem mergeCollisionsNoOpDirtyStays [Analysis α D] (eg : EGraph α D) (collisions : List (EClassId × EClassId)) :
    (mergeCollisions eg collisions).dirty = eg.dirty := by
  induction collisions with
  | nil =>
    simp[mergeCollisions]
  | cons x xs ih =>
    simp[mergeCollisions]
    split
    case isTrue h  =>
      exact ih
    case isFalse h =>
      simp[union, h]
      -- unreachable case, but how do i put the hypo in the ? i think better to just helper lemma this

      sorry
-/

omit [Repr α] in
theorem unionPreservesAnyValidID_egraph [Analysis α D] (eg : EGraph α D) (id₁ id₂ id : EClassId)
    (hValid : eg.uf.isValidID id) :
    (union eg id₁ id₂).fst.uf.isValidID id := by
  simp[union]
  split
  case isTrue h =>
    simp[hValid]
  case isFalse h =>
    simp only
    exact UF.unionPreservesValidID eg.uf (lookupCanonicalEClassId eg id₁) (lookupCanonicalEClassId eg id₂) id hValid

omit [Repr α] in theorem mergeCollisionsOpAndNoOp [Analysis α D] (collisions : List (EClassId × EClassId)) (eg : EGraph α D) (hwf : eg.uf.wellFormed):
  --(hwf : eg.uf.wellFormed) (hvalid : ∀ p ∈ collisions, eg.uf.isValidID p.1 ∧ eg.uf.isValidID p.2) :
    -- seems to make it more general, hope this won't cause issues...
    (∀ p ∈ collisions, eg.uf.isValidID p.1 ∧ eg.uf.isValidID p.2) →
    -- either the number of canon classes decrease with union (wel-op)
    numCanonClasses (mergeCollisions eg collisions) < numCanonClasses eg ∨
    -- or nothing happens (no union, no dirty emptying, everything the same)
    numCanonClasses (mergeCollisions eg collisions) = numCanonClasses eg ∧
    (mergeCollisions eg collisions).dirty = eg.dirty ∧
    (mergeCollisions eg collisions).aldrt = eg.aldrt := by

  induction collisions generalizing eg with
  | nil =>
    intro hvalidity
    apply Or.intro_right
    constructor <;> simp[mergeCollisions] -- woohoo
    /-
    · -- numcanonclasses
      unfold mergeCollisions
      rfl
    constructor <;> simp[mergeCollisions] -- dirty and aldrt both
    -/
  | cons x xs ih =>
    intro hvalidity
    let (id₁, id₂) := x




    have hvalidhead : eg.uf.isValidID id₁ ∧ eg.uf.isValidID id₂ :=
      hvalidity (id₁, id₂) (List.mem_cons_self (a := (id₁, id₂)) (l := xs))

    -- have xmemlist := List.mem_cons_self (a := (id₁, id₂)) (l := xs)
    -- have theyarevalid : (id₁, id₂) ∈ x :: xs := hvalid' (id₁, id₂) xmemlist
    -- not working



    unfold mergeCollisions
    by_cases heq : lookupCanonicalEClassId eg id₁ = lookupCanonicalEClassId eg id₂
    case pos =>
      -- wait a minute
      /-
      simp[heq]
      simp[heq] at ih
      have unionReasoning := unionNoOpPreservesDirty eg id₁ id₂ heq
      have unionDecrease := unionOpReducesClasses eg id₁ id₂

      -- ih wants     (∀ (a b : EClassId), (a, b) ∈ xs → eg.uf.isValidID a ∧ eg.uf.isValidID b) →
      -- we need ehm
      -/

      -- eq case, no op
      have unionReasoning := unionNoOpPreservesDirty eg id₁ id₂ heq
      have unionPreserves := unionNoOpPreservesNumClasses eg id₁ id₂ heq
      -- have unionDecrease  := unionOpReducesClasses eg id₁ id₂ heq
      have uwf := unionOpPreservesUfWf eg id₁ id₂ hvalidhead.1 hvalidhead.2 hwf -- need: id₁ ₂ isvalid

      simp[heq]
      simp at ih

      -- need (a, b) ∈ (id₁, id₂) :: xs for below
      have memcons := λ p hp => (hvalidity p (List.mem_cons_of_mem _ hp)) -- no idea what went here
      -- need (∀ (a b : EClassId), (a, b) ∈ xs → eg.uf.isValidID a ∧ eg.uf.isValidID b) →
      -- have hvd : ∀ (a b : EClassId), (a, b) ∈ xs → eg.uf.isValidID a ∧ eg.uf.isValidID b := λ a b hm => hvalidity (a, b) (List.mem_cons_self (a := (a, b)) (l := xs))
      have hvd : ∀ (a b : EClassId), (a, b) ∈ xs → eg.uf.isValidID a ∧ eg.uf.isValidID b := λ a b => memcons (a, b) -- huh?
      have ans := ih eg hwf hvd

      exact ans

      /-
      apply Or.intro_right
      constructor
      · -- (x₁, x₂) equal case, so yes op. we show that union decreased classes

        sorry
      · -- no op, then by IH tail holds
        unfold mergeCollisions
      -/
    case neg haermgaelkmtbrlkaetmblaekmtbelkamblkemtablekmtlbkma =>
      simp[heq]
      simp at ih

      have ⟨v₁, v₂⟩ := hvalidity (id₁, id₂) (List.mem_cons_self (a := (id₁, id₂)) (l := xs))

      have uwf := unionOpPreservesUfWf eg id₁ id₂ v₁ v₂ hwf
      have red := unionOpReducesClasses eg id₁ id₂ v₁ v₂ hwf heq
      left


      have hvalid'' : ∀ p ∈ xs, (union eg id₁ id₂).fst.uf.isValidID p.1 ∧ (union eg id₁ id₂).fst.uf.isValidID p.2 := by
        intro p hp
        have ⟨hv1, hv2⟩ := hvalidity p (List.mem_cons_of_mem (id₁, id₂) hp)

        constructor
        · exact unionPreservesAnyValidID_egraph eg id₁ id₂ p.1 hv1
        · exact unionPreservesAnyValidID_egraph eg id₁ id₂ p.2 hv2

      have hmcc := mergeCollisionsNeverIncreaseClasses (union eg id₁ id₂).fst xs uwf hvalid''
      have husc : numCanonClasses (union eg id₁ id₂).fst < numCanonClasses eg := unionOpReducesClasses eg id₁ id₂ v₁ v₂ hwf heq


      exact Nat.lt_of_le_of_lt hmcc husc


omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairLoop1NoTouchClasses (eg : EGraph α D) (ecls : EClass α D) :
    numCanonClasses (repairLoop1 eg ecls).fst = numCanonClasses eg:= by
  simp[numCanonClasses, repairLoop1]

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairNoTouchClasses (eg : EGraph α D) (id : EClassId) :
    numCanonClasses eg = numCanonClasses (repair eg id).fst := by
  simp[repair]
  split
  case h_1 ec none =>
    simp only
  case h_2 ec lSome =>
    simp only
    have r1ntc := repairLoop1NoTouchClasses eg ec
    simp[numCanonClasses] at *
    simp[r1ntc]

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairLoop1NoTouchDirty (eg : EGraph α D) (ecls : EClass α D) :
    (repairLoop1 eg ecls).fst.dirty = eg.dirty := by
  unfold repairLoop1
  simp

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairNoTouchDirty (eg : EGraph α D) (id : EClassId) :
    (repair eg id).fst.dirty = eg.dirty := by
  simp[repair]
  split
  case h_1 =>
    simp
  case h_2 optEc ec lSome =>
    simp only
    exact repairLoop1NoTouchDirty eg ec

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairLoop1NoTouchAldrt (eg : EGraph α D) (ecls : EClass α D) :
    (repairLoop1 eg ecls).fst.aldrt = eg.aldrt := by
  unfold repairLoop1
  simp

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairNoTouchAldrt (eg : EGraph α D) (id : EClassId) :
    (repair eg id).fst.aldrt = eg.aldrt := by
  simp[repair]
  split
  case h_1 =>
    simp
  case h_2 optEc ec lSome =>
    simp only
    exact repairLoop1NoTouchAldrt eg ec

omit [Repr α] [DecidableEq D] [Inhabited D] in
theorem repairNumWorkEq (eg : EGraph α D) (id : EClassId) :
    numWork (repair eg id).fst = numWork eg := by
  have ntd := repairNoTouchDirty eg id
  have nta := repairNoTouchAldrt eg id
  unfold numWork
  simp[ntd, nta]


/-
theorem mergeCollisionsNoTouchDirty [Analysis α D] (eg : EGraph α D) (cols : List (EClassId × EClassId)) :
    (mergeCollisions eg cols).dirty = eg.dirty := by
  unfold mergeCollisions
  split
  case h_1 => rfl
  case h_2 l1 id₁ id₂ l2 =>
    by_cases
    sorry
-/




--theorem repairDoesntTouchAnything [Analysis α D] (eg : EGraph α D)

theorem fold_repairStep_measure [Analysis α D] (l : List EClassId) (acc : EGraph α D)
    (hWf : acc.uf.wellFormed) :
    numCanonClasses (l.foldl oneStepRepair acc) < numCanonClasses acc ∨
    (numCanonClasses (l.foldl oneStepRepair acc) = numCanonClasses acc ∧
     (l.foldl oneStepRepair acc).dirty = acc.dirty ∧
     (l.foldl oneStepRepair acc).aldrt = acc.aldrt) := by
  induction l generalizing acc with
  | nil =>
  /-
    rw[List.foldl_nil]
    simp only
    rw[and_self, and_self]
    right
    simp only
  -/
    simp --?
  | cons x xs ih =>
    simp

    sorry


theorem congruenceRepairMeasure [Analysis α D] (eg : EGraph α D)
    (hWf : eg.uf.wellFormed) (hNotEmpty : ¬eg.dirty.isEmpty) :
    -- makes unions
    numCanonClasses (congruenceRepair eg) < numCanonClasses eg ∨
    -- or cleans dirties
    (
      numCanonClasses (congruenceRepair eg) = numCanonClasses eg ∧
      numWork (congruenceRepair eg) < numWork eg
    )
    := by








  sorry

-- this is incorrect
theorem singleRebuildPassDecreasesWork [Analysis α D] (eg : EGraph α D) :
    numWork (singleRebuildPass eg) < numWork eg := by
  unfold singleRebuildPass
  simp only -- im surprised there isn't a rewriting thing and simp? gives me "simp only"

  sorry

def rebuild [Analysis α D] (eg : EGraph α D) : EGraph α D :=
  if eg.dirty.isEmpty && eg.aldrt.isEmpty then eg
  else
    let eg' := singleRebuildPass eg
    rebuild eg'
termination_by rebuildTerminationBy eg
decreasing_by

  sorry
