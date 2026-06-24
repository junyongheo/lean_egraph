import Leanegraph.core.SharedDefs

namespace Naive
/-
  Notes: HCons must always be canonical nodes for lookup purposes, scan code for that also TODO:
  Also that the UF always points to canonical values
  Also that the Hcons are unique
  Make them Prop s?
  Many things are unique keys, since they're maps
  Use hcons.insertUnique or something where I define it?
-/
/-
  Basic Union Find, to make it as simple as possible
  Goals: Reasoning...? Provability...? Not-break-my-head-ability? Pure?
  Should not be difficult to swap out later

  Some notes

  1. Every ID must have been pushed before use (doable)
  2. Uf.push must be the only way to add things in (is doable)
  3. Nothing must be removed, ever (see note 1)

  For 2, note that union only updates and doesn't add/remove classes
-/
abbrev UF := List <| EClassId × EClassId

def UF.find (uf : UF) (id : EClassId) : EClassId :=
  uf.lookup id |>.getD id

-- Leader is always id₁
def UF.union (uf : UF)  (id₁ id₂ : EClassId) : UF × EClassId:=
  let leader₁ := uf.find id₁
  let leader₂ := uf.find id₂
  if leader₁ == leader₂ then (uf, leader₁)
  else
  let newUf := uf.map (λ (member, leader) =>
    if leader == leader₂ then (member, leader₁) else (member, leader)
  )
  (newUf, leader₁)

def UF.size (uf : UF) : Nat :=
  uf.length

def UF.push (uf : UF) : UF × EClassId :=
  let newClass := uf.size
  ((newClass, newClass) :: uf, newClass)

-- #eval UF.union (UF.push ([] : UF) |>.1 |> UF.push |>.1 |> UF.push |>.1) 0 2 |>.1

/-
  Theorems, props, invariants, yada₂
-/


-- ID is
def UF.isValidID (uf : UF) (id : EClassId) : Prop :=
  id < uf.size

def UF.isValid (uf : UF) : Prop :=
  ∀ id cid, (id, cid) ∈ uf → uf.isValidID id ∧ uf.isValidID cid

-- because of this, changed def to abbrev
-- alternatively could define membership for uf but this seems easier?
-- TODO: abbrev vs def

-- Every Canonical ID in the UF points to itself
def UF.isCanon (uf : UF) : Prop :=
  ∀ id cid, (id, cid) ∈ uf → uf.find cid = cid



theorem UF.pushIsCanon (uf : UF) :
    let (newUf, newId) := uf.push; newUf.find newId = newId := by
  simp[push, find]

theorem UF.singletonCanon :
    isCanon (UF.push []).fst :=
  by
    simp[push, size]
    simp[isCanon]
    rfl


theorem UF.lookupIsMem
    (uf : UF) (id cid : EClassId) (h : List.lookup id uf = some cid)
      : (id, cid) ∈ uf := by
  induction uf with
  | nil =>
    simp at h
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    by_cases hk : k = id
    ·
      subst hk
      simp[List.lookup] at h
      subst h
      simp
    ·
      simp[List.lookup] at h
      have hk' : k ≠ id := hk
      have hk'' : id ≠ k := by
        intro h
        exact hk h.symm
      have hpleasesimpimbegging : (id == k) = false := by
        simp[hk'']
      simp[hpleasesimpimbegging] at h
      simp[hk'', ih h]



theorem UF.findIdem (uf : UF) (h : uf.isCanon) (id : EClassId) :
    uf.find (uf.find id) = uf.find id := by
  cases hL : List.lookup id uf with
  | none =>
    simp[find]
    simp[hL]
  | some n =>
    have hP : uf.find id = n := by
      simp[find, hL]

    simp[hP]
    /-
      hL : List.lookup id uf = some n
      hP : uf.find id = n
      ⊢ uf.find n = n

      Idea:
        - UF is canon, find/lookup returns some n
        - N is therefore a canonical value
        - Therefore uf.find n should return n
        QED.
        That is proven.
        Goodbye Function.

    -/
    simp[isCanon] at h
    apply h id n
    /-
      New Idea:
        - hP : uf.find id = n -- eigenlijk hL
        - ⊢ (id, n) ∈ uf
        - Show that uf.find id = n → (id, n) ∈ uf
    -/
    exact lookupIsMem uf id n hL



theorem UF.pushPreservesValid (uf : UF) (h : uf.isValid) :
    (uf.push).fst.isValid :=
  by
    unfold isValid
    intro id cid hmem
    constructor
    ·
      simp[push]
      simp[isValidID]
      simp[size]
      rcases hmem
      case left.head       =>
        unfold size
        apply Nat.lt_add_one
      case left.tail hmem' =>
        simp[isValid] at h
        have hValids := h id cid hmem'
        have hIdValid := hValids.left
        simp[isValidID, size] at hIdValid
        -- Ok now id < List.length uf, and id < List.length uf + 1
        -- Surely there's a lemma for this in simp
        -- simpa -- no
        apply Nat.lt_succ_of_lt hIdValid
    ·
      -- the two branches are the same except replace right for left in all, surely there's some sort of automation for this
      simp[push]
      simp[isValidID]
      simp[size]
      rcases hmem
      case right.head       =>
        unfold size
        apply Nat.lt_add_one
      case right.tail hmem' =>
        simp[isValid] at h
        have hValids := h id cid hmem'
        have hIdValid := hValids.right
        simp[isValidID, size] at hIdValid
        -- Ok now id < List.length uf, and id < List.length uf + 1
        -- Surely there's a lemma for this in simp
        -- simpa -- no
        apply Nat.lt_succ_of_lt hIdValid


-- Helper Lemma for the Below
theorem UF.lookingAtTheWrongPlace (id cid : EClassId) (uf : UF) (h : (id, cid) ∈ uf) (hC : uf.isCanon) (hV : uf.isValid)
    : (find ((uf.size, uf.size) :: uf) cid = cid) = (find uf cid = cid) :=
  by
    -- proof_by_obvious
    have hCanon := hC id cid h
    have hIdLt := hV id cid h |> And.right
    simp[isValidID] at hIdLt
    have hne := Nat.ne_of_lt hIdLt

    simp[UF.find, List.lookup]

    /-
      Why in the world does this not match
      hne : cid ≠ uf.size
      ⊢ (match cid == uf.size with
    -/

    -- match h : cid == uf.size with

    have hne' : (cid == uf.size) = false := by
      simp[hne]

    simp[hne']

-- Intuitively, push allocates a new id so shouldn't mess with the
theorem UF.pushPreservesCanon (uf : UF) (hC : uf.isCanon) (hV : uf.isValid):
    (uf.push).fst.isCanon :=
  by
    simp[push]
    unfold isCanon
    intro id cid hmem
    rcases hmem with ⟨hh, ht⟩ -- ok so splitting this with ⟨ ⟩ gives me nice cases
    ·
      simp[size]
      rfl
    case head.cons head tail =>
      simp[find]
    case tail hmem =>
      -- ⊢ find ((uf.size, uf.size) :: uf) cid = cid
      -- But we have hmem : List.Mem (id, cid) uf
      -- In other words uf.size ≠ cid, so we can discard the head, then use hC : uf.isCanon
      -- But how? Helper lemma?

      /-
      induction (uf.size, uf.size) :: uf with -- cool you can induction like this, but this doesn't help
      | nil => rfl
      | cons head tail tail_ih
      -/


      simp[lookingAtTheWrongPlace id cid uf hmem hC hV] -- could be moved here for brevity

      exact hC id cid hmem


    /-
    rcases hmem
    ·
      sorry
    ·
      sorry
    -/



-- theorem UF.unionPreservesCanon (uf : UF) :
    -- uf.isCanon → ∀ id₁ id₂, (uf.union id₁ id₂).fst.isCanon := by
-- Can move all the implications into the named params
-- We would end up doing intro h, intro id₁ id₂ anyway


/-
  For a UF that isCanon, after Union it blijfs canon.
  Idea:

-/
theorem UF.unionPreservesCanon (uf : UF) (h : uf.isCanon) (hV : uf.isValid) (id₁ id₂ : EClassId) :
    (uf.union id₁ id₂).fst.isCanon := by
  unfold isCanon
  intro id cid hmem

  simp[union]
  split
  case isTrue hSameClass =>
    simp -- simp[Prod.fst] -- unfolded fst
    have hFind := h id cid
    -- simp[UF.find]
    /-
      Have: hFind : (id, cid) ∈ uf → uf.find cid = cid
            ⊢ uf.find cid = cid
            hmem : (id, cid) ∈ (uf.union id₁ id₂).fst
            If we can derive (id, cid) ∈ uf, we fine.
            Idea: Since union doesn't add any new id/cid, we should be able to show that
              (id, cid) ∈ (uf.union id₁ id₂).fst    →    (id, cid) ∈ uf

      No scratch that, case isTrue doesn't change UF at all
      Above is valid for isFalse / no it isn't because its a different branch of the code
    -/

    -- have unionNChangeMem : (id, cid) ∈ (uf.union id₁ id₂).fst → (id, cid) ∈ uf := by

    --  sorry

    -- simp[hFind <| unionNChangeMem hmem]

    have noChangeUnion : (uf.union id₁ id₂).fst = uf := by
      simp[UF.union]
      simp[hSameClass]

    simp[noChangeUnion] at hmem
    exact hFind hmem
  case isFalse hNeq =>
    /-
      Situation: id₁ and id₂ were different classes, so they were merged into one.
      Goal: Show that this preserves canonicity
      Intuition: Everything except for the one thing that x.snd = uf.find id₂ is unchanged
      Idea 1: Can we split on the condition?
      Idea 2: Induction on the map? Then split case? -- no, the ind. hyp. is completely off
      Idea 3: Helper Lemma?
    -/
    simp
    unfold find


    sorry





end Naive
