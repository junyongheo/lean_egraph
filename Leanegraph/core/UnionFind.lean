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

def changeLeader (uf : UF) (id₁ id₂ : EClassId) (x : EClassId × EClassId) : EClassId × EClassId :=
  if x.snd = uf.find id₂ then (x.fst, uf.find id₁) else (x.fst, x.snd)

-- Leader is always id₁
def UF.union (uf : UF)  (id₁ id₂ : EClassId) : UF × EClassId:=
  let leader₁ := uf.find id₁
  let leader₂ := uf.find id₂
  if leader₁ == leader₂ then (uf, leader₁)
  else
    (uf.map (changeLeader uf id₁ id₂), leader₁)
  /-
  let newUf := uf.map (λ (member, leader) =>
    if leader == leader₂ then (member, leader₁) else (member, leader)
  )
  (newUf, leader₁)
  -/
def UF.size (uf : UF) : Nat :=
  uf.length

def UF.push (uf : UF) : UF × EClassId :=
  let newClass := uf.size
  ((newClass, newClass) :: uf, newClass)

def UF.ufmap (uf : UF) (f : EClassId × EClassId → EClassId × EClassId) := List.map (α := EClassId × EClassId) (β := EClassId × EClassId) f uf

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

def UF.hasRep (uf : UF) : Prop :=
  ∀ id cid, (id, cid) ∈ uf → (cid, cid) ∈ uf

def UF.isComplete (uf : UF) : Prop :=
  ∀ id, id < uf.size → ∃ cid, (id, cid) ∈ uf
/- not working
def UF.correct (uf : UF): Prop :=
  ∀ id cid, (id, cid) ∈ uf → uf.find id = cid
-/
/-
def UF.everyKeyPresent' (uf : UF) : Prop :=
  ∀ id, uf.isValidID id → (id, uf.find id) ∈ uf
-/
def UF.uniqueKeys (uf : UF) : Prop :=
  List.Nodup (uf.map Prod.fst)

def UF.wellFormed (uf : UF) : Prop :=
  uf.isValid ∧ uf.isCanon ∧ uf.hasRep ∧ uf.isComplete ∧ uf.uniqueKeys




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
      -- Surely there's a better way to do this
      have hk' : k ≠ id := hk
      have hk'' : id ≠ k := by
        intro h
        exact hk h.symm
      have hpleasesimpimbegging : (id == k) = false := by
        simp[hk'']
      simp[hpleasesimpimbegging] at h
      simp[hk'', ih h]
/-
-- Is Not?
theorem UF.findIsMem
    (uf : UF) (id cid : EClassId) (h : uf.find id = some cid)
      : (id, cid) ∈ uf := by
  induction uf with
  | nil =>
    simp at h
-/

theorem UF.memLookup (uf : UF) (id cid : EClassId) (hU : uf.uniqueKeys) (hMem : (id, cid) ∈ uf) :
    List.lookup id uf = some cid := by
  induction uf with
  | nil =>
    contradiction
  | cons x tail ih =>
    rcases x with ⟨k, v⟩

    simp [uniqueKeys] at hU
    rcases hU with ⟨hnotmemtail, hnoduptail⟩

    rcases List.mem_cons.mp hMem with hInhead | hIntail
    ·
      injection hInhead with hidk hcidv
      subst hidk hcidv
      simp [List.lookup]

    ·
      have ht : id ∈ tail.map Prod.fst := List.mem_map_of_mem hIntail

      have hneq : id ≠ k := by
        intro h_eq
        subst h_eq
        have hcont := hnotmemtail cid
        contradiction


      have pls : (id == k) = false := by
        simp [hneq]

      simp [List.lookup, pls]

      exact ih hnoduptail hIntail



theorem UF.everyKeyPresent (uf : UF) (h : uf.wellFormed) :
    ∀id, uf.isValidID id → (id, uf.find id) ∈ uf := by
  intro id h₁
  rcases h with ⟨hv,hc, hr, hcmp, hu⟩

  have hCanon := hcmp id  h₁

  rcases hCanon with ⟨cid, hmem⟩

  have exsts := memLookup uf id cid hu hmem

  simp[find, exsts, hmem]

/-
TODO: unneeded with new changes? check and delete.
theorem UF.correctness (uf : UF) (id cid : EClassId) (hU : uf.uniqueKeys) (hmem : (id,cid) ∈ uf) :
    uf.find id = cid := by
  have ok := memLookup uf id cid hU hmem
  simp[find, ok]

theorem UF.completeFindMem (uf : UF) (id : EClassId) (hC : uf.isComplete)
    (hU : uf.uniqueKeys) (hid : uf.isValidID id) :
      (id, uf.find id) ∈ uf := by
  simp[isComplete] at hC
  simp[uniqueKeys] at hU
  simp[isValidID] at hid

  have hcidex := hC id hid
  rcases hcidex with ⟨cid, hmem⟩

  have aaa := correctness uf id cid hU hmem
  simpa[aaa] using hmem
-/


-- Helper theorem for union preserves canon proof
-- Map then Lookup == Lookup then Map
theorem UF.lookupMap (uf : UF) (k leader₁ leader₂ : EClassId) :
    (uf.map (fun p => if p.2 == leader₂ then (p.1, leader₁) else p)).lookup k
    = (uf.lookup k).map (fun l => if l == leader₂ then leader₁ else l) := by
  induction uf with
  | nil => simp
  | cons head rest ih =>
    rcases head with ⟨m,l⟩
    simp [List.map, List.lookup]
    by_cases hm : k == m
    case pos =>
      simp[hm]
      -- WHAT A FANCY MOVE
      by_cases hl : l = leader₂ <;> simp[hl, hm]
    case neg =>
      have hnm : (k == m) = false := by simp[hm]
      by_cases hl : l = leader₂
      -- i would do the <;> again if only i could figure out how to do multiple
      case pos =>
        simp[hl]
        simp[hnm]
        simp at ih
        exact ih
      case neg =>
        simp[hl]
        simp[hm]
        simpa using ih


theorem UF.findIdempotent (uf : UF) (h : uf.isCanon) (id : EClassId) :
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

theorem UF.findReturnsValid (uf : UF) (h : uf.isValid) (id : EClassId)
    (hID : uf.isValidID id) : uf.find id < uf.size := by
  unfold UF.find
  cases hOpt : List.lookup id uf with
  | none =>
    simp[isValidID] at hID
    simp[hID]
  | some val =>
    simp
    simp[isValidID] at hID
    have hmem := lookupIsMem uf id val hOpt
    simp[isValid] at h
    rcases h id val hmem with ⟨_, ans⟩
    exact ans

theorem UF.unionPreservesSize (uf : UF) (id₁ id₂ : EClassId):
    (uf.union id₁ id₂).fst.size = uf.size := by
  unfold union
  simp
  split
  case isTrue eq =>
    simp only -- but where
  case isFalse nEq =>
    rw[UF.size]
    rw[List.length_map]
    rw[UF.size]
    -- thanks simp?

theorem UF.unionLeaderValid (uf : UF) (id₁ id₂ : EClassId)
  (h₁ : id₁ < uf.size) (_ : id₂ < uf.size) (hValid : uf.isValid) :
    (uf.union id₁ id₂).snd < uf.size := by
  simp[union]
  have v₁ := UF.findReturnsValid uf hValid id₁ h₁
  split
  case isTrue h =>
    -- have v₂ := UF.findReturnsValid uf hValid id₂ h₂
    exact v₁
  case isFalse h =>
    exact v₁



theorem UF.pushPreservesUniqueKeys (uf : UF) (hWf : uf.wellFormed) :
    (uf.push).fst.uniqueKeys := by
  unfold push
  rcases hWf with ⟨rv, rcn, rr, rcm, hU⟩
  simp
  simp[uniqueKeys] at hU
  simp[uniqueKeys]
  constructor
  ·
    intro random hex
    unfold isValid at rv
    have ⟨hsv, hrv⟩ := rv (uf.size) random hex
    simp[isValidID] at hsv
  ·
    exact hU

theorem UF.unionPreservesUniqueKeys (uf : UF) (hU : uf.uniqueKeys)
  (id₁ id₂ : EClassId) :
    (uf.union id₁ id₂).fst.uniqueKeys := by
  simp[union]
  unfold changeLeader
  split
  case isTrue h =>
    simp[hU]
  case isFalse h =>
    simp
    unfold uniqueKeys at *
    simp [List.map_map]
    have h_eq : (Prod.fst ∘ fun (x : EClassId × EClassId) => if x.snd = uf.find id₂ then (x.fst, uf.find id₁) else (x.fst, x.snd)) = Prod.fst := by
      ext x
      simp[Function.comp]
      split
      simp
      simp
    rw[h_eq]
    assumption

-- theorem UF.newlyPushedIsMem
/-
theorem UF.pushPreservesCorrect (uf : UF)
    (rv : uf.isValid) (rcr : uf.correct) :
      (uf.push).fst.correct := by
  unfold push
  simp only [correct]
  intro id cid hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with hn | ho
  ·
    rcases hn
    simp[find]
  ·
    have hneq : id ≠ uf.size := by
      intro heq
      have hid := (rv id cid ho).1
      rw[isValidID, heq] at hid
      -- without simp you would do this, thanks simp?
      -- Nat.lt_irrefl (n : Nat) : ¬n < n
      apply Nat.lt_irrefl uf.size
      apply hid

    have hneq' : (id == uf.size) = false := by
      simp[hneq]
    simp[find, List.lookup, hneq']
    have aaa := rcr id cid ho
    -- simp[find] at aaa
    -- exact aaa
    simpa[find] using aaa
-/
/-
theorem UF.unionPreservesCorrect (uf : UF) (id₁ id₂ : EClassId) (h : uf.wellFormed) :
    (uf.union id₁ id₂).fst.correct := by
  simp[union]
  split
  case isTrue  heq =>
    simp
    exact h.2.2.2.2 -- hehe
  case isFalse hnq =>
  /-
    simp[correct]
    intro id cid a b hmem hbr
    by_cases b = uf.find id₂
    case pos heq =>
      simp[heq] at hbr
      rcases hbr with ⟨ha, uf2⟩
      subst heq
      rw[ha] at hmem -- why didn't this rw with subst?


      sorry
    case neg hnq =>
      simp[hnq] at hbr
      rcases hbr with ⟨ha, hb⟩
      rw[ha, hb] at hmem
      rw[hb] at hnq
      simp[find]




      sorry
  -/
  unfold correct
  intro id cid hmem
  have hCorrect := h.2.2.2.2
  have hCanon   := h.2.1
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨⟨oldId, oldCid⟩, hold, hEq⟩
  simp at hEq
  simp only
  by_cases hc : oldCid == uf.find id₂
  ·
    sorry
  ·
    have hBr : (oldCid = uf.find id₂) = false := by
      simp[hc]
      intro c
      simp[c] at hc
    simp at hBr
    -- simp[hBr] at hEq

    have holdCorrect : uf.find oldId = oldCid :=
        hCorrect oldId oldCid hold




    sorry

-/


theorem UF.pushPreservesComplete (uf : UF) (h : uf.wellFormed) :
    (uf.push).fst.isComplete := by
  unfold isComplete
  rcases h with ⟨rv, rcn, rr, rcm, _⟩
  simp[push]
  intro id size
  simp[UF.isComplete] at rcm
  simp[UF.size] at *
  simp[UF.isValid] at rv
  simp[UF.hasRep] at rr
  simp[UF.isCanon] at rcn
  have aa := rcm id
  by_cases h_lt : id < List.length uf
  ·
    rcases aa h_lt with ⟨cid, hcid_mem⟩
    exists cid
    exact Or.inr hcid_mem
  ·
    have h_eq : id = List.length uf := by omega
    exists id
    constructor
    constructor
    exact h_eq
    exact h_eq
    -- i have no idea why constructor removed a goal and why the second constructor opened two identical goals

theorem UF.unionPreservesComplete (uf : UF) (id₁ id₂ : EClassId) (h : uf.wellFormed) :
    (union uf id₁ id₂).fst.isComplete := by
  unfold isComplete
  rcases h with ⟨rv, rcn, rr, rcm, _⟩
  intro id hvalidBefore
  simp[union]
  unfold changeLeader
  split
  case isTrue heq =>
    simp
    simp[isComplete] at rcm
    have bb := unionPreservesSize uf id₁ id₂
    simp[bb] at hvalidBefore
    exact rcm id hvalidBefore
  case isFalse hnq =>
    simp
    simp[UF.isComplete] at rcm
    simp[UF.isValid] at rv
    simp[UF.hasRep] at rr
    simp[UF.isCanon] at rcn
    have bb := unionPreservesSize uf id₁ id₂
    simp[bb] at hvalidBefore

    rcases rcm id hvalidBefore with ⟨hid, hmem⟩

    by_cases h : hid = uf.find id₂
    ·
      exists uf.find id₁
      exists id
      exists hid
      simp[h]
      rw[←h]
      exact hmem
    ·
      exists hid
      exists id
      exists hid
      simp[h]
      exact hmem

/-
theorem UF.pushPreservesEveryKeyPresent (uf : UF) (h : uf.wellFormed) :
    (uf.push).fst.everyKeyPresent := by
  simp[everyKeyPresent, push]
  intro id hv
  simp [UF.isValidID, UF.size] at hv
  by_cases heq : id = uf.size
  ·
    simp[heq, UF.find]

  ·
    -- id < uf.size + 1
    -- id ≠ uf.size
    -- thus id < uf.size
    -- PROOF BY !!!OBVIOUS!!! LEAN
    have hids : id < uf.size := by
      simp[UF.size] at *
      have hle : id ≤ List.length uf := Nat.lt_succ_iff.mp hv
      exact Nat.lt_of_le_of_ne hle heq

    have hidAtOld := h.2.2.2.2.1 id hids
    have hFoundAtOld : UF.find (((uf.size, uf.size) :: uf) : UF) id = uf.find id := by
      have pls : ¬(id == uf.size) := by
        simp[heq]
      simp[UF.find, List.lookup, pls]
    rw[hFoundAtOld]
    exact Or.inr hidAtOld
-/
    /-
      heq : ¬id = uf.size
      hids : id < uf.size
      hmem_old : (id, uf.find id) ∈ uf
      ⊢ (id, find ((uf.size, uf.size) :: uf) id) ∈ uf

    -/




  /-
  constructor
  constructor
  ·
    simp[isValidID, size] at hv
    simp[size]

    sorry
  ·
    sorry
  -/

theorem changeLeaderPreservesFst (uf : UF) (id₁ id₂ : EClassId) (x : EClassId × EClassId) :
    (changeLeader uf id₁ id₂ x).fst = x.fst := by
  unfold changeLeader
  split
  simp
  simp

theorem unionPreservesFst (uf : UF) (id₁ id₂ : EClassId) :
    List.map Prod.fst (uf.union id₁ id₂).fst = List.map Prod.fst uf := by
  simp[UF.union]
  split
  case isTrue h =>
    simp
  case isFalse h =>
    simp
    intro a b hmem
    have rw := changeLeaderPreservesFst uf id₁ id₂ (a,b)
    simp[rw]

/-
  EveryKeyPresent
-/
/-
theorem UF.unionPreservesEveryKeyPresent (uf : UF) (id₁ id₂ : EClassId)
  (h₁ : uf.isValidID id₁) (h₂ : uf.isValidID id₂) (h : uf.wellFormed) :
    (uf.union id₁ id₂).fst.everyKeyPresent := by
  /-
    Every key present says that all valid IDs have an entry in the UF (as .fst)
    Union does not touch .fst at all
  -/
  rw[union]
  unfold everyKeyPresent
  intro id hIdv
  split
  case isTrue heq =>
    simp[heq] at hIdv
    simp
    exact h.2.2.2.2.1 id hIdv
  case isFalse hnq =>
    simp only
    simp[hnq] at hIdv

    have hIdV' : uf.isValidID id := by
      have hsize := UF.unionPreservesSize uf id₁ id₂
      simp[UF.isValidID] at hIdv
      simp[UF.union, hnq] at hsize
      rw[hsize] at hIdv
      exact hIdv

    have hidmem := h.2.2.2.2.1 id hIdV'

    have hmem_new : changeLeader uf id₁ id₂ (id, uf.find id) ∈ uf.map (changeLeader uf id₁ id₂) :=
      List.mem_map_of_mem (l := uf) (h := hidmem)

    have hfst := changeLeaderPreservesFst uf id₁ id₂ (id, uf.find id)


    /-
      f (a, canon a) = (a, canon (map f a))
    -/

    -- have eq : changeLeader uf id₁ id₂ (id, uf.find id) = (id, find (List.map (changeLeader uf id₁ id₂) uf) id) := by
      --simp[changeLeader]
    have eq : changeLeader uf id₁ id₂ (id, uf.find id) = (id, find (uf.map (changeLeader uf id₁ id₂)) id) := by
      unfold changeLeader find
      simp[lookupMap2]
      simp[Option.map]

      sorry

    rw[←eq]

    exact hmem_new
-/

  /-
  simp[union]
  split
  case isTrue heq  =>
    simp
    exact h
  case isFalse hnq =>
    induction uf with
    | nil =>
      simp[everyKeyPresent]
      intro id isValid
      simp[isValidID, size] at isValid
    | cons x xs ih =>


      sorry
  -/
  /-
  simp[everyKeyPresent, union]
  intro id hmem
  by_cases uf.find id₁ = uf.find id₂
  case pos heq =>

    simp[heq]
    simp[heq] at hmem
    have hmemcanon := findReturnsValid uf h.1 id hmem
    -- have isComp := h.2.2.2.1
    rw[←isValidID] at hmemcanon
    have mem := h.2.2.2.1 id hmem

    sorry
  case neg hneq =>
    simp[hneq]
    simp[hneq] at hmem
    simp[changeLeader]
    exists id₁
    exists (uf.find id₁)
    constructor
    ·
      sorry
    ·
      simp[hneq]

      sorry
  -/


theorem UF.pushPreservesReps (uf : UF) (h : uf.hasRep) :
    (uf.push).fst.hasRep := by
  unfold hasRep
  intro id cid mem
  simp[push] at *
  unfold hasRep at h
  rcases mem with ⟨hid, hcid⟩
  exact Or.inl hcid
  case inr hy =>
    exact Or.inr (h id cid hy)

theorem UF.unionPreservesReps (uf : UF) (id₁ id₂ : EClassId) (h : uf.wellFormed) (h₁ : UF.isValidID uf id₁) (_ : UF.isValidID uf id₂):
    (uf.union id₁ id₂).fst.hasRep := by
  unfold hasRep at *
  intro id cid hmem

  rcases h with ⟨hc, hv, hr, hcm, hcrr⟩
  have hwf : uf.wellFormed := ⟨hc, hv, hr, hcm, hcrr⟩
  simp[union]
  have aa := hr id cid

  simp[union] at hmem
  unfold changeLeader



  simp[isComplete] at hcm


  split at hmem
  case isTrue  hEq =>
    simp at hmem
    simp[hEq]
    exact aa hmem
  case isFalse hNq =>
    simp at hmem
    simp[hNq]
    rcases hmem with ⟨a, b, hmem, heq⟩
    simp[changeLeader] at heq
    by_cases hb : b = uf.find id₂
    ·
      simp[hb] at heq
      rcases heq with ⟨haid, hcid₁cid⟩ -- what a name

      simp[UF.isValidID] at *
      simp[UF.isValid] at hc


      exists cid
      exists cid

      simp[]
      constructor
      ·

        rcases hcm id₁ h₁ with ⟨cid₁, hex⟩
        have hCans := hv id₁ cid₁ hex
        have hReps := hr id₁ cid₁ hex
        have hVald := hc (uf.find id₁) (uf.find id₂)




        rw[haid] at hmem
        rw[hb] at hmem

        -- subst hb haid
        -- subst hcid₁cid

        unfold isCanon at hv
        unfold hasRep at hr

        subst hcid₁cid


        have ok := everyKeyPresent uf hwf id₁ h₁

        have ok' := hv id₁ cid₁ hex
        rw[←ok'] at hReps

        have bb := hr id₁ (uf.find id₁) ok
        exact bb
        -- get better names...

      ·
        intro _
        assumption
    ·
      simp [hb] at heq
      rcases heq with ⟨haid, hbcid⟩
      subst haid hbcid
      refine ⟨b, b, aa ?_, ?_⟩
      · exact hmem
      · simp[hb]

  /-

  split

  case isTrue  hEq =>

    sorry
  case isFalse hNq =>
    simp
    simp[union, hNq] at hmem
    rcases hmem with ⟨a, b, c, d⟩

    have hAb :=

    constructor
    ·
      simp[union, hNq] at hmem

      simp[hmem]
      sorry
    ·
      sorry
    -/

theorem uniqueKeyValue {k v₁ v₂ : EClassId}
  (uf : UF) (h : uf.uniqueKeys) (h₁ : (k,v₁) ∈ uf) (h₂ : (k,v₂) ∈ uf) :
    v₁ = v₂ := by
  induction uf with
  | nil =>
      cases h₁
  | cons el uf ih =>
      simp[UF.uniqueKeys] at h
      rcases h with ⟨hel, hnodup⟩
      simp at h₁
      simp at h₂
      rcases h₁ with helf | h₁
      subst helf
      · rcases h₂ with heq | h₂
        ·
          cases heq
          rfl
        ·
          exfalso
          apply hel
          ·
            simp
            apply h₂
      ·
        rcases h₂ with hels | h₂
        ·
          exfalso
          apply hel
          subst hels
          simp
          apply h₁
        ·
          exact ih hnodup h₁ h₂



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
/-
theorem UF.unionPreservesCanonFailed (uf : UF) (h : uf.isCanon) (hV : uf.isValid) (id₁ id₂ : EClassId) :
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
    -/
    simp [UF.union] at hmem
    simp [hNeq] at hmem

    rcases List.mem_map.mp hmem with ⟨p, hp, rfl⟩

    rcases p with ⟨id', cid'⟩

    by_cases hcid : cid' == uf.find id₂


    sorry
-/

theorem UF.unionPreservesValidID (uf : UF) (id₁ id₂ id : EClassId)
    (hValid : uf.isValidID id) :
    (uf.union id₁ id₂).fst.isValidID id := by
  unfold UF.isValidID at *
  rw [UF.unionPreservesSize uf id₁ id₂]
  exact hValid

/-
  TOOD: Protip: if you're proving theorems at 2am then please document your thoughts
  because I cannot remember what I was thinking
  It works though? Forget about it
-/
theorem UF.unionPreservesValid (uf : UF) (h : uf.isValid) (id₁ id₂ : EClassId)
    (h₁ : uf.isValidID id₁) -- (_ : uf.isValidID id₂)
    : (uf.union id₁ id₂).fst.isValid := by
  unfold isValid union changeLeader
  simp
  intro id cid hmem
  by_cases hSame : uf.find id₁ = uf.find id₂
  ·
    simp[hSame] at *
    simp[isValid] at h
    exact h id cid hmem
  ·
    simp[hSame] at hmem
    rcases hmem with ⟨a, b, hmem, ok⟩
    simp[isValid] at h
    have hValids := h id cid
    have ⟨aVal, bVal⟩  := h a b hmem
    by_cases hrewr : b = uf.find id₂
    ·
      simp[hrewr] at ok
      rcases ok with ⟨aEq, hCid⟩
      simp[hSame]
      rw[←hrewr, ←aEq]
      simp[isValidID] at *
      simp[UF.size] at *
      rw[aEq]
      constructor
      ·
        simp[←aEq, aVal]
      ·
        simp[←hCid]
        have ans := findReturnsValid uf h id₁ h₁
        simp[UF.size] at ans
        assumption
    ·
      simp[hrewr] at ok
      rcases ok with ⟨hId, hcid⟩
      simp[hSame]
      simp[isValidID, UF.size]
      have what := h a b hmem
      simp[hId, hcid, isValidID, UF.size] at what
      assumption

    /-
    constructor
    ·
      simp[hSame]
      simp[isValidID]

      have


      sorry
    ·
      simp[hSame]
      simp[find, isValidID]
      sorry
    -/

theorem UF.unionPreservesCanon (uf : UF) (h : uf.isCanon) (id₁ id₂ : EClassId)
    : (uf.union id₁ id₂).fst.isCanon := by
  unfold isCanon union
  intro id cid hmem
  by_cases hSame : (uf.find id₁ == uf.find id₂)
  · -- IDs already same class, no change
    simp at hSame
    simp[isCanon] at h
    simp[hSame] at hmem
    simp[hSame]
    have hcanon := h id cid hmem
    exact hcanon
  · -- Diff classes, change does happen
    simp[hSame]
    simp[hSame] at hmem
    simp[isCanon] at h
    simp[find]
    unfold changeLeader at *
    rw[←UF.find]
    -- SOMEDAY: figure out how to rewrite a specific instance
    rw[find]
    -- map commute(?)
    have hcomm := lookupMap uf cid (uf.find id₁) (uf.find id₂)
    simp at hcomm
    simp[hcomm]

    rcases hmem with ⟨a, b, habmem, hb⟩

    by_cases hrewr : b = uf.find id₂
    case pos =>
      simp[hrewr] at hb
      rcases hb with ⟨haid, h1cid⟩

      -- split again on lookup of option
      cases hLookup : List.lookup cid uf with
      | none =>
        simp
      | some val =>
        simp

        have hNeq : uf.find id₂ ≠ cid := by
          intro heq
          /-
          have hidsameclass : uf.find id₁ = uf.find id₂ := by
            simp[h1cid, heq]
          simp[hidsameclass] at hSame
          -/
          simp[h1cid, heq] at hSame

        -- canon of cid is val
        -- canon of id₁ is cid
        -- therefore cid = val?
        -- also id₂ ≠ cid so ifte branch can be simplified
        have hCidCanon : uf.find cid = cid := by
          rw[←h1cid]
          apply findIdempotent uf h id₁

        have hvec : val = cid := by
          rw[←hCidCanon]
          unfold find
          simp[hLookup]

        simp[hvec]
        simp[hNeq.symm]

    case neg =>
      simp[hrewr] at hb
      rcases hb with ⟨haid, hbcid⟩
      simp[haid, hbcid] at habmem
      have cidcanon := h id cid habmem
      simp[haid, hbcid] at *
      -- WHAT???
      cases hLookup : List.lookup cid uf with
      | none =>
        simp
      | some val =>

        have hvec : val = cid := by
          rw[←cidcanon]
          unfold find
          simp[hLookup]

        simp [hvec, hrewr]


def UF.numCanonClasses (uf : UF) : Nat :=
  uf.filter (λ (id, cid) => id == cid) |>.length

/-
theorem UF.unionReturnsMem (uf : UF) (id₁ id₂ : EClassId) :
    (id₂, id₁) ∈ (uf.union id₁ id₂).fst := by
  simp[union]
  split
  case isTrue h =>
    simp

  sorry
-/


def canon (x : EClassId × EClassId) : Bool :=
  x.1 == x.2

-- no canon can magically turn into a new canon
theorem ifCanonAlrCanon (uf : UF) (id₁ id₂ : EClassId)
    (hWf : uf.wellFormed)
    (h : uf.uniqueKeys)
    (hOp : uf.find id₁ ≠ uf.find id₂)
    (h₁ : uf.isValidID id₁)
    (x : EClassId × EClassId) (hx : x ∈ uf) :
    (changeLeader uf id₁ id₂ x).fst == (changeLeader uf id₁ id₂ x).snd →
    x.fst == x.snd := by
  intro hself
  have hWf := hWf
  rcases hWf with ⟨hv, _, hr, _, _⟩
  unfold changeLeader at hself
  by_cases hcond : x.snd = uf.find id₂
  ·
    simp [hcond] at hself
    exfalso
    -- i don't know why that was so difficult to do? lean??
    have xIs : (uf.find id₁, uf.find id₂) ∈ uf := by
      have ok : (x.fst, x.snd) = x := by
        rfl
      rw[hself, hcond] at ok
      rw[←ok] at hx
      exact hx
    have hkp := UF.everyKeyPresent uf hWf
    have hrep := hr id₁ (uf.find id₁) (hkp id₁ h₁)

    have hcontr := uniqueKeyValue uf h xIs hrep
    exact hOp (hcontr.symm)
  · simp [hcond] at hself
    simp[hself]

theorem mapFilterMustLEq {α : Type _} (l : List α) (f : α → α) (p : α → Bool)
    (hff : ∀ x ∈ l, p (f x) = true → p x = true) :
    ((l.map f).filter p).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    have iharg : ∀ x ∈ xs, p (f x) = true → p x = true :=
      fun a ha => hff a (List.mem_cons_of_mem x ha)
    have ha := ih iharg
    cases hf : p (f x)
    ·
      cases ht : p x
      ·
        simp
        exact ha
      ·
        simp
        have ns := Nat.le_succ_of_le ha
        exact ns
    ·
      have ht_true := hff x List.mem_cons_self hf
      simp [ht_true]
      exact ha


theorem mapFilterMustSmaller {α : Type _} (l : List α) (f : α → α) (p : α → Bool) (el : α)
    (htmem : el ∈ l) (helt : p el = true) (hpelf : p (f el) = false)
      (hff : ∀ x ∈ l, p (f x) = true → p x = true) :
        ((l.map f).filter p).length < (l.filter p).length := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.map_cons, List.filter_cons]
    have htnon : ∀ x ∈ tl, p (f x) = true → p x = true :=
      fun x hx => hff x (List.mem_cons_of_mem hd hx)

    -- was head eq split
    by_cases heq : hd = el
    ·
      rw [heq]
      simp [helt, hpelf]
      have h_le := mapFilterMustLEq tl f p htnon
      omega
    ·
      have htmem_tl : el ∈ tl := by
        rcases List.mem_cons.mp htmem with h_hd | h_tl
        ·
          have h_nd := h_hd.symm
          contradiction
        ·
          exact h_tl

      have h_ih := ih htmem_tl htnon

      cases hf : p (f hd)
      ·
        cases ht : p hd
        ·
          simp
          omega
        ·
          simp
          omega
      ·
        have ht_true := hff hd List.mem_cons_self hf
        simp [ht_true]
        omega


theorem UF.unionReducesNumCanonClasses (uf : UF) (id₁ id₂ : EClassId)
  (h₁ : uf.isValidID id₁) (h₂ : uf.isValidID id₂)
  (hWf : uf.wellFormed) (hOp : ¬(uf.find id₁ = uf.find id₂)) :
    numCanonClasses (uf.union id₁ id₂).fst < numCanonClasses uf := by

  rcases hWf with ⟨hv, hc, hrep, hcomp, hu⟩
  have hWf : uf.wellFormed := ⟨hv, hc, hrep, hcomp, hu⟩
  have hep := everyKeyPresent uf hWf
  simp [union, numCanonClasses, hOp]

  -- readability..
  let f := fun x => changeLeader uf id₁ id₂ x
  let p := fun (x : EClassId × EClassId) => x.fst == x.snd
  change ((uf.map f).filter p).length < (uf.filter p).length

  apply mapFilterMustSmaller uf f p (uf.find id₂, uf.find id₂)
  · exact hrep id₂ (uf.find id₂) (hep id₂ h₂)
  · simp[p]
  ·
    simp[f, p, changeLeader]
    intro heq
    have heq := heq.symm
    contradiction
  ·
    intro x hmem hmt
    have px := ifCanonAlrCanon uf id₁ id₂ ⟨hv, hc, hrep, hcomp, hu⟩ hu hOp h₁ x hmem hmt
    exact px


/-

/-
  have hPr := unionPreservesReps uf id₁ id₂ hWf h₁ h₂ hWf.2.2.2.2
  unfold hasRep at hPr
  simp[union, hOp, numCanonClasses]
  have hex := hWf.2.2.1 id₂ (uf.find id₂) (hWf.2.2.2.2 id₂ h₂)

  rcases List.append_of_mem hex with ⟨before, after, hit⟩

  rw[hit]
-/
  /-
    At this point we have
    hex (hExists a class that fits the filter) : (uf.find id₂, uf.find id₂) ∈ uf
    and goal
    (List.filter (fun x => x.fst == x.snd)
          (List.map (fun x => if x.snd = uf.find id₂ then (x.fst, uf.find id₁) else (x.fst, x.snd)) uf)).length <
      (List.filter (fun x => x.fst == x.snd) uf).length

    where List.filter (fun x => x.fst == x.snd) uf).length means
      the number of pairs who have equal parts(?)

    1) List.map (fun x => if x.snd = uf.find id₂ then (x.fst, uf.find id₁) else ... uf
            <
    2) Standard UF

    Where 1) has one item hit correctly because we have (uf.find id₂, uf.find id₂)
    which becomes
    (uf.find id₁, uf.find id₂) and by hOp we have ¬uf.find id₁ = uf.find id₂
    So the length must decrease

  -/
  /-
  have h2to1 : changeLeader uf id₁ id₂ (uf.find id₂, uf.find id₂) = (uf.find id₂, uf.find id₁) := by
    simp[changeLeader]

  have hnot_self : canon (changeLeader uf id₁ id₂ (uf.find id₂, uf.find id₂)) = false := by
    simp [h2to1, canon]
    exact fun h => hOp h.symm

  have hwas_self : canon (uf.find id₂, uf.find id₂) = true := by
    simp [canon]
  -/



  /-

  let change2to1 := fun (x : EClassId × EClassId) =>
    if x.snd = uf.find id₂ then (x.fst, uf.find id₁) else (x.fst, x.snd)


  have h2to1 : change2to1 (uf.find id₂, uf.find id₂) = (uf.find id₂, uf.find id₁) := by
    simp[change2to1]



  have hnot_self : equalPairs (change2to1 (uf.find id₂, uf.find id₂)) = false := by
    simp [h2to1, equalPairs]
    exact fun h => hOp h.symm
  have hwas_self : equalPairs (uf.find id₂, uf.find id₂) = true := by
    simp [equalPairs]

  -/















  sorry
-/

theorem UF.unionPreservesWellFormed (uf : UF) (h : uf.wellFormed) (id₁ id₂ : EClassId)
    (h₁ : uf.isValidID id₁) (h₂ : uf.isValidID id₂) :
      (union uf id₁ id₂).fst.wellFormed := by

  rcases h with ⟨hv, hc, hr, hcmp, huk⟩
  have h : uf.wellFormed := ⟨hv, hc, hr, hcmp, huk⟩
  -- surely there is a better way to deconstruct and still keep

  unfold wellFormed

  have nv   := unionPreservesValid uf hv id₁ id₂ h₁
  have nc   := unionPreservesCanon uf hc id₁ id₂
  have nr   := unionPreservesReps uf id₁ id₂ h h₁ h₂
  have ncmp := unionPreservesComplete uf id₁ id₂ h
  -- have nekp : (uf.union id₁ id₂).fst.everyKeyPresent := sorry
  have nuk  := unionPreservesUniqueKeys uf huk id₁ id₂

  exact ⟨nv, nc, nr, ncmp, nuk⟩

theorem UF.pushPreservesWellFormed (uf : UF) (h : uf.wellFormed) :
    uf.push.fst.wellFormed := by

  rcases h with ⟨hv, hc, hr, hcmp, huk⟩
  have h : uf.wellFormed := ⟨hv, hc, hr, hcmp, huk⟩
  -- surely there is a better way to deconstruct and still keep

  unfold wellFormed

  have nv   := pushPreservesValid uf hv
  have nc   := pushPreservesCanon uf hc hv
  have nr   := pushPreservesReps uf hr
  have ncmp := pushPreservesComplete uf h
  -- have nekp := pushPreservesEveryKeyPresent uf h
  have nuk  := pushPreservesUniqueKeys uf h

  exact ⟨nv, nc, nr, ncmp, nuk⟩



end Naive
