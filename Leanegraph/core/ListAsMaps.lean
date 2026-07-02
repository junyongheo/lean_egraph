variable {α β : Type _} [DecidableEq α]

-- Inserts a key/value pair into the map
-- Overwrites existing key
-- TODO: do we ever need to reject existing keys?
-- TODO: what did I mean by that?
def uniqueInsert (cur : List (α × β)) (k : α) (v : β) : List <| α × β :=
  (k, v) :: cur.filter (λ p => p.1 != k)

-- Removes a key/value pair from the map.
def uniqueRemove (cur : List (α × β)) (k : α) : List <| α × β :=
  cur.filter (λ p => p.1 != k)

def uniqueReplace : List (α × β) → α → β → List (α × β)
| [],               _, _ => []
| ((k', v') :: xs), k, v => if k == k' then (k, v) :: xs else (k', v') :: uniqueReplace xs k v


-- this doesn't need the unique name but for the sake of consistency
-- kinda interesting that the std impl. uses ```match k = k with true/false```,
-- TODO: SOMEDAY: look that up one day
-- better for simp? case splitting?
-- iig can just use the standard and no need to define this
/-
def uniqueLookup : List (α × β) → α → Option β
| [], _ => none
| ((k', v) :: xs), k =>
  if k = k' then some v else uniqueLookup xs k

-- #eval uniqueLookup [(0,1), (2,4), (3,6)] 4
-/
/-
not equal!! Replace must R E P L A C E and not I N S E R T
def uniqueReplace' : List (α × β) → α → β → List (α × β) :=
  λ cur k v => uniqueInsert (uniqueRemove cur k) k v
-/

def KeysUnique (cur : List (α × β)) : Prop :=
  List.Nodup (cur.map Prod.fst)

theorem keysUnique_filter
  (xs : List (α × β)) (h : KeysUnique xs) (k : α) : KeysUnique (xs.filter (λ p => p.1 != k)) := by
  induction xs with
  | nil => simp[h]
  | cons x xs ih =>
    rcases List.nodup_cons.mp h with ⟨hx, hxs⟩
    simp[KeysUnique, List.filter]
    match h' : x.fst != k with
    | true =>
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨p, hp1, hp2⟩
        apply hx
        rw[List.mem_map]
        exact ⟨p, (List.mem_filter.mp hp1).1, hp2⟩
      · rw[←KeysUnique] at hxs
        rw[←KeysUnique]
        exact ih hxs
    | false =>
      rw[←KeysUnique] at hxs
      rw[←KeysUnique]
      exact ih hxs



theorem uniqueInsert_Preserves_Unique
  (cur : List (α × β)) (hBefore : KeysUnique cur) (k : α) (v : β) : KeysUnique (uniqueInsert cur k v) :=
  by
    unfold KeysUnique
    unfold uniqueInsert
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨p, hp, hpkey⟩
      have hp' := List.mem_filter.mp hp
      have hneq : p.1 != k := hp'.2

      subst hpkey
      simp[] at hneq
    ·
      rw [←KeysUnique]
      exact keysUnique_filter cur hBefore k

theorem uniqueRemove_Preserves_Unique
  (cur : List (α × β)) (hBefore : KeysUnique cur) (k : α) : KeysUnique (uniqueRemove cur k) := by
  exact keysUnique_filter cur hBefore k



/-
theorem uniqueReplace_Preserves_Unique
  (cur : List (α × β)) (hBefore : KeysUnique cur) (k : α) (v : β) : KeysUnique (uniqueReplace cur k v) := by
  unfold KeysUnique uniqueReplace
  simp
  induction cur with
  | nil => simp[]
  | cons x xs h =>
    simp[]
    split
    case isTrue hEq =>
      have hN : List.Nodup (k :: xs.map Prod.fst) := by
        simpa [hEq, KeysUnique] using hBefore
      simp[hN]
    case isFalse hFalse =>
      have hBefore' : List.Nodup (x.1 :: xs.map Prod.fst) := by
        simpa [KeysUnique] using hBefore
      rcases List.nodup_cons.mp hBefore' with ⟨hx, hxs⟩
      constructor
      ·

      sorry
-/


theorem uniqueReplace_map_fst
    (cur : List (α × β)) (k : α) (v : β) :
    (uniqueReplace cur k v).map Prod.fst = cur.map Prod.fst := by
  induction cur with
  | nil =>
      simp [uniqueReplace]
  | cons x xs ih =>
      simp [uniqueReplace]
      split
      · simp[]
        assumption
      · simp [ih]

theorem uniqueReplace_Preserves_Unique
  (cur : List (α × β))
  (hBefore : KeysUnique cur)
  (k : α)
  (v : β) :
  KeysUnique (uniqueReplace cur k v) := by
  unfold KeysUnique
  rw [uniqueReplace_map_fst]
  exact hBefore


/-
  Instead of structure, apparently these subtype things are useful
-/

abbrev ListMap α β := { val : List (α × β) // KeysUnique val }

def ListMap.empty : ListMap α β :=
  ⟨
    [],
    by unfold KeysUnique; simp
  ⟩


def ListMap.insert (k : α) (v : β) (map : ListMap α β) : ListMap α β :=
  ⟨
    uniqueInsert map.val k v,
    uniqueInsert_Preserves_Unique map.val map.2 k v
  ⟩

def ListMap.remove (k : α) (map : ListMap α β) : ListMap α β :=
  ⟨
    map.val.filter (λ p => p.1 != k),
    keysUnique_filter map.val map.property k
  ⟩


def ListMap.replace (k : α) (v : β) (map : ListMap α β) : ListMap α β :=
  ⟨
    uniqueReplace map.val k v,
    by
      unfold KeysUnique
      rw[uniqueReplace_map_fst]
      exact map.property
  ⟩

def ListMap.lookup (map : ListMap α β) (k : α) : Option β :=
  map.val.lookup k

/-
theorem mapNoTouchKeys {α β γ : Type _} (xs : List (α × β)) (f : β → γ) :
      (xs.map (fun (k, v) => (k, f v))).map Prod.fst = xs.map Prod.fst := by
  simp
-/


-- maybe i shouldn't call it map
def ListMap.map {γ : Type _} (xs : ListMap α β) (f : α → β → γ) : ListMap α γ :=
  ⟨
    xs.val.map (λ (k, v) => (k, f k v)),
    by
      /-
        Idea: Map doesn't touch keys, so KeysUnique is trivially preserved
        H e l p e r  L e m m a
        Maybe we can inline the helper lemma for brevity
        Do we need the theorem separately..?
        TODO:don't delete for later use (uncomment) if needed
      -/
      have mapNoTouchKeys (xs : List (α × β)) (f : β → γ) :
        (xs.map (fun (k, v) => (k, f v))).map Prod.fst = xs.map Prod.fst := by
        simp
      unfold KeysUnique
      simp -- [mapNoTouchKeys xs.val f]
      -- SOMEDAY: lookup simp, does it try run things from context?
      exact xs.property

  ⟩


-- Should this be a prop?
def ListMap.contains (map : ListMap α β) (k : α) : Bool :=
  map.val.any (λ (k', _) => k == k')

def ListMap.notContains (map : ListMap α β) (k : α) : Prop :=
  map.val.all (λ (k', _) => k != k')











/-
  Question: Can we encode the invariant into the type? That's a benefit of DTT right
  A well formed map is one with unique keys, but how to encode?
-/

structure ListMapStr (α : Type _) (β : Type _) where
  Vals   : List (α × β)
  Unique : KeysUnique Vals -- reused

-- #print ListMap -- structures are types, is this good enough?

/-
  Define our Insert, Replace, Delete Functions
  For insert presumably induction is easiest,
  define the base case
-/

-- Base Case is the existence of a well formed ListMap
def emptyListMap : ListMapStr α β := ⟨[], by simp[KeysUnique]⟩

/-
  Proof Sketch:
    - Given: Map is well formed (because it exists, yay!)
    - Show:
      - k ∉ map.Vals.filter
      - Insert k is fine
-/
def ToListMap (k : α) (v : β) (map : ListMapStr α β) : ListMapStr α β :=
  ⟨
    (k, v) :: map.Vals.filter (λ p => p.1 != k),
    by
      unfold KeysUnique
      apply List.nodup_cons.mpr -- break down nodup into its precond
      /-
        Goal at this point
        ¬(k, v).fst ∈ List.map Prod.fst (List.filter (fun p => p.fst != k) map.Vals)
        ∧
        (List.map Prod.fst (List.filter (fun p => p.fst != k) map.Vals)).Nodup

        Use constructor to break into the two halves
      -/
      constructor
      · -- ¬(k, v).fst ∈ List.map Prod.fst (List.filter (fun p => p.fst != k) map.Vals)
        -- In English: Show that k is not in the filtered list
        intro hmem -- goal into "isMem → False"
        -- Rewrite hmem
        rw[List.mem_map] at hmem
        rcases hmem with ⟨p, hp, hpkey⟩ -- break into parts
        -- rcases can break down a fancy term into constituent parts in one go
        rw[List.mem_filter] at hp -- rewrite the filter in hp
        rcases hp with ⟨hp', hpNotkey⟩ -- hp broken into parts
        simp at hpkey -- get "p.fst = k"
        /-
          Current State, we have
            hpNotkey : (p.fst != k) = true and hpkey : p.fst = k (badly named)
            Together we get a contradiction for prove goal of false
        -/
        rw[hpkey] at hpNotkey
        simp at hpNotkey

      · -- (List.map Prod.fst (List.filter (fun p => p.fst != k) map.Vals)).Nodup
        -- In English: Show that the filtered list is nodup
        rw[←KeysUnique]
        -- Goal: KeysUnique (List.filter (fun p => p.fst != k) map.Vals)
        apply keysUnique_filter map.Vals map.Unique
  ⟩

def ListMapStr.insert (k : α) (v : β) (map : ListMapStr α β) : ListMapStr α β :=
  ⟨
    (k, v) :: map.Vals.filter (λ p => p.1 != k),
    by
      unfold KeysUnique
      apply List.nodup_cons.mpr
      constructor
      ·
        intro hmem
        rw[List.mem_map] at hmem
        rcases hmem with ⟨p, hp, hpkey⟩
        have hp' := List.mem_filter.mp hp
        have hnm := hp'.2
        subst hpkey
        simp at hnm
      ·
        rw[←KeysUnique]
        apply keysUnique_filter map.Vals map.Unique
  ⟩


/-
  Since keys are unique, filtering by a key should do at most 1 pair of damage
-/
def ListMapStr.remove (k : α) (map : ListMapStr α β) : ListMapStr α β :=
  ⟨
    map.Vals.filter (λ p => p.1 != k),
    by
      exact keysUnique_filter map.Vals map.Unique k
  ⟩

theorem uniqueReplace_map_fst2
    (cur : List (α × β)) (k : α) (v : β) :
    (uniqueReplace cur k v).map Prod.fst = cur.map Prod.fst := by
  induction cur with
  | nil =>
    rfl
  | cons x xs ih =>
    simp[uniqueReplace]
    split
    case isTrue =>
      simpa -- simp + assumption?
      -- assumption
    case isFalse =>
      simp[ih]


def ListMapStr.replace (k : α) (v : β) (map : ListMapStr α β) : ListMapStr α β :=
  ⟨
    uniqueReplace map.Vals k v,
    by
      unfold KeysUnique
      rw[uniqueReplace_map_fst2]
      exact map.Unique
  ⟩
