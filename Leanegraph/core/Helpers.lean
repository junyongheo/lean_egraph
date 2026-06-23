variable {α β : Type _} [DecidableEq α]

def uniqueInsert (cur : List (α × β)) (k : α) (v : β) : List <| α × β :=
  (k, v) :: cur.filter (λ p => p.1 != k)

def uniqueRemove (cur : List (α × β)) (k : α) : List <| α × β :=
  cur.filter (λ p => p.1 != k)

def uniqueReplace : List (α × β) → α → β → List (α × β)
| [],               _, _ => []
| ((k', v') :: xs), k, v => if k == k' then (k, v) :: xs else (k', v') :: uniqueReplace xs k v

/-
not equal
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
not needed
theorem uniqueReplace_Preserves_Unique
  (cur : List (α × β)) (hBefore : KeysUnique cur) (k : α) (v : β) : KeysUnique (uniqueReplace cur k v) := by
  unfold KeysUnique uniqueReplace
  simp
  induction cur with
  | nil => simp[]
  | cons x xs h =>
    simp[]
    sorry
-/
