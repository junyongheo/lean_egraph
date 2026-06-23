def search {α} (f : Nat → Option α) (start : Nat) : Option α :=
  match f start with
  | .some x => .some x
  | .none =>
    match start with
    | 0 => .none
    | n+1 => search f n

theorem search_const_none {α} (start : Nat) :
      search (α := α) (fun _ => .none) start = .none := by
  induction start with
  | zero =>
    rw[search]
  | succ n ih =>
    simp[search]
    exact ih

example : search (fun n => if n * n ≤ 121 then .some n else .none) 100 = .some 11 := by
  simp[search]


def sub2 : Nat → Nat
| 0 => 0
| 1 => 0
| x + 2 => x

#print sub2

example (n : Nat) : sub2 n = n - 2 := by
 unfold sub2
 cases n
 case zero => simp
 case succ n => grind


def search2 {α} (f : Nat → Option α) (start : Nat) : α :=
  match f start with
  | .some x => x
  | .none => search f (start + 1)
