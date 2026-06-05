inductive Tree (β : Type v) where
  | leaf
  | node (key : Nat) (value : β) (left : Tree β) (right : Tree β)
deriving Repr

def Tree.contains (t : Tree β) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node k' _ l' r' =>
    if k < k' then
      l'.contains k
    else if k' < k then
      r'.contains k
    else
      true

def Tree.find? (t : Tree β) (k : Nat) : Option β :=
  match t with
  | leaf => none
  | node k' v' l' r' =>
    if k < k' then
      l'.find? k
    else if k' < k then
      r'.find? k
    else
      some v'

def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node k v leaf leaf
  | node k' v' l' r' =>
    if k < k' then
      node k' v' (l'.insert k v) r'
    else if k' < k then
      node k' v' l' (r'.insert k v)
    else
      node k' v' l' r'

def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node k' v' l' r' => l'.toList ++ [(k', v')] ++ r'.toList


#eval Tree.leaf.insert 2 "two"
      |>.insert 3 "three"
      |>.insert 1 "one"
      |>.toList

def Tree.toListTR (t : Tree β) : List (Nat × β) :=
    go t []
  where
    go (t : Tree β) (acc : List (Nat × β)) : List (Nat × β) :=
      match t with
      | leaf => acc
      | node k' v' l' r' => go l' ((k',v') :: go r' acc)

theorem Tree.toList_eq_toListTR (t : Tree β)
        : t.toList = t.toListTR := by
  simp [toListTR, go t []]
where
  go (t : Tree β) (acc : List (Nat × β))
      : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc <;>
      simp [toListTR.go, toList, *, List.append_assoc]

theorem Tree.toList_eq_toListTR' (t : Tree β)
        : t.toList = t.toListTR := by
  simp [toListTR, go t []]
where
  go (t : Tree β) (acc : List (Nat × β))
     : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc <;>
      simp [toListTR.go, toList, *, List.append_assoc]

@[csimp] theorem Tree.toList_eq_toListTR_csimp
    : @Tree.toList = @Tree.toListTR := by
  funext β t
  apply Tree.toList_eq_toListTR

-- Show that a predicate holds for a tree if it:
inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
-- 1. Holds trivially for leaf types
  | leaf : ForallTree p <|.leaf
-- 2. To show that it holds for node,
  | node :
    -- We show that the predicate holds for the current KV
    p key value →
    -- Holds for the left tree (recursively)
    ForallTree p left →
    -- Right subtree
    ForallTree p right →
    -- Then we can conclude it holds for this node.
    ForallTree p (.node key value left right)


-- To show that something is a BST
-- It suffices to show:
inductive BST : Tree β → Prop
  -- Leaf is a BST by construction
  | leaf : BST <|.leaf
  -- That the left nodes are all k < key
  | node :
    ForallTree (λ k v => k < key) left →
    -- Right
    ForallTree (λ k v => k > key) right →
    -- That the leftsubtree is a BST and right
    BST left → BST right →
    -- Then the node is a BST
    BST (.node key value left right)

local macro "by_cases' " e:term : tactic =>
  `(tactic| by_cases $e <;> simp [*])

attribute [local simp] Tree.insert

/-- The `have_eq lhs rhs` tactic (tries to) prove that `lhs = rhs`,
    and then replaces `lhs` with `rhs`. -/
local macro "have_eq " lhs:term:max rhs:term:max : tactic =>
  `(tactic|
    (have h : $lhs = $rhs :=
       -- TODO: replace with linarith
       by simp +arith at *; apply Nat.le_antisymm <;> assumption
     try subst $lhs))

theorem Tree.forall_insert_of_forall
  (h₁ : ForallTree p t) (h₂ : p key value)
  : ForallTree p (t.insert key value) := by
  induction h₁ with
  | leaf => exact .node h₂ .leaf .leaf
  | node hp hl hr ih_l ih_r =>
    rename Nat => k
    by_cases' key < k
    · exact .node hp ih_l hr
    · by_cases' k < key
      · exact .node hp hl ih_r
      · have_eq key k
        exact .node hp hl hr

theorem Tree.bst_insert_of_bst {t : Tree β}
  (h : BST t) (key : Nat) (value : β) : BST (t.insert key value) := by
  induction h with
  | leaf =>
    exact .node .leaf .leaf .leaf .leaf
  | node h₁ h₂ b₁ b₂ ih₁ ih₂ =>
    rename Nat => k
    simp
    by_cases' key < k
    · exact .node (forall_insert_of_forall h₁ ‹key < k›) h₂ ih₁ b₂
    · by_cases' k < key
      · exact .node h₁ (forall_insert_of_forall h₂ ‹k < key›) b₁ ih₂
      · have_eq key k
        exact .node h₁ h₂ b₁ b₂
