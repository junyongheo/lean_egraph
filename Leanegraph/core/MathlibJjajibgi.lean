inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  /-- Two nil lists are `Forall₂`-related -/
  | nil : Forall₂ R [] []
  /-- Two cons lists are related by `Forall₂ R`
  if the heads are related by `R` and the tails are related by `Forall₂ R` -/
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)
