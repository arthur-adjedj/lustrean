
theorem piext {α} : ∀ β β' : α → Sort _, (∀ x, β x = β' x) → (∀ x, β x) = (∀ x, β' x) := by
  intros β β' βx_eq_β'x
  have : β = β' := by
    funext
    apply βx_eq_β'x
  rw [this]

macro "piext " x:ident : tactic => `(tactic| (apply piext; intro $x:ident))