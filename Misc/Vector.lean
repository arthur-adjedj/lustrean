namespace Vector

@[simp]
theorem get_mk_vector_fin {α n} : ∀ (x : α) (i : Fin n), (Vector.replicate n x).get i = x := by
  intros x i
  apply Vector.getElem_replicate

@[simp]
theorem get_mk_vector_nat {α n} : ∀ (x : α) (i : Nat) (h : i < n), (Vector.replicate  n x)[i] = x := by
  intros x i h
  rw [Vector.replicate]
  have : i < (Vector.replicate n x).size := by simpa using h
  show (Vector.replicate n x)[i] = x
  simp

@[simp]
theorem get_of_fn_fin {α n} : ∀ (f : Fin n → α) (i : Fin n), (Vector.ofFn f).get i = f i := by
  intros f i
  simp [Vector.ofFn]
  show (Array.ofFn f)[i] = f i
  simp

@[simp]
theorem get_of_fn_nat {α n} : ∀ (f : Fin n → α) (i : Nat) (h : i < n), (Vector.ofFn f)[i] = f ⟨i, h⟩ := by
  intros f i h
  simp [Vector.ofFn]

end Vector