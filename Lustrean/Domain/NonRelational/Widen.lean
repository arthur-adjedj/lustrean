import Lustrean.Domain.NonRelational.Lattice

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]

-- set_option maxHeartbeats 1222222 in
theorem non_rel_subset : ∀ (x y : {env : Vector α (n+1) // ∀ i, ¬ env[i] = ⊥}),
  NonRelational.non_rel x ⊑ NonRelational.non_rel y
  ↔ ∀ i : Fin (n+1), x.val[i] ⊑ y.val[i]
:= by
  intros x y
  obtain ⟨x, x_prop⟩ := x
  obtain ⟨y, y_prop⟩ := y
  apply Iff.intro <;> intros H
  · unfold BoundedLattice.IsSubset at H
    simp only [Min.min, Lustrean.meet] at H
    simp only [NonRelational.meet, map2Nil, coalesce] at H
    simp at H
    split at H <;> rename_i h'
    · simp at H
      intros i
      simp [BoundedLattice.IsSubset]
      rw [H]
      simp
    · cases H
  · simp only [BoundedLattice.IsSubset]
    simp only [Min.min, Lustrean.meet]
    simp only [NonRelational.meet]
    simp [map2Nil, coalesce]
    simp [BoundedLattice.IsSubset, -left_eq_inf] at H
    rw [dif_pos]
    case hc =>
      intros i
      rw [←H i]
      apply x_prop
      -- TODO: grind fails here
    simp only [non_rel.injEq, Subtype.mk.injEq]
    ext i h
    simp only [Vector.getElem_ofFn, ←H]

protected def widen : NonRelational α n → NonRelational α n → Nat → NonRelational α n
  | .non_rel x, .non_rel y, n => .non_rel
    <| .mk (Vector.ofFn fun i => x.val.get i ∇_n y.val.get i)
    <| by
      intros i
      simp
      intros Hc
      apply x.property i
      apply BoundedLattice.antisymm
      · conv =>
          rhs
          rw [←Hc]
        apply WidenLawful.covering_left
      · apply BoundedLattice.bot_min
  | .bot, z, _ | z, .bot, _ => z

instance : Widen (NonRelational α n) where
  widen := NonRelational.widen

instance : WidenLawful (NonRelational α n) where
  covering_left := by
    intros x y n
    cases x <;> cases y <;> simp [widen, NonRelational.widen]
    <;> (try apply BoundedLattice.bot_min)
    <;> (try apply BoundedLattice.refl)
    rename_i x y
    rw [non_rel_subset]
    intros i
    simp
    apply WidenLawful.covering_left

  covering_right := by
    intros x y n
    cases x <;> cases y <;> simp [widen, NonRelational.widen]
    <;> (try apply BoundedLattice.bot_min)
    <;> (try apply BoundedLattice.refl)
    rename_i x y
    rw [non_rel_subset]
    intros i
    simp
    apply WidenLawful.covering_right
end Lustrean.NonRelational