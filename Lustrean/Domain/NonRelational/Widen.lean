import Lustrean.Domain.NonRelational.Lattice

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]

theorem non_rel_subset : ∀ (x y : {env : Vector α (n+1) // ∀ i, env.get i ≠ ⊥}),
  NonRelational.non_rel x ⊑ NonRelational.non_rel y
  ↔ ∀ i : Fin (n+1), x.val.get i ⊑ y.val.get i
:= by
  intros x y
  constructor <;> intros H
  · simp [BoundedLattice.IsSubset, meet] at H
    unfold map2Nil at H
    unfold coalesce at H
    simp at H
    split at H <;> rename_i h'
    · simp at H
      rw [H]
      simp
    · cases H
  · simp [BoundedLattice.IsSubset, meet]
    unfold map2Nil
    simp [coalesce]
    simp [BoundedLattice.IsSubset] at H
    rw [dif_pos]
    case hc => grind
    cases x
    rename_i x Hx
    simp at *
    ext i h
    simp
    apply H

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
