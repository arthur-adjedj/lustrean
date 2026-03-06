import Lustrean.Domain.NonRelational.Basic

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

theorem join_commutative : x ⊔ y = y ⊔ x := by
  dsimp [Max.max, Join.join]
  cases x <;> cases y <;> simp [join]
  rename_i x y
  simp [BoundedLattice.join_commutative]

theorem join_associative : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) := by
  dsimp [Max.max, Join.join]
  cases x <;> cases y <;> cases z <;> simp [join]

theorem join_absorption : x ⊔ (x ⊓ y) = x := by
  dsimp [Max.max, Join.join, Min.min, Meet.meet]
  cases x <;> cases y <;> simp only [
    meet,
    map2Nil,
    coalesce
  ]
  split <;> simp [join]
  · ext
    simp
  · rfl
  all_goals simp [join]

theorem join_bot : x ⊔ bot = x := by
  dsimp [Max.max, Join.join]
  cases x <;> simp [join]

theorem join_top : x ⊔ top = top := by
  dsimp [Max.max, Join.join]
  cases x
  case non_rel n env =>
    obtain ⟨env, prop⟩ := env
    -- have: Decidable (⊤ = ⊥):= ι.dec_bot ⊤
    if h: (⊤ : α) = ⊥ then
      exfalso
      apply prop 0
      apply BoundedLattice.trivial_of_top_eq_bot h
    else
      simp [h, join, top]
      grind
  case bot =>
    simp [join]

end Lustrean.NonRelational