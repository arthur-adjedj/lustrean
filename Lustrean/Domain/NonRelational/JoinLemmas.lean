import Lustrean.Domain.NonRelational.Basic

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

theorem join_commutative : join x y = join y x := by
  cases x <;> cases y <;> simp [join]
  rename_i x y
  simp [BoundedLattice.join_commutative]

theorem join_associative : join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> simp [join]

theorem join_absorption : join x (meet x y) = x := by
  cases x <;> cases y <;> simp only [
    meet,
    map2Nil,
    coalesce
  ]
  split <;> simp [join]
  · ext
    simp
    rfl
  · rfl
  all_goals simp [join]

theorem join_bot : x.join bot = x := by
  cases x <;> simp [join]

theorem join_top : x.join top = top := by
  cases x
  case non_rel n env =>
    obtain ⟨env, prop⟩ := env
    -- have: Decidable (⊤ = ⊥):= ι.dec_bot ⊤
    if h: (⊤: α) = ⊥ then
      exfalso
      apply prop 0
      apply BoundedLattice.trivial_of_top_eq_bot h
    else
      simp [h, join, top]
      grind
  case bot =>
    simp [join]

end Lustrean.NonRelational
