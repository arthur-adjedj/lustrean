import Lustrean.Domain.NonRelational.Lattice
import Lustrean.Domain.NonRelational.Widen

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]

protected def narrow (x y : NonRelational α n) (m : Nat) := map2Nil x y fun x y => Vector.ofFn fun i =>
  Narrow.narrow (x.get i) (y.get i) m

instance : Narrow (NonRelational α n) where
  narrow := NonRelational.narrow

instance : NarrowLawful (NonRelational α n) where
  bounding_low x y m := by
    match x, y with
    | .non_rel ⟨x, x_prop⟩, .non_rel ⟨y, y_prop⟩ =>
      simp [Narrow.narrow, NonRelational.narrow, map2Nil, coalesce, NonRelational.meet, Min.min, Lustrean.meet]
      split
      case isFalse => apply BoundedLattice.bot_min
      case isTrue H =>
        rw [dif_pos]
        case hc =>
          intros i Hc
          apply H i
          apply BoundedLattice.min_bot_is_bot
          conv =>
            rhs
            rw [← Hc]
          apply NarrowLawful.bounding_low
        rw [non_rel_subset]
        intros i
        simp
        apply NarrowLawful.bounding_low
    | .bot, _ | _, .bot=>
      simp [Narrow.narrow, NonRelational.narrow, map2Nil, NonRelational.meet, Min.min, Lustrean.meet]
      apply BoundedLattice.bot_min

  bounding_high := by
    intros x y n
    cases x <;> cases y <;> simp [Narrow.narrow, NonRelational.narrow, map2Nil, coalesce]
    rename_i x y
    split
    case isFalse => apply BoundedLattice.bot_min
    case isTrue H =>
      rw [non_rel_subset]
      intros i
      simp
      apply NarrowLawful.bounding_high
    all_goals rfl
end Lustrean.NonRelational
