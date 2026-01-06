import Lustrean.Domain.NonRelational.JoinLemmas
import Lustrean.Domain.NonRelational.MeetLemmas

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]

instance : BoundedLattice (NonRelational α n) where
  join_commutative := join_commutative
  join_associative := join_associative
  join_absorption := join_absorption
  join_bot := join_bot
  join_top := join_top
  meet_commutative := meet_commutative
  meet_associative := meet_associative
  meet_absorption := meet_absorption
  meet_top := meet_top
  meet_bot := meet_bot
  join_is_lub x y z xz yz := by
    fun_cases (x.join y) with
    | case1 n x x_prop y y_prop =>
      cases z with
      | non_rel env =>
        dsimp only [Min.min, Max.max] at *
        simp only [Join.join, join]
        simp only [Meet.meet, meet, map2Nil, coalesce, Fin.getElem_fin, Vector.getElem_ofFn, ne_eq] at xz yz ⊢
        split at xz; case isFalse => simp only [reduceCtorEq] at xz
        rename_i h
        split at yz; case isFalse => simp only [reduceCtorEq] at yz
        rename_i h'
        simp only [non_rel.injEq, Subtype.mk.injEq] at xz yz
        have := fun (i: Fin (n+1)) => BoundedLattice.join_is_lub (x[i.val]) (y[i.val]) env.val[i.val]
          (by grind) (by grind)
        have next_cond: ∀ (i : Fin (n + 1)), ¬ (x[i.val] ⊔ y[i.val]) ⊓ env.val[i.val] = ⊥
        := by
          intro i
          rw [←this i]
          apply BoundedLattice.join_eq_bot_iff_bot.not.mpr
          grind
        simp only [next_cond, not_false_eq_true, implies_true, ↓reduceDIte, non_rel.injEq,
          Subtype.mk.injEq]
        ext i i_idx
        specialize this ⟨i, i_idx⟩
        simpa only [Vector.getElem_ofFn]
      | bot =>
        simp only [meet_bot, reduceCtorEq] at xz
    | case2 =>
      simpa only [meet_bot]
    | case3 =>
      simpa only [join_bot]
  meet_is_glb x y z xz yz := by
    rcases x with ⟨x, x_prop⟩ | _; case bot =>
      simpa only [meet_bot, bot_meet] using xz
    rename_i n
    rcases y with ⟨y, y_prop⟩ | _; case bot =>
      simpa only [meet_bot, bot_meet] using yz
    rcases z with ⟨z, z_prop⟩ | _; case bot =>
      simp only [bot_meet]
    dsimp [Min.min] at xz yz ⊢
    simp only [Meet.meet, meet, map2Nil, coalesce] at xz yz
    split at xz; case isFalse => simp only [reduceCtorEq] at xz
    rename_i hx
    split at yz; case isFalse => simp only [reduceCtorEq] at yz
    rename_i hy
    simp only [non_rel.injEq, Subtype.mk.injEq, Fin.getElem_fin] at xz yz
    have := fun (i: Fin (n+1)) => BoundedLattice.meet_is_glb (x[i.val]) (y[i.val]) z[i.val]
      (by grind) (by grind)
    simp only [Meet.meet, meet, map2Nil, coalesce]
    have cond₁: ∀ (i : Fin (n + 1)), ¬ x[i.val] ⊓ y[i.val] = ⊥
    := by
      intros i h
      specialize this i
      simp only [h, BoundedLattice.meet_bot, z_prop] at this
    have cond₂: ∀ (i : Fin (n + 1)), ¬z[i.val] ⊓ (x[i.val] ⊓ y[i.val]) = ⊥
      := by grind
    grind
end Lustrean.NonRelational
