import Lustrean.Domain.NonRelational.Basic

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

@[simp]
theorem _root_.Vector.ofFn_get_self{α: Type}{n: Nat}(v: Vector α n)
: Vector.ofFn (fun i => v.get i) = v
:= by ext; simp [getElem]

@[simp, grind =]
theorem meet_top : x.meet top = x := by
  match x with
  | .bot => simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩ =>
    if h: (⊤ : α) = ⊥  then
      exfalso
      apply x_prop 0
      apply BoundedLattice.trivial_of_top_eq_bot h
    else
      simp [meet, map2Nil, coalesce, top, *]

@[simp, grind =]
theorem meet_bot : x.meet bot = bot := by
  cases x <;> simp [meet, map2Nil]

@[grind =]
theorem meet_commutative : meet x y = meet y x := by
  cases x <;> cases y <;> simp [meet, map2Nil, coalesce]
  rename_i x y
  simp [BoundedLattice.meet_commutative]

@[simp, grind =]
theorem bot_meet : bot.meet x = bot := by simp [meet_bot, meet_commutative]

@[simp]
theorem top_meet : top.meet x = x   := by simp [meet_top, meet_commutative]

theorem meet_associative : meet (meet x y) z = meet x (meet y z) := by
  cases x with
  | bot => simp
  | non_rel x' =>
  rename_i n
  obtain ⟨x, x_prop⟩ := x'
  cases y with
  | bot => simp
  | non_rel y' =>
  obtain ⟨y, y_prop⟩ := y'
  cases z with
  | bot => simp
  | non_rel z' =>
  obtain ⟨z, z_prop⟩ := z'
  simp [meet, map2Nil]
  simp only [meet, map2Nil, coalesce]
  simp only [Vector.get_of_fn_fin]
  if h : ∀ i : Fin (n+1), x.get i ⊓ y.get i ⊓ z.get i ≠ ⊥ then
    have: ∀ i : Fin (n+1), x.get i ⊓ y.get i ≠ ⊥ := by
      grind [BoundedLattice.meet_associative, BoundedLattice.meet_commutative, BoundedLattice.meet_bot]
    have: ∀ i : Fin (n+1), y.get i ⊓ z.get i ≠ ⊥ := by
      grind [BoundedLattice.meet_associative, BoundedLattice.meet_commutative, BoundedLattice.meet_bot]
    simp [*]
  else
    by_cases ∀ i: Fin (n+1), x.get i ⊓ y.get i ≠ ⊥ <;>
    by_cases ∀ i : Fin (n+1), y.get i ⊓ z.get i ≠ ⊥ <;>
    simp [*]

theorem meet_absorption : meet x (join x y) = x := by
  match x, y with
  | .bot, _ =>
    simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩, .bot =>
    simp [join, meet, map2Nil, coalesce, BoundedLattice.meet_idempotent, *]
  | .non_rel ⟨x, x_prop⟩, .non_rel ⟨y, y_prop⟩ =>
    simp [meet, map2Nil, join, coalesce, *]

end Lustrean.NonRelational
