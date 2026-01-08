import Lustrean.Domain.NonRelational.Basic
import Misc.Vector

namespace Lustrean.NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]
variable (x y z : NonRelational α n)

@[simp]
theorem _root_.Vector.ofFn_getElem_self{α: Type}{n: Nat}(v: Vector α n)
: Vector.ofFn (fun i => v[i.val] ) = v
:= by ext; simp [getElem]

@[simp]
theorem meet_top : x ⊓ top = x := by
  simp only [Min.min, Meet.meet]
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
theorem meet_bot : x ⊓ bot = bot := by
  cases x <;> simp [Min.min, Meet.meet, meet, map2Nil]

@[grind =]
theorem meet_commutative : x ⊓ y = y ⊓ x := by
  dsimp only [Min.min, Meet.meet]
  cases x <;> cases y <;> simp [meet, map2Nil, coalesce]
  rename_i x y
  simp [BoundedLattice.meet_commutative]

@[simp, grind =]
theorem bot_meet : bot ⊓ x = bot := by simp [meet_bot, meet_commutative]

@[simp]
theorem top_meet : top ⊓ x = x   := by simp [meet_top, meet_commutative]

set_option maxHeartbeats 1000000 in
theorem meet_associative : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := by
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
  dsimp [Min.min, Meet.meet]
  simp only [meet, map2Nil, Fin.getElem_fin]
  if h : ∀ i : Fin (n+1), ¬ x[i.val] ⊓ y[i.val] ⊓ z[i.val] = ⊥ then
    have h_xy: ∀ i : Fin (n+1), ¬ x[i.val] ⊓ y[i.val] = ⊥ := by
      intros i h'
      specialize h i
      rw [h'] at h
      simp at h
    have h_yz: ∀ i : Fin (n+1), ¬ y[i.val] ⊓ z[i.val] = ⊥ := by
      intros i h'
      specialize h i
      rw [BoundedLattice.meet_associative, h'] at h
      simp at h
    unfold coalesce
    simp at h_xy h_yz
    simp [h_xy, h_yz]
  else
    unfold coalesce
    if h_xy: ∀ i : Fin (n+1), ¬ x[i.val] ⊓ y[i.val] = ⊥ then
      if h_yz: ∀ i : Fin (n+1), ¬ y[i.val] ⊓ z[i.val] = ⊥ then
        simp [h_xy, h_yz]
      else
        simp [h_xy, h_yz]
        simp at h_yz
        obtain ⟨e, P⟩ := h_yz
        exists e
        simp [P]
    else
      simp [h_xy]
      if h_yz: ∀ i : Fin (n+1), ¬ y[i.val] ⊓ z[i.val] = ⊥ then
        simp [h_yz]
        simp at h_xy
        obtain ⟨e, P⟩ := h_xy
        exists e
        rw [←BoundedLattice.meet_associative]
        simp [P]
      else
        simp [h_yz]

theorem meet_absorption : x  ⊓(x ⊔ y) = x := by
  dsimp [Max.max, Min.min, Meet.meet, Join.join]
  match x, y with
  | .bot, _ =>
    simp [meet, map2Nil]
  | .non_rel ⟨x, x_prop⟩, .bot =>
    grind only [meet, map2Nil, join, Fin.getElem_fin, coalesce, le_refl, inf_of_le_left,
      Vector.getElem_ofFn, non_rel.injEq, Subtype.mk.injEq]
  | .non_rel ⟨x, x_prop⟩, .non_rel ⟨y, y_prop⟩ =>
    simp [meet, map2Nil, join, coalesce, *]

end Lustrean.NonRelational
