import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice
import Lustrean.Imp

namespace Lustrean
class BoundedLattice (α : Type) where
  bot : α
  top : α
  join : α → α → α
  meet : α → α → α
  join_commutative : ∀ (x y : α), join x y = join y x
  join_associative : ∀ (x y z : α), join (join x y) z = join x (join y z)
  join_absorption : ∀ (x y : α), join x (meet x y) = x
  join_bot : ∀ (x : α), join x bot = x
  join_top : ∀ (x : α), join x top = top
  meet_commutative : ∀ (x y : α), meet x y = meet y x
  meet_associative : ∀ (x y z : α), meet (meet x y) z = meet x (meet y z)
  meet_absorption : ∀ (x y : α), meet x (join x y) = x
  meet_top : ∀ (x : α), meet x top = x
  meet_bot : ∀ (x : α), meet x bot = bot
  non_trivial : top ≠ bot := by decide
export BoundedLattice (bot top join meet)

instance {α: Type}[Lattice α][ι : BoundedOrder α] : BoundedLattice α where
  bot := ⊥
  top := ⊤
  join x y := x ⊔ y
  meet x y := x ⊓ y
  join_commutative := by grind
  join_associative := by grind
  join_absorption x y := by simp
  join_bot := by simp
  join_top := by simp
  meet_commutative := by grind
  meet_associative := by grind
  meet_absorption x y := by simp
  meet_bot := by simp
  meet_top := by simp
  non_trivial := by sorry

notation " ⊤ " => top
notation " ⊥ " => bot
infixr:60 " ⊔ " => join
infixr:70 " ⊓ " => meet

namespace BoundedLattice
variable {α : Type} [ι : BoundedLattice α]

attribute [simp] bot top join meet
attribute [simp]
join_associative join_absorption join_bot join_top
meet_associative meet_absorption meet_bot meet_top

def IsBot : α → Prop :=
  (· = ⊥)

def IsSubset : α → α → Prop :=
  fun x y => x = meet x y

infixr:50 " ⊑ " => IsSubset

theorem trans : ∀ {x y z : α}, x ⊑ y → y ⊑ z → x ⊑ z := by
  intros x y z Hx Hy
  unfold IsSubset at *
  rw [Hx]
  conv =>
    lhs
    rw [Hy]
  rw [meet_associative]

instance : Trans (@IsSubset α ι) (@IsSubset α ι) (@IsSubset α ι) where
  trans := trans

theorem bot_min : ∀ {x : α}, ⊥ ⊑ x := by
  intros x
  unfold IsSubset
  simp [meet_commutative]

theorem antisymm : ∀ {x y : α}, x ⊑ y → y ⊑ x → x = y := by
  intros x y H H'
  unfold IsSubset at *
  rw [meet_commutative] at H'
  rw [H]
  symm
  assumption

instance : Std.Antisymm (@IsSubset α ι) where
  antisymm := @antisymm _ _

local instance instBoundedLatticeLE : LE α where
  le := IsSubset

instance : Std.IsPreorder α where
  le_refl a := by
    simp [LE.le, IsSubset]


@[simp]
theorem min_bot_is_bot : ∀ {x : α}, x ⊑ ⊥ → x = bot := by
  intros x H
  apply antisymm
  · assumption
  · apply bot_min

theorem min_join_left : ∀ {x y : α}, x ⊑ x ⊔ y := by
  intros x y
  unfold IsSubset
  symm
  apply meet_absorption

theorem min_join_right : ∀ {x y : α}, y ⊑ x ⊔ y := by
  intros
  rw [join_commutative]
  apply min_join_left

theorem join_eq_bot_iff_bot : ∀ {x y : α}, x ⊔ y = ⊥ ↔ x = ⊥ ∧ y = ⊥ := by
  intros x y
  constructor
  · intros H
    have : ∀ (a b : α), a ⊔ b = ⊥ → a = ⊥ := by
      intros a b Ha
      have : a = a ⊓ (a ⊔ b) := by simp
      rw [this, Ha]
      simp
    constructor <;> apply this <;> first | assumption | rw [join_commutative] <;> assumption
  · intro ⟨ Hx, Hy ⟩
    simp [Hx, Hy]

theorem meet_not_bot_left : ∀ {x y : α}, x ⊓ y ≠ ⊥ → x ≠ ⊥ := by
  intros x y H Hc
  apply H
  rw [Hc, meet_commutative]
  simp

theorem meet_not_bot_right : ∀ {x y : α}, x ⊓ y ≠ ⊥ → y ≠ ⊥ := by
  intros x y H Hc
  apply H
  rw [Hc]
  simp

instance [DecidableEq α] : DecidablePred (@IsBot α ι) := by
  rename_i ι'
  intros _
  apply ι'

instance [DecidableEq α] : DecidableRel (@IsSubset α ι) := by
  rename_i ι'
  intros _ _
  apply ι'

def IsIncreasing : (Nat → α) → Prop :=
  fun x => ∀ n, x n ⊑ x (n+1)

def IsDecreasing : (Nat → α) → Prop :=
  fun x => ∀ n, x (n+1) ⊑ x n

@[simp]
theorem join_idempotent : ∀ x : α, x ⊔ x = x := by
  intros x
  conv =>
    lhs
    arg 2
    rw [←meet_top x]
  apply join_absorption

@[simp]
theorem meet_idempotent : ∀ x : α, x ⊓ x = x := by
  intros x
  conv =>
    lhs
    arg 2
    rw [←join_bot x]
  apply meet_absorption

theorem refl : ∀ {x : α}, x ⊑ x := by
  intros x
  simp [IsSubset]

@[simp]
theorem meet_min_left : ∀ {x y : α}, x ⊓ y ⊑ x := by
  intros x y
  simp [IsSubset]
  conv =>
    rhs
    arg 2
    rw [meet_commutative]
  rw [←meet_associative]
  simp

@[simp]
theorem meet_min_right : ∀ {x y : α}, x ⊓ y ⊑ y := by
  intros x y
  rw [meet_commutative]
  apply meet_min_left

end BoundedLattice

class Widen (α : Type) where
  -- Nat : number of iterations
  widen : α → α → Nat → α
export Widen (widen)

macro l:term " ∇_" n:term:max r:term : term => ``(widen $l $r $n)

namespace Widen
variable {α : Type} [Widen α]

@[simp]
def widenSeq (x : Nat → α) : Nat → α
  | 0 => x 0
  | .succ n => (widenSeq x n) ∇_n (x n.succ)
end Widen

class WidenLawful (α : Type)
extends Widen α, BoundedLattice α
where
  covering_left : ∀ (x y : α) n, x ⊑ (x ∇_n y)
  covering_right : ∀ (x y : α) n, y ⊑ (x ∇_n y)
  -- trust Adrien for termination

class Narrow (α : Type) where
  -- Nat : number of iterations
  narrow : α → α → Nat → α

namespace Narrow
variable {α : Type} [Narrow α]

@[simp]
def narrowSeq (x : Nat → α) (n : Nat) : α := match n with
  | 0 => x 0
  | .succ n => Narrow.narrow (narrowSeq x n) (x n.succ) n
end Narrow

class NarrowLawful (α : Type)
extends Narrow α, BoundedLattice α
where
  bounding_low : ∀  (x y : α) (n : Nat), (x ⊓ y) ⊑ (narrow x y n)
  bounding_high : ∀  (x y : α) (n : Nat), (narrow x y n) ⊑ x
  -- trust Adrien for termination

class Domain (α : Type)[BEq α]
extends BoundedLattice α, ToString α,
  WidenLawful α, NarrowLawful α
where
  nb_var : Nat
  dec_bot: DecidablePred (· = bot)
  -- keep only elements satisfying the boolean expression
  guard : α → BExpr nb_var → α
  assign : α → Fin nb_var → IExpr nb_var → α
export Domain (guard assign)

instance (α : Type) [BEq α][ι: Domain α] : DecidablePred (· = (bot: α)) := ι.dec_bot


section conversions
namespace BoundedLattice
instance {α: Type}[BoundedLattice α]: LE α where
  le := BoundedLattice.IsSubset

instance {α: Type}[BoundedLattice α]: OrderBot α where
  bot := bot
  bot_le :=
end BoundedLattice
end conversions

end Lustrean
