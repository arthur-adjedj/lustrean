import Lustrean.Domain.NonRelational
import Lustrean.Domain.GaloisConnection

namespace Lustrean

variable {D₀ D₁: Type} [BEq D₀] [Hashable D₀]
         [ι₀ : ValueDomain D₀] [ι₁ : ValueDomain D₁]

def Partition (D₀ D₁: Type) [BEq D₀] [Hashable D₀]
:= Std.HashMap D₀ D₁

namespace Partition

section Definitions
#eval (Std.HashMap.ofList [(1,0), (0,2)])
instance : ToString (Partition D₀ D₁) where
  toString m := m.toList
    |>.map (fun (cond, concl) => s!"{cond} ↦ {concl}")
    |> ",".intercalate
    |> (s!"({·})")

def join(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def meet(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def add(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def mul(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def neg(x : Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def sub(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def div(x y: Partition D₀ D₁): Partition D₀ D₁ :=
  sorry

def widen(x y: Partition D₀ D₁) (n : Nat): Partition D₀ D₁ :=
  sorry

def narrow(x y: Partition D₀ D₁) (n : Nat): Partition D₀ D₁ :=
  sorry

def refine (op : Lustrean.CompareOp) (x y: Partition D₀ D₁): Partition D₀ D₁ × Partition D₀ D₁ :=
  sorry
end Definitions

instance : Add (Partition D₀ D₁) := sorry -- .mk Partition.add
instance : Mul (Partition D₀ D₁) := sorry -- .mk Partition.mul
instance : Neg (Partition D₀ D₁) := sorry -- .mk Partition.neg
instance : Sub (Partition D₀ D₁) := sorry -- .mk Partition.sub
instance : Div (Partition D₀ D₁) := sorry -- .mk Partition.div
instance : Widen (Partition D₀ D₁)  where widen a b n  := sorry -- a.widen b n
instance : Narrow (Partition D₀ D₁) where narrow a b n := sorry -- a.meet b n

section GaloisConnection
end GaloisConnection

section Theorems

theorem join_commutative(a b: Partition D₀ D₁): a.join b = b.join a := by
  sorry

theorem join_associative (a b c: Partition D₀ D₁): (a.join b).join c = a.join (b.join c) := by
  sorry

theorem meet_commutative(a b: Partition D₀ D₁): a.meet b = b.meet a := by
  sorry

theorem meet_associative(a b c: Partition D₀ D₁): (a.meet b).meet c = a.meet (b.meet c) := by
  sorry

theorem join_absorption: ∀ (x y: Partition D₀ D₁), x.join (x.meet y) = x:= by
  sorry

theorem meet_absorption: ∀ (x y: Partition D₀ D₁), x.meet (x.join y) = x:= by
  sorry

end Theorems


instance : BoundedLattice (Partition D₀ D₁) where
  bot := sorry
  top := sorry
  join := Partition.join
  meet := Partition.meet
  join_bot := by sorry
  join_top := by sorry
  meet_bot := by sorry
  meet_top := by sorry
  non_trivial := by sorry -- decide
  join_commutative := Partition.join_commutative
  join_associative := Partition.join_associative
  meet_commutative := Partition.meet_commutative
  meet_associative := Partition.meet_associative
  join_absorption  := Partition.join_absorption
  meet_absorption  := Partition.meet_absorption

instance : WidenLawful (Partition D₀ D₁) where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_left := by sorry

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_right := by sorry

instance : NarrowLawful (Partition D₀ D₁) where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_high := by sorry

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_low := by sorry

instance : ValueDomain (Partition D₀ D₁) where
  nil := sorry

  compare op x y := Partition.refine op x y

  -- We interpret `None` as if it were ±∞
  rand := sorry

  eq_dec := sorry -- Should be inferred by auto-params

section Correctness

-- theorem add_correct
-- : gc.IsBinAbstraction (· + ·) Sign.add
-- := by sorry

-- def neg_complete
-- : gc.IsAbstraction (-·) Sign.neg
-- := by sorry

-- theorem sub_correct
-- : gc.IsBinAbstraction (· - ·) Sign.sub
-- := by sorry

-- theorem mul_correct
-- : gc.IsBinAbstraction (· * ·) Sign.mul
-- := by sorry

-- theorem div_correct(x y: Partition D₀ D₁)
-- : 0 ∉ y.concrete → x.concrete / y.concrete ≤ (x.div y).concrete
-- := by sorry

-- theorem refine_correct (ord : CompareOp) (x y: Partition D₀ D₁)
-- : (x.refine ord y).1.concrete ⊆ { e |
--   e ∈ x.concrete ∧
--   (∃ e' ∈ y.concrete, ord.toProp e e') }
-- := by sorry

theorem rand_correctness (l? r?: Option Int)
: { e | (∀ l ∈ l?, l ≤ e) ∧ (∀ r ∈ r?, e ≤ r)} ⊆ (ValueDomain.rand l? r? : Sign).concrete
:= by sorry

end Correctness