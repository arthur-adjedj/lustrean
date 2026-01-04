import Lustrean.Domain.NonRelational
import Lustrean.Domain.GaloisConnection
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace Lustrean

section Auxiliary -- TODO: Move to some other file? Find replacements?

attribute [grind =] Std.compare_self

@[grind =] theorem ex_lt (a b: Int )
: a < b → compare a b = .lt := @Int.compare_eq_lt a b |>.mpr

@[grind =] theorem ex_gt (a b: Int )
: a > b → compare a b = .gt := @Int.compare_eq_gt a b |>.mpr

open Pointwise in
@[grind =] theorem ex_Set_lt: ∀ (X Y: Set Int), (X ≤ Y) = (X ⊆ Y) := by simp

theorem aux {x y: Int}
: x * y < 0 → x > 0 ∧ y < 0 ∨ x < 0 ∧ y > 0
:= by
  intros h
  if c: x > 0 then
    have := Int.neg_of_mul_neg_right h c
    grind
  else
    have c: x < 0 := by grind
    have := Int.pos_of_mul_neg_right h c
    grind

theorem aux2 {x y: Int}
: x * y > 0 → x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0
:= by
  intros h
  if c: x > 0 then
    have := Int.pos_of_mul_pos_right h c
    grind
  else
    have c: x < 0 := by grind
    have := Int.neg_of_mul_pos_right h c
    grind

theorem Int.mul_neg_of_div_neg {x y: Int}
: x / y < 0 → x * y < 0
:= by
  intros h
  rw [←Int.sign_neg_iff, Int.sign_ediv] at h
  split at h
  · simp only [lt_self_iff_false] at h
  rw [←Int.sign_neg_iff, Int.sign_mul]
  assumption

theorem aux3{x y: Int}(h: x / y < 0)
: x > 0 ∧ y < 0 ∨ x < 0 ∧ y > 0
:= (aux ∘ Int.mul_neg_of_div_neg) h

theorem Int.mul_pos_of_div_pos {x y: Int}
: x / y > 0 → x * y > 0
:= by
  intros h
  simp only [gt_iff_lt] at *
  rw [←Int.sign_pos_iff, Int.sign_ediv] at h
  split at h
  · simp only [lt_self_iff_false] at h
  rw [←Int.sign_pos_iff, Int.sign_mul]
  assumption

theorem aux4{x y: Int}(h: x / y > 0)
: x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0
:= (aux2 ∘ Int.mul_pos_of_div_pos) h

end Auxiliary

/-- Abstraction over sets of integers. The only
 information retained is the sign of the elements
 of the set.  -/
structure Sign where mk ::
 hasPos: Bool  := false
 hasZero: Bool := false
 hasNeg: Bool  := false
 deriving DecidableEq, Repr, Inhabited

namespace Sign
/-- Seeing elements in `Sign` as a set, the opposite -/
@[grind]
def opposite(s: Sign): Sign where
  hasZero := ! s.hasZero
  hasPos  := ! s.hasPos
  hasNeg  := ! s.hasNeg

/-  We name all elements of the type.  -/
section elements
@[grind] def None: Sign := {}
@[grind] def Zero: Sign := {hasZero := true}
@[grind] def Pos: Sign := {hasPos := true}
@[grind] def Neg: Sign := {hasNeg := true}
@[grind] def NonZero: Sign := Zero.opposite
@[grind] def ZeroPos: Sign := Neg.opposite
@[grind] def ZeroNeg: Sign := Pos.opposite
@[grind] def All: Sign := None.opposite
end elements

instance: Std.ToFormat Sign where format := fun
|.mk false false  false => "[⊥]"
|.mk false false  true  => "[<0]"
|.mk false true   false => "[=0]"
|.mk true  false  false => "[>0]"
|.mk false true   true  => "[≤0]"
|.mk true  false  true  => "[≠0]"
|.mk true  true   false => "[≥0]"
|.mk true  true   true  => "[⊤]"
instance: ToString Sign := ⟨toString ∘ Std.format⟩
instance: Repr Sign := ⟨fun a _ => Std.format a⟩

namespace Notation
scoped notation "[⊥]" => Sign.None
scoped notation "[⊤]" => Sign.All
scoped notation "[=0]" => Sign.Zero
scoped notation "[>0]" => Sign.Pos
scoped notation "[<0]" => Sign.Neg
scoped notation "[≥0]" => Sign.ZeroPos
scoped notation "[≤0]" => Sign.ZeroNeg
end Notation

def join(a b: Sign): Sign where
  hasZero := a.hasZero || b.hasZero
  hasPos  := a.hasPos  || b.hasPos
  hasNeg  := a.hasNeg  || b.hasNeg

def meet(a b: Sign): Sign where
  hasZero := a.hasZero && b.hasZero
  hasPos  := a.hasPos  && b.hasPos
  hasNeg  := a.hasNeg  && b.hasNeg

def add(a b : Sign): Sign :=
  if a = .None ∨ b = .None then
    .None
  else
    {
      hasZero := a.hasZero && b.hasZero ||
                 a.hasNeg  && b.hasPos  ||
                 a.hasPos  && b.hasNeg
      -- Safe since we assume the other is non-empty
      hasPos  := a.hasPos  || b.hasPos
      -- Safe since we assume the other is non-empty
      hasNeg  := a.hasNeg  || b.hasNeg
    }

def neg(a: Sign): Sign := {
  a with
  hasNeg := a.hasPos
  hasPos := a.hasNeg
}

def sub(a b: Sign): Sign :=
  a.add b.neg

def mul (a b: Sign): Sign :=
    {
      hasPos  := a.hasPos && b.hasPos ||
                 a.hasNeg && b.hasNeg
      hasZero := a.hasZero || b.hasZero,
      hasNeg  := a.hasNeg && b.hasPos ||
                 a.hasPos && b.hasNeg
    }

def div(a b: Sign): Sign :=
  if b = .Zero then
    .None
  else {
    -- NOTE: Since we're working with integers, the sign of a division
    -- may be zero even if both of its components are not. It suffices
    -- that the denominator is big enough.
    hasZero := a ≠ .None && b ≠ .None,
    hasPos  := a.hasPos && b.hasPos ||
               a.hasNeg && b.hasNeg
    hasNeg  := a.hasNeg && b.hasPos ||
               a.hasPos && b.hasNeg
  }

@[grind]
def incl(a b: Sign): Bool :=
  !(a.hasZero && !b.hasZero) &&
  !(a.hasPos  && !b.hasPos ) &&
  !(a.hasNeg  && !b.hasNeg )

/-- Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e ≤ e' -/
def refineLE: Sign → Sign → Sign
| ⟨p,z,n⟩, ⟨true, _, _⟩          => ⟨p,z,n⟩
| ⟨_,z,n⟩, ⟨false, true, _⟩      => ⟨false, z, n⟩
| ⟨_,_,n⟩, ⟨false, false, true⟩  => ⟨false,false,n⟩
| ⟨_,_,_⟩, ⟨false, false, false⟩ => ⟨false,false,false⟩

/--
  Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e ≥ e'

  The operation is defined in terms of `refineLE` to reduce the burden
  of proofs. Intuitively, this works well because `neg` is a perfect
  abstraction.
-/
abbrev refineGE(x y: Sign): Sign := x.neg.refineLE y.neg |>.neg

/-- Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e < e' -/
def refineLT: Sign → Sign → Sign
| ⟨p,z,n⟩, ⟨true, _, _⟩          => ⟨p,z,n⟩
| ⟨_,_,n⟩, ⟨false, true, _⟩      => ⟨false, false, n⟩
-- Again, one cannot be perfect for LT here, since we could have e ∈ x' st e < 0
-- but this doesn't imply there is some e' ∈ y such that e < e'.  We need to
-- make an overapproximation
| ⟨_,_,_⟩, ⟨false, false, _⟩  => ⟨false,false,false⟩

/--
  Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e ≥ e'

  The operation is defined in terms of `refineLT` to reduce the burden
  of proofs. Intuitively, this works well because `neg` is a perfect
  abstraction.
-/
abbrev refineGT(x y: Sign): Sign := x.neg.refineLT y.neg |>.neg

/-- Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e = e' -/
def refineEQ(x y: Sign): Sign := x.meet y

/-- Given x and y, return x' such that ∀ e ∈ x', e ∈ x ∧ ∃ e' ∈ y, e ≠ e' -/
def refineNE(x y: Sign): Sign := {
  hasPos  := x.hasPos && y ≠ .None -- Pick of different sign or higher
  hasZero := x.hasZero && (y.hasPos || y.hasNeg)
  hasNeg  := x.hasNeg && y ≠ .None -- Pick of different sign or lower
}

/--
  Given x and y and some binary comparison op, returns the restrictions
  x' and y' of x and y of elements for which the comparison may hold.
-/
def refine (op: Lustrean.CompareOp) (x y: Sign): Sign × Sign := match op with
  | .eq  => (x.refineEQ y, y.refineEQ x)
  | .lt  => (x.refineLT y, y.refineGT x)
  | .neq => (x.refineNE y, y.refineNE x)
  | .le  => (x.refineLE y, y.refineGE x)
  | .ge  => (x.refineGE y, y.refineLE x)
  | .gt  => (x.refineGT y, y.refineLT x)

end Sign

instance: Add Sign := .mk Sign.add
instance: Mul Sign := .mk Sign.mul
instance: Neg Sign := .mk Sign.neg
instance: Sub Sign := .mk Sign.sub
instance: Div Sign := .mk Sign.div
instance: Widen Sign  where widen a b _ := a.join b
instance: Narrow Sign where narrow a b _ := a.meet b

section GaloisEmbedding
namespace Sign

/-! Inclusion of Sign elements establishes a partial order -/

@[grind =]
instance instLE: LE Sign where
  le x y := Sign.incl x y = true

@[grind]
instance instPartialOrderSign: PartialOrder Sign where
  le_refl := by simp [LE.le, Sign.incl]
  le_trans := by
    intros; simp only [LE.le] at *; grind [Sign.incl]
  le_antisymm := by
    rintro ⟨z1,p1,n1⟩ ⟨x2,p2,n2⟩ ab bc
    simp only [LE.le, incl, Bool.not_and, Bool.not_not, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, mk.injEq] at *
    grind

open Classical in
/--
  Abstraction of a set of integers by `Sign` (which only captures
  its element's signature (<0,=0,>0) information)

  Since we make no assumption of whether our sets are decidable or
  not, we must use the axiom of choice to decide the conditions
  `∃ z ∈ X, z > 0` and `∃ z ∈ X, z > 0`. This makes our abstract
  function noncomputable, but it is acceptable since we only make
  use of it to prove theorems about our operators.
-/
@[grind =]
noncomputable def abstract(X: Set Int): Sign := {
      hasZero := 0 ∈ X
      hasPos := ∃ z ∈ X, z > 0
      hasNeg := ∃ z ∈ X, z < 0
}

/-- The integer set represented by a particular `Sign` element -/
@[grind =]
def concrete(a: Sign): Set Int := setOf λ z ↦
  match compare z 0 with
  | .lt => a.hasNeg
  | .eq => a.hasZero
  | .gt => a.hasPos

/--
  There is a Galois embedding between the Sign domain and the
  Integers subset domain.
-/
def gc: GaloisConnection Sign.abstract Sign.concrete := by
    rintro X ⟨p,z,n⟩
    constructor <;> grind (splits := 10) [LE.le]

-- TODO: It'd be nice if there was a simproc that propagated
-- equalities down `match` statements.

noncomputable
instance ge: GaloisEmbedding abstract concrete := gc.toGaloisInsertion <| by
  rintro ⟨hasPos, z, hasNeg⟩
  simp [Sign.abstract, Sign.concrete, LE.le, Sign.incl]
  apply And.intro
  · if h: hasPos then apply Or.inr; exists 1  else grind
  · if h: hasNeg then apply Or.inr; exists -1 else grind

end Sign
end GaloisEmbedding

section Theorems
namespace Sign

theorem join_commutative(a b: Sign): a.join b = b.join a := by
  have h: ∀ (a b: Sign), a.join b ≤ b.join a := by
    intros a b
    apply Sign.ge.u_le_u_iff.mp
    intros x
    grind [Sign.join]
  grind [Std.IsPartialOrder.le_antisymm]

theorem join_associative (a b c: Sign): (a.join b).join c = a.join (b.join c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals (
    apply Sign.ge.u_le_u_iff.mp
    intros p
    grind [Sign.join]
  )

theorem meet_commutative(a b: Sign): a.meet b = b.meet a := by
  have h: ∀ (a b: Sign), a.meet b ≤ b.meet a := by
    intros a b
    apply Sign.ge.u_le_u_iff.mp
    intros x
    grind [Sign.meet]
  grind [Std.IsPartialOrder.le_antisymm]

theorem meet_associative(a b c: Sign): (a.meet b).meet c = a.meet (b.meet c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals(
    apply Sign.ge.u_le_u_iff.mp
    intros p
    grind [Sign.meet]
  )

theorem join_absorption: ∀ (x y: Sign), x.join (x.meet y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  grind [join, meet, mk.injEq, Bool.or_eq_left_iff_imp]

theorem meet_absorption: ∀ (x y: Sign), x.meet (x.join y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  grind [meet, join, mk.injEq, Bool.and_eq_left_iff_imp]

end Sign
end Theorems

instance: BoundedLattice Sign where
  bot := .None
  top := .All
  join := Sign.join
  meet := Sign.meet
  join_bot := by simp [Sign.None, Sign.join]
  join_top := by simp [Sign.All, Sign.None, Sign.opposite,  Sign.join]
  meet_bot := by simp [Sign.None, Sign.meet]
  meet_top := by simp [Sign.All, Sign.None, Sign.opposite, Sign.meet]
  -- non_trivial := by decide
  join_commutative := Sign.join_commutative
  join_associative := Sign.join_associative
  meet_commutative := Sign.meet_commutative
  meet_associative := Sign.meet_associative
  join_absorption  := Sign.join_absorption
  meet_absorption  := Sign.meet_absorption

instance: WidenLawful Sign where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_left := by
    rintro x y -
    simp [BoundedLattice.IsSubset, Widen.widen]
    rewrite [Sign.meet_absorption]
    rfl

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  covering_right := by
    rintro x y -
    simp [BoundedLattice.IsSubset, Widen.widen]
    rewrite [Sign.join_commutative, Sign.meet_absorption]
    rfl

instance: NarrowLawful Sign where
  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_high := by
    rintro ⟨z,p,n⟩ ⟨z',p',n'⟩ -
    simp [BoundedLattice.IsSubset, Narrow.narrow]
    grind [Sign.meet]

  /- NOTE: These theorems are inlined since they depend on
     definitions introduced by the `BoundedLattice` typeclass -/
  bounding_low := by
    simp [BoundedLattice.IsSubset, Narrow.narrow]
    grind [Sign.meet]

instance: ValueDomain Sign where
  nil := .All

  compare op x y := Sign.refine op x y

  -- We interpret `None` as if it were ±∞
  rand := fun
  | .some l, .some r =>
    if l ≤ r then
      {
        hasZero := l ≤ 0 ∧ 0 ≤ r,
        hasPos := 0 < r,
        hasNeg := l < 0
      }
    else .None
  | .none, .none => .All
  | .none, .some r =>
    {
      hasZero := 0 ≤ r,
      hasPos := 0 < r,
      hasNeg := true
    }
  | .some l, .none =>
    {
      hasZero := l ≤ 0,
      hasPos := true,
      hasNeg := l < 0
    }

section Correctness
namespace Sign
open Pointwise -- For operations on Sets

/-!
  Note that most operators are not complete. For instance, consider the
  add function. We have `[<0] + [<0] = [<0]`.
-/
#eval open Sign.Notation in [<0] + [<0]
/-!
  However, in our concrete domain we can deduce something stronger. Consider
  when `-1 ∈ γ ([<0] + [<0])`, however `-1 ∉ (γ[<0] + γ[<0])`. This is because
  -1 cannot be obtained from the sum of two negative integers. Therefore,
  `γ ([<0] + [<0]) ⊄ (γ[<0] + γ[<0])`
-/

theorem add_correct
: Sign.gc.IsBinAbstraction (· + ·) Sign.add
:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  if h: ⟨z,p,n⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp only [Sign.add, Sign.None, Sign.concrete, HAdd.hAdd, Set.add]
    grind
  else if h: ⟨z',p',n'⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp only [HAdd.hAdd, Set.add, concrete, Set.mem_image2, Set.mem_setOf_eq,
      add, None, mk.injEq]
    grind
  else
  intros e
  simp only [Set.add, Sign.add]
  rintro ⟨e1,x_e1, e2, y_e2, e1_e2⟩
  cases com_e: compare e 0 <;>
  simp only [Int.compare_eq_eq, Int.compare_eq_lt, Int.compare_eq_gt] at com_e <;>
  simp [ Sign.concrete, * ] at x_e1 y_e2 ⊢ <;> grind

def neg_complete
: Sign.gc.IsBestAbstraction (-·) Sign.neg
:= by
  intros x
  simp only [Neg.neg, Sign.concrete, Set.preimage_setOf_eq, Sign.neg]
  grind [Sign.neg, Sign.concrete]
-- grind_pattern neg_complete => a.neg.concrete

@[grind =] -- The grind attribute does not go through `abbrev`s?
theorem concrete_neg (a: Sign): a.neg.concrete = -a.concrete := neg_complete a |>.symm

-- TODO: Consider how one can define theorems about
-- composing abstractions (probably should live in GaloisConnection)
theorem sub_correct
: Sign.gc.IsBinAbstraction (· - ·) Sign.sub
:= by
  intros x y
  simp only [Sign.sub, LE.le]
  calc
    _ ⊆ (x.concrete + y.neg.concrete) := by
      -- TODO: Make grind reason over these
      simp [←neg_complete]
      simp only [HSub.hSub, Sub.sub, Set.image2, Int.sub]
      simp only [HAdd.hAdd, Add.add, Set.image2]
      intros e; simp only [Int.add_def, Set.mem_setOf_eq, Set.mem_neg, forall_exists_index, and_imp]
      intros e1 e1_x e2 e2_y e1_e2
      refine ⟨e1, e1_x, (-e2), ?_⟩
      simp [*]
    _ ⊆ _ := by
      apply add_correct

theorem mul_correct
: Sign.gc.IsBinAbstraction (· * ·) Sign.mul
:= by
  intros x y e h
  simp only [Sign.concrete, Set.mem_mul, Set.mem_setOf_eq] at h
  obtain ⟨e1, e1_x, e2, e2_y, e1_e2⟩ := h --
  unfold Sign.mul
  simp only [Sign.concrete, Bool.or_eq_true, Bool.and_eq_true,
  Set.mem_setOf_eq] at *
  split
  · have disj: e1 > 0 ∧ e2 < 0 ∨ e2 > 0 ∧ e1 < 0 := by grind [
      aux,
      Int.neg_of_mul_neg_right,
      Int.pos_of_mul_neg_right
    ]
    cases disj <;> grind
  · have disj: e1 = 0 ∨ e2 = 0 := by grind [Int.eq_zero_or_eq_zero_of_mul_eq_zero]
    cases disj <;> grind
  · have disj: e1 > 0 ∧ e2 > 0 ∨ e1 < 0 ∧ e2 < 0 := by grind [aux2]
    cases disj <;> grind

-- Since in Lean we have x / 0 = 0, we need to state the correctness
-- of Sign.div under the assumption that `¬ y.hasZero`, since in this
-- case, our operation differs from that of Lean.
theorem div_correct(x y: Sign)
: ¬ y.hasZero → x.concrete / y.concrete ≤ (x.div y).concrete
:= by
  intros y_ne0 e h
  simp only [Sign.concrete, Set.mem_div, Set.mem_setOf_eq] at h
  obtain ⟨e1, e1_x, e2, e2_x, e1_e2⟩ := h
  fun_cases (x.div y)
  · grind [Sign.None, Sign.Zero]
  · simp only [Sign.Zero, Sign.concrete, Bool.or_eq_true, Bool.and_eq_true,
    Set.mem_setOf_eq] at *
    split
    · have disj: e1 > 0 ∧ e2 < 0 ∨ e2 > 0 ∧ e1 < 0 := by grind [aux3]
      cases disj <;> grind
    · grind [Sign.None]
    · have disj: e1 > 0 ∧ e2 > 0 ∨ e1 < 0 ∧ e2 < 0 := by grind [aux4]
      cases disj <;> grind

theorem refineLT_correct (x y: Sign)
: (x.refineLT y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e < e') }
:= by
  fun_cases (x.refineLT y)
  · intros e h; refine ⟨h, ?_⟩
    exists (if e <= 0 then 1 else e+1)
    grind
  · intros e h; constructor
    · grind
    · exists 0; grind
  · grind

theorem refineGT_correct (x y: Sign)
: (x.refineGT y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e > e') }
:= by
  have := refineLT_correct x.neg y.neg
  intro e
  specialize @this (-e)
  grind [Set.mem_neg]

theorem refineLE_correct (x y: Sign)
: (x.refineLE y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e ≤ e') }
:= by
  fun_cases (x.refineLE y)
  · intros e h; refine ⟨h, ?_⟩
    exists (if e <= 0 then 1 else e+1)
    grind
  · intros e h; constructor
    · grind
    · exists 0; grind
  all_goals grind

theorem refineGE_correct (x y: Sign)
: (x.refineGE y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e ≥ e') }
:= by
  have := refineLE_correct x.neg y.neg
  intro e
  specialize @this (-e)
  grind [Set.mem_neg]

theorem refineEQ_correct (x y: Sign)
: (x.refineEQ y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e = e') }
:= by grind [Sign.refineEQ, Sign.meet]

-- TODO: Golf
theorem refineNE_correct (x y: Sign)
: (x.refineNE y).concrete ⊆ { e |
   e ∈ x.concrete ∧
   (∃ e' ∈ y.concrete, e ≠ e') }
:= by
  obtain ⟨p,z,n⟩ := x
  obtain ⟨p',z',n'⟩ := y
  simp only [Sign.None, Sign.refineNE]
  intros e
  cases comp_e: compare e 0
  · intros h
    constructor
    · grind
    · exists (if p' then 1 else if z' then 0 else e - 1)
      grind
  · intros h; constructor
    · grind
    · exists (if p' then 1 else -1)
      grind
  · intros h
    constructor
    · grind
    · exists (if p' then e+1 else if z' then 0 else -1)
      simp only [Sign.concrete, Set.mem_setOf_eq] at *
      grind

theorem refine_1_correct (ord: CompareOp)(x y: Sign)
: (x.refine ord y).1.concrete ⊆ { e |
  e ∈ x.concrete ∧
  (∃ e' ∈ y.concrete, ord.toProp e e') }
:= by
  fun_cases (x.refine ord y) <;> simp only [CompareOp.toProp]
  · grind [refineEQ_correct]
  · grind [refineLT_correct]
  · grind [refineNE_correct]
  · grind [refineLE_correct]
  · grind [refineGE_correct]
  · grind [refineGT_correct]

theorem refine_2_correct (ord: CompareOp)(x y: Sign)
: (x.refine ord y).2.concrete ⊆ { e' |
  e' ∈ y.concrete ∧
  (∃ e ∈ x.concrete, ord.toProp e e') }
:= by
  fun_cases (x.refine ord y) <;> simp only [CompareOp.toProp] <;> intros e h
  · grind [refineEQ_correct]
  · grind [refineGT_correct]
  · grind [refineNE_correct]
  · grind [refineGE_correct]
  · grind [refineLE_correct]
  · grind [refineLT_correct]

theorem rand_correctness (l? r?: Option Int)
: { e | (∀ l ∈ l?, l ≤ e) ∧ (∀ r ∈ r?, e ≤ r)} ⊆ (ValueDomain.rand l? r? : Sign).concrete
:= by
  simp only [ValueDomain.rand, Option.mem_def]
  grind

end Sign
end Correctness
