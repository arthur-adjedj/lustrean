import Lustrean.Domain.NonRelational
-- import Lustrean.Domain.GaloisConnection
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.Defs.PartialOrder

namespace Lustrean.Domain

-- TODO: Fix up
attribute [local simp] Int.compare_eq_gt Int.compare_eq_lt

private def Int.compare_eq_of_lt a b := @Int.compare_eq_lt a b  |>.mpr
local grind_pattern Int.compare_eq_of_lt => compare a b, a + 1 ≤ b
-- TODO: Consider if using a+1 ≤ b is required, instead of a < b

local grind_pattern Std.compare_self => compare a a

private def Int.compare_eq_of_gt a b := @Int.compare_eq_gt a b  |>.mpr
local grind_pattern Int.compare_eq_of_gt => compare a b, b + 1 ≤ a
-- TODO: Consider if using b+1 ≤ a is required, instead of a > b


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
def opposite(s: Sign): Sign where
  hasZero := ! s.hasZero
  hasPos := ! s.hasPos
  hasNeg := ! s.hasNeg

/-  We name all elements of the type.  -/
section elements
def None: Sign := {}
def Zero: Sign := {hasZero := true}
def Pos: Sign := {hasPos := true}
def Neg: Sign := {hasNeg := true}
def NonZero: Sign := Zero.opposite
def ZeroPos: Sign := Neg.opposite
def ZeroNeg: Sign := Pos.opposite
def All: Sign := None.opposite
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

def mul(a b : Sign): Sign :=
  if a = .Zero ∨ b = .Zero then
    .Zero
  else
    {
      hasZero := a.hasZero || b.hasZero,
      hasPos  := a.hasPos && b.hasPos || a.hasNeg && b.hasNeg
      hasNeg  := a.hasNeg && b.hasPos || b.hasNeg && b.hasPos
    }

def neg(a: Sign): Sign := {
  a with
  hasNeg := a.hasPos
  hasPos := a.hasNeg
}

def sub(a b: Sign): Sign :=
  a.add b.neg

def div(a b: Sign): Sign :=
  if b = .Zero then
    .None
  else {
    hasZero := a.hasZero,
    hasPos  := a.hasPos && b.hasPos || a.hasNeg && b.hasNeg
    hasNeg  := a.hasNeg && b.hasPos || b.hasNeg && b.hasPos
  }

def incl(a b: Sign): Bool :=
  !(a.hasZero && !b.hasZero) &&
  !(a.hasPos  && !b.hasPos ) &&
  !(a.hasNeg  && !b.hasNeg )

/- TODO: Improve -/
def restrictLE: Sign → Sign → Sign
| ⟨p,z,n⟩, ⟨true, _, _⟩          => ⟨p,z,n⟩
| ⟨_,z,n⟩, ⟨false, true, _⟩      => ⟨false, z, n⟩
-- Again, one cannot be perfect for LT here, since we could have e ∈ x' st e < 0
-- but this doesn't imply there is some e' ∈ y such that e < e'.  We need to
-- make an overapproximation
| ⟨_,_,n⟩, ⟨false, false, true⟩  => ⟨false,false,n⟩
| ⟨_,_,_⟩, ⟨false, false, false⟩ => ⟨false,false,false⟩

def restrictLT: Sign → Sign → Sign
| ⟨p,z,n⟩, ⟨true, _, _⟩          => ⟨p,z,n⟩
| ⟨_,_,n⟩, ⟨false, true, _⟩      => ⟨false, false, n⟩
-- Again, one cannot be perfect for LT here, since we could have e ∈ x' st e < 0
-- but this doesn't imply there is some e' ∈ y such that e < e'.  We need to
-- make an overapproximation
| ⟨_,_,_⟩, ⟨false, false, _⟩  => ⟨false,false,false⟩

-- TODO: Fix
def restrict(ord: Ordering)(x y: Sign): Sign := match ord with
| .lt => x.restrictLT y
| .eq => x.meet y
| .gt => x.neg.restrictLT y.neg |>.neg

-- TODO: Fix
def compare' (op: Lustrean.CompareOp) (x y: Sign): Sign × Sign := match op with
  | .eq  => (x.restrict .eq y, y.restrict .eq x)
  | .lt  => (x.restrict .lt y, y.restrict .lt x)
  | .neq => ((x.restrict .lt y).meet  (x.restrict .gt y),
             (y.restrict .lt x).meet  (y.restrict .gt x))
  | .le  => (x.restrictLE y, y.restrictLE x)
  | .ge  => compare' .le y  x
  | .gt  => compare' .lt y  x
termination_by (match op with |.ge => 2 |.le|.gt => 1 |_ => 0)

end Sign

instance: Add Sign := .mk Sign.add
instance: Mul Sign := .mk Sign.mul
instance: Neg Sign := .mk Sign.neg
instance: Sub Sign := .mk Sign.sub
instance: Div Sign := .mk Sign.div
instance: Widen Sign  where widen a b _ := a.join b
instance: Narrow Sign where narrow a b _ := a.meet b

section GaloisEmbedding
/-- The concrete domain of Sign is the set of (computable)
    subsets of integers. -/
abbrev Set α := α → Bool

/-- We establish a partial order on sets through inclusion -/
@[grind =]
instance instLESetInt: LE (Set Int) where
  le f g := ∀ x, f x -> g x
instance instPartialOrderSetInt: PartialOrder (Set Int) where
  le_refl := by intros f g a; assumption
  le_trans := by intros f g h fg gh a fa; apply (gh _ (fg a fa))
  le_antisymm := by
    intros f g fg gf
    ext x
    specialize fg x
    specialize gf x
    cases h: (f x) <;> grind

/-- Inclusion of Sign elements establishes a partial order -/
@[grind =]
instance: LE Sign where
  le x y := Sign.incl x y = true
/-- Inclusion of Sign elements establishes a partial order -/
@[grind]
instance instPartialOrderSign: PartialOrder Sign where
  le_refl := by simp [LE.le, Sign.incl]
  le_trans := by
    intros; simp [LE.le, Sign.incl] at *; grind
  le_antisymm := by
    rintro ⟨z1,p1,n1⟩ ⟨x2,p2,n2⟩ ab bc
    simp [LE.le, Sign.incl] at *
    grind

open Classical in
/-- Abstraction of a set of integers by `Sign` (which only captures
its element's signature (<0,=0,>0) information) -/
@[grind =]
noncomputable def Sign.abstract(X: Set Int): Sign := {
      hasZero := X 0
      hasPos := ∃ z, z > 0 ∧ X z
      hasNeg := ∃ z, z < 0 ∧ X z
}

/-- The integer set represented by a particular `Sign` element -/
@[grind =]
def Sign.concrete(a: Sign): Set Int := λ z ↦ match compare z 0 with
| .lt => a.hasNeg
| .eq => a.hasZero
| .gt => a.hasPos

-- /--
--   There is a Galois embedding between the Sign domain and the
--   Integers subset domain.

--   To define the abstraction function, one needs to be able to
--   determine whether a positive (resp. negative) integer is in
--   the set or not. This is generally undecidable, so we need to
--   make use of the axiom of choice. This is acceptable, since
--   we don't use the abstraction nor concretization functions in
--   our computations, just to justify the laws of operators.
-- -/
-- @[grind =]
-- noncomputable instance instGESignIntSet: GaloisEmbedding (A := Sign) (C := Set Int) where
--   concrete := Sign.concrete
--   abstract := Sign.abstract

--   connection:= by
--     rintro ⟨p,z,n⟩ X
--     constructor
--     · intros abs_lt x x_X
--       simp at *
--       simp [LE.le, Sign.incl] at abs_lt
--       cases h: compare x 0 <;> simp at h <;> grind
--     · intros conc_lt
--       simp [LE.le, Sign.incl] at ⊢
--       have h₁: ∀ a b, a = false ∨ b = true ↔ (a = true → b = true) := by
--         grind
--       simp only [h₁]
--       apply and_assoc.mpr
--       have h0 := conc_lt 0; simp at h0
--       apply And.intro
--       · grind
--       apply And.intro <;> grind [LE.le]

--   embedding := by
--     rintro ⟨p,z,n⟩
--     simp only [Sign.abstract, gt_iff_lt, Sign.concrete, Std.compare_self, Sign.mk.injEq, true_and]
--     apply And.intro
--     · cases p_def: p
--       · simp only [decide_eq_false_iff_not, not_exists, not_and, Bool.not_eq_true]; grind
--       · simp; exists 1
--     · cases n_def: n
--       · simp; grind
--       · simp; exists -1

def inst: GaloisConnection Sign.abstract Sign.concrete := by
    rintro X ⟨p,z,n⟩
    constructor
    · intros abs_lt x x_X
      simp at *
      simp [LE.le, Sign.incl] at abs_lt
      cases h: compare x 0 <;> simp at h
      · simp [Sign.abstract, Sign.concrete] at *
        set_option trace.grind.ematch.instance true in
        grind
        sorry
      · sorry
      · sorry
    · intros conc_lt
      have h₁: ∀ a b, a = false ∨ b = true ↔ (a = true → b = true) := by
        grind
      simp only [LE.le, Sign.incl, Bool.not_and, Bool.not_not, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, h₁, and_assoc] at ⊢
      clear h₁
      have h0 := conc_lt 0; simp at h0
      apply And.intro
      · grind
      apply And.intro
      · intros h
        simp [Sign.abstract] at h
        obtain ⟨z, z_pos, Xz⟩ := h
        simp only [LE.le] at conc_lt
        grind
      · intros h
        simp [Sign.abstract] at h
        obtain ⟨z, z_pos, Xz⟩ := h
        simp only [LE.le] at conc_lt
        grind

noncomputable instance: GaloisConnection (A := Sign) (C := Set Int) where


instance: GaloisInsertion Sign.concrete Sign.abstract where

end GaloisEmbedding

section theorems
namespace Sign

theorem join_commutative(a b: Sign): a.join b = b.join a := by
  have h: ∀ (a b: Sign), a.join b ≤ b.join a := by
    intros a b
    apply instGESignIntSet.lt_of_concrete_lt
    intros x
    simp [GaloisConnection.concrete, Sign.join]
    grind
  grind [Std.IsPartialOrder.le_antisymm]

theorem join_associative (a b c: Sign): (a.join b).join c = a.join (b.join c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals(
    apply instGESignIntSet.lt_of_concrete_lt
    intros p
    simp [GaloisConnection.concrete, Sign.join]
    grind
  )

theorem meet_commutative(a b: Sign): a.meet b = b.meet a := by
  have h: ∀ (a b: Sign), a.meet b ≤ b.meet a := by
    intros a b
    apply instGESignIntSet.lt_of_concrete_lt
    intros x
    simp [GaloisConnection.concrete, Sign.meet]
    grind
  grind [Std.IsPartialOrder.le_antisymm]

theorem meet_associative(a b c: Sign): (a.meet b).meet c = a.meet (b.meet c) := by
  apply Std.IsPartialOrder.le_antisymm
  all_goals(
    apply instGESignIntSet.lt_of_concrete_lt
    intros p
    simp [GaloisConnection.concrete, Sign.meet]
    grind
  )
theorem join_absorption: ∀ (x y: Sign), x.join (x.meet y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  simp [Sign.meet, Sign.join]
  grind
theorem meet_absorption: ∀ (x y: Sign), x.meet (x.join y) = x:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  simp [Sign.meet, Sign.join]
  grind

end Sign
end theorems

instance: BoundedLattice Sign where
  bot := .None
  top := .All
  join := Sign.join
  meet := Sign.meet
  join_bot := by simp [Sign.None, Sign.join]
  join_top := by simp [Sign.All, Sign.None, Sign.opposite,  Sign.join]
  meet_bot := by simp [Sign.None, Sign.meet]
  meet_top := by simp [Sign.All, Sign.None, Sign.opposite, Sign.meet]
  non_trivial := by decide
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
  /- TODO: What laws must `nil` obey? -/
  nil := .All

  /- TODO: What laws must `compare` obey?
    (x', y') st x' = {e  ∈ x : ∃e' ∈ y, e op e'}
                y' = {e' ∈ y : ∃e  ∈ x, e op e'}
  -/
  compare op x y := Sign.compare' op x y

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
      hasZero := true,
      hasPos := 0 < r,
      hasNeg := false
    }
  | .some l, .none =>
    {
      hasZero := true,
      hasPos := false,
      hasNeg := l < 0
    }

section Correctness

open Classical in
private noncomputable def Set.add(X Y: Set Int): Set Int
:= λ z ↦ ∃ x y, z = x + y ∧ X x = true ∧ Y y = true

theorem add_correct
: instGESignIntSet.IsBinAbstraction Set.add Sign.add
:= by
  rintro ⟨z,p,n⟩ ⟨z',p',n'⟩
  if h: ⟨z,p,n⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp [Sign.add, Sign.None, concrete, Set.add]
    grind
  else if h: ⟨z',p',n'⟩ = Sign.None then
    obtain ⟨rfl, rfl, rfl⟩ := h
    intros e
    simp [Sign.add, Sign.None, concrete, Set.add]
    grind
  else
  intros e
  simp only [Set.add, Sign.add, decide_eq_true_eq]
  rintro ⟨e1,e2, e1_e2, x_e1, y_e2⟩
  cases com_e: compare e 0 <;> simp only [Int.compare_eq_eq, Int.compare_eq_lt, Int.compare_eq_gt] at com_e
  all_goals (
    simp only [ concrete ] at x_e1 y_e2 ⊢
    grind
  )
  -- ADD IS NOT COMPLETE!
  -- We have [<0] + [<0] = [<0]
  #eval open Sign.Notation in
    [<0] + [<0]
  -- but if -1 ∈ γ ([<0] + [<0]) then it doesn't mean -1 ∈ (γ[<0] + γ[<0])).
  -- In particular, -1 ∈ γ(a) + γ(b) → ∃ c ≥ 0 ∈ γ(a) ∪ γ(b), since -1 cannot
  -- be obtained from the sum of two negative integers.

attribute [local grind] concrete
notation "γ" x => (concrete x: Set Int)
-- macro "concrete" x : term  => `((concrete $x: Set Int))

theorem restrictLT_correct (x y: Sign)
: ∀ e, (γ (x.restrictLT y)) e = true →
  (γ x) e = true ∧
  ∃ e',
    (γ y) e' = true ∧
    e < e'
:= by
  fun_cases (x.restrictLT y)
  · intros e h; refine ⟨h, ?_⟩
    exists (if e <= 0 then 1 else e+1)
    grind
  · intros e h; constructor
    · grind
    · exists 0; grind
  · intros e h; constructor <;> grind

theorem restrictLE_correct (x y: Sign)
: let concrete := instGESignIntSet.concrete
  ∀ e, concrete (x.restrictLE y) e = true →
  concrete x e = true ∧
  ∃ e',
    concrete y e' = true ∧
    e ≤ e'
:= by
  fun_cases (x.restrictLE y) <;>
  simp only [concrete]
  · intros e h; refine ⟨h, ?_⟩
    exists (if e <= 0 then 1 else e+1)
    grind
  · intros e h; constructor
    · grind
    · exists 0; grind
  all_goals intros e h; constructor <;> grind

end Correctness
