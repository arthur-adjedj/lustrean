import Lustrean.Domain.NonRelational

namespace Lustrean.Domain

inductive Sign where
 | bot
 | top
 | zero
 | pos
 | neg
 | nonZero
 | zeroNeg
 | zeroPos
 deriving DecidableEq, Repr, Inhabited

def Sign.toPred(s: Sign): Int → Prop := λ x ↦ match s with
| .bot => False
| .top => True
| .zero => x = 0
| .pos  => x > 0
| .neg  => x < 0
| .zeroNeg => x ≤ 0
| .zeroPos => x ≥ 0
| .nonZero => x ≠ 0

instance : ToString (Sign) where toString
| .top     => "[⊤]"
| .bot     => "[⊥]"
| .zero    => "[=0]"
| .pos     => "[>0]"
| .neg     => "[<0]"
| .nonZero => "[≠0]"
| .zeroNeg  => "[≤0]"
| .zeroPos  => "[≥0]"

@[grind =]
def Sign.incl(s1 s2: Sign): Prop := (s1 = s2) ∨
match s1, s2 with
| .bot, _
| _, .top
| .zero, .zeroNeg
| .zero, .zeroPos
| .neg,  .zeroNeg
| .pos,  .zeroPos
| .neg,  .nonZero
| .pos,  .nonZero => True
| _, _ => False

instance: DecidableRel (Sign.incl) := by
  intros x y
  if h: x = y then simp [Sign.incl, h]; apply isTrue; simp
  else
    simp [Sign.incl, h]
    have hT: Decidable True := isTrue True.intro
    have hF: Decidable False := isFalse id
    split
    all_goals (first| exact hT | exact hF)

def Sign.join (x y: Sign):=
  if x.incl y then y else
  if y.incl x then x else
  match x, y with
  | .pos, .neg
  | .neg, .pos => .nonZero
  | .zero, .pos
  | .pos, .zero => .zeroPos
  | .zero, .neg
  | .neg, .zero => .zeroNeg
  | _, _ => .top

instance: Add (Sign) where
  add
  | .bot, _ => .bot
  | _, .bot => .bot
  /- 0 is neutral -/
  | .zero, x | x, .zero => x
  | x, y => if x = y then x else .bot

instance: Neg (Sign) where
  neg
  | .bot => .bot
  | .top => .top
  | .zero => .zero
  | .pos => .neg
  | .neg => .pos
  | .nonZero => .nonZero
  | .zeroNeg => .zeroPos
  | .zeroPos => .zeroNeg

-- Mul α
-- Sub α
-- Div α



def Sign.join_comm {x y: Sign}
: x.join y = y.join x
:= by cases x <;> cases y <;> simp [Sign.join, Sign.incl]

def Sign.incl_correct {x y: Sign}
: x.incl y -> ∀ z, x.toPred z → y.toPred z
:= by
  intros x_y z x_z
  unfold Sign.incl at x_y
  if h:x = y then
    subst y; assumption
  else
    simp [h] at x_y
    split at x_y <;> try simp [Sign.toPred] at * <;> grind

def Sign.incl_complete {x y: Sign}
: (∀ z, x.toPred z → y.toPred z) → x.incl y
:= by
  intros imp
  unfold Sign.incl
  if h:x = y then
    subst y; simp
  else
    simp [h]
    split
    /- TODO: This one is annoying -/
    all_goals sorry

theorem Sign.incl_join(x y : Sign)
: x.incl (x.join y)
:= by
  cases x <;> cases y <;> simp [Sign.incl, Sign.join]

theorem Sign.join_correct {x y: Sign}
: forall z, (x.join y).toPred z ↔ x.toPred z ∨ y.toPred z
:= by
  intros z
  constructor
  · intros z_xy
    cases x <;> cases y <;> simp [Sign.join, Sign.incl, Sign.toPred] at z_xy ⊢ <;> grind
  · rintro (h | h)
    · have h := Sign.incl_correct <| Sign.incl_join x y
      apply h
      assumption
    · have h := Sign.incl_correct <| (Sign.join_comm ▸ (Sign.incl_join y x))
      apply h
      assumption

def Sign.meet (x y: Sign):=
  if x.incl y then x else
  if y.incl x then y else
  match x, y with
  | .zeroPos, .zeroNeg
  | .zeroNeg, .zeroPos => .zero
  | .nonZero, .zeroPos
  | .zeroPos, .nonZero => .pos
  | .nonZero, .zeroNeg
  | .zeroNeg, .nonZero => .neg
  | _, _ => .bot

def Sign.meet_comm {x y: Sign}
: x.meet y = y.meet x
:= by cases x <;> cases y <;> simp [Sign.incl, Sign.meet]

theorem Sign.meet_incl(x y : Sign)
: (x.meet y).incl x
:= by cases x <;> cases y <;> simp [Sign.incl, Sign.meet]

theorem Sign.meet_correct (x y: Sign)
: forall z, (x.meet y).toPred z ↔ x.toPred z ∧ y.toPred z
:= by
  intros z
  constructor
  · intros z_xy
    constructor
    · apply Sign.incl_correct (Sign.meet_incl x y); assumption
    · apply Sign.incl_correct (Sign.meet_comm ▸ (Sign.meet_incl y x)); assumption
  · rintro h
    cases x <;> cases y <;> simp [Sign.meet, Sign.incl, Sign.toPred] at h ⊢ <;> grind

theorem Sign.incl_antisymm(x y: Sign)
: x.incl y -> y.incl x -> x = y
:= by
  intros h h2
  cases x <;> cases y <;> simp [Sign.incl] at h h2 <;> rfl

instance: BoundedLattice (Sign) where
  bot := .bot
  top := .top

  join := Sign.join
  meet := Sign.meet

  join_commutative := by apply Sign.join_comm

  join_associative := by
    intros x y z

    sorry

  meet_commutative := by apply Sign.meet_comm

-- BoundedLattice α
-- WidenLawful α
-- NarrowLawful α
