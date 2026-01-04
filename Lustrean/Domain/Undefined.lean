import Lustrean.Domain.NonRelational

namespace Lustrean
structure Undefined (α : Type) : Type where
  val : α
  may_be_nil : Bool
  deriving Repr, Inhabited, DecidableEq, BEq

namespace Undefined
variable {α : Type} [BEq α][ι : ValueDomain α] (x y z : Undefined α)

protected def add : Undefined α := .mk (x.val + y.val) (x.may_be_nil || y.may_be_nil)
protected def neg : Undefined α := .mk (-x.val) (x.may_be_nil)
protected def sub : Undefined α := .mk (x.val - y.val) (x.may_be_nil || y.may_be_nil)
protected def mul : Undefined α := .mk (x.val * y.val) (x.may_be_nil || y.may_be_nil)
protected def div : Undefined α := .mk (x.val / y.val) (x.may_be_nil || y.may_be_nil)

instance : Add (Undefined α) where
  add := Undefined.add
instance : Neg (Undefined α) where
  neg := Undefined.neg
instance : Sub (Undefined α) where
  sub := Undefined.sub
instance : Mul (Undefined α) where
  mul := Undefined.mul
instance : Div (Undefined α) where
  div := Undefined.div

protected def toString := if x.may_be_nil then s!"{x.val} ⊔ nil"
  else toString x.val

instance : ToString (Undefined α) where
  toString := Undefined.toString

def bot : Undefined α := .mk ⊥ false
def top : Undefined α := .mk ⊤ true
def meet : Undefined α := .mk (x.val ⊓ y.val) (x.may_be_nil && y.may_be_nil)
def join : Undefined α := .mk (x.val ⊔ y.val) (x.may_be_nil || y.may_be_nil)

theorem join_commutative : join x y = join y x := by
  simp [join]
  simp [BoundedLattice.join_commutative, Bool.or_comm]

theorem join_associative : join (join x y) z = join x (join y z) := by
  simp [join]
  simp [Bool.or_assoc]


theorem join_absorption : x.join (x.meet y) = x := by
  simp [join, meet]
  cases x ; cases y.may_be_nil <;> simp

theorem join_bot : join x bot = x := by
  simp [join, bot]

theorem join_top : join x top = top := by
  simp [join, top]

theorem meet_commutative : meet x y = meet y x := by
  simp [meet]
  simp [BoundedLattice.meet_commutative, Bool.and_comm]

theorem meet_associative : meet (meet x y) z = meet x (meet y z) := by
  simp [meet]
  simp [Bool.and_assoc]

theorem meet_absorption : x.meet (x.join y) = x := by
  simp [meet, join]
  cases x ; cases y.may_be_nil <;> simp

theorem meet_top : meet x top = x := by
  simp [meet, top]

theorem meet_bot : meet x bot = bot := by
  simp [meet, bot]

theorem non_trivial : Undefined.top ≠ (bot : Undefined α) := by
  simp [top, bot]

instance : BoundedLattice (Undefined α) where
  bot := bot
  top := top
  meet := meet
  join := join
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

def widen (n : Nat) : Undefined α :=
  .mk (ι.widen x.val y.val n) (x.may_be_nil || y.may_be_nil)

def narrow (n : Nat) : Undefined α :=
  .mk (ι.narrow x.val y.val n) (x.may_be_nil && y.may_be_nil)

instance : Widen (Undefined α) where
  widen := widen

instance : Narrow (Undefined α) where
  narrow := narrow

instance : WidenLawful (Undefined α) where
  covering_left := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Widen.widen, widen, meet]
    constructor
    · apply WidenLawful.covering_left
    · intros ; left ; assumption
  covering_right := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Widen.widen, widen, meet]
    constructor
    · apply WidenLawful.covering_right
    · intros ; right ; assumption

instance : NarrowLawful (Undefined α) where
  bounding_low := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Narrow.narrow, narrow, meet]
    rw [← ι.meet_associative]
    apply NarrowLawful.bounding_low
  bounding_high := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Narrow.narrow, narrow, meet]
    constructor
    · apply NarrowLawful.bounding_high
    · intros ; assumption


def compare (op : CompareOp) (x y : Undefined α) :
  Undefined α × Undefined α :=
  let (x', y') := ι.compare op x.val y.val
  (.mk x' x.may_be_nil, .mk y' y.may_be_nil)

instance : ValueDomain (Undefined α) where
  rand a b := .mk (ι.rand a b) false
  nil := .mk ⊥ true
  compare := compare
  covering_left := WidenLawful.covering_left
  covering_right := WidenLawful.covering_right
  dec_bot := by
    have := ι.dec_bot
    rintro ⟨x,nil?⟩
    simp [Undefined.bot, Lustrean.bot]
    infer_instance

  bounding_low := NarrowLawful.bounding_low
  bounding_high := NarrowLawful.bounding_high
end Undefined
end Lustrean
