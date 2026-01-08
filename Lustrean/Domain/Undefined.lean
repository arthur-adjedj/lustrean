import Lustrean.Domain.NonRelational.ValueDomain

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
instance: Bot (Undefined α) where bot := bot
def top : Undefined α := .mk ⊤ true
instance: Top (Undefined α) where top := top
def meet : Undefined α := .mk (x.val ⊓ y.val) (x.may_be_nil && y.may_be_nil)
instance: Min (Undefined α) where min := meet
def join : Undefined α := .mk (x.val ⊔ y.val) (x.may_be_nil || y.may_be_nil)
instance: Max (Undefined α) where max := join

theorem join_commutative : x ⊔ y = y ⊔ x := by
  dsimp [Max.max]; dsimp [join]
  simp only [BoundedLattice.join_commutative, Bool.or_comm]

theorem join_associative : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) := by
  dsimp [Max.max]; dsimp [join]
  simp [Bool.or_assoc]


theorem join_absorption : x ⊔ (x ⊓ y) = x := by
  dsimp [Max.max, Min.min]
  dsimp [join, meet]
  cases x ; cases y.may_be_nil <;> simp

theorem join_bot : x ⊔ bot = x := by
  dsimp [Max.max]
  simp [join, bot]

theorem join_top : x ⊔ top = top := by
  dsimp [Max.max]; dsimp [join]
  simp [top]

theorem meet_commutative : x ⊓ y = y ⊓ x := by
  dsimp [Min.min]; dsimp [meet]
  simp [BoundedLattice.meet_commutative, Bool.and_comm]

theorem meet_associative : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := by
  dsimp [Min.min]; dsimp [meet]
  simp [Bool.and_assoc]

theorem meet_absorption : x ⊓ (x ⊔ y) = x := by
  dsimp [Min.min, Max.max]; dsimp [meet, join]
  cases x ; cases y.may_be_nil <;> simp

theorem meet_top : x ⊓ top = x := by
  dsimp [Min.min]; dsimp [meet]
  simp [top]

theorem meet_bot : x ⊓ bot = bot := by
  dsimp [Min.min]
  simp [meet, bot]

theorem non_trivial : Undefined.top ≠ (bot : Undefined α) := by
  simp [top, bot]

theorem join_is_lub
: ∀ (x y z : Undefined α), x = x ⊓ z → y = y ⊓ z → x ⊔ y = (x ⊔ y) ⊓ z
:= by
  rintro ⟨x,x?⟩ ⟨y, y?⟩ ⟨z, z?⟩
  dsimp [Min.min, Max.max]
  simp only [join, meet, mk.injEq]
  rintro ⟨hx, hx?⟩ ⟨hy, hy?⟩
  constructor
  · apply BoundedLattice.join_is_lub <;> assumption
  · grind only

theorem meet_is_glb
: ∀ (x y z : Undefined α), z = z ⊓ x → z = z ⊓ y → z = z ⊓ (x ⊓ y)
:= by
  rintro ⟨x,x?⟩ ⟨y, y?⟩ ⟨z, z?⟩
  dsimp [Min.min]
  simp only [ meet, mk.injEq]
  rintro ⟨hx, hx?⟩ ⟨hy, hy?⟩
  constructor
  · apply BoundedLattice.meet_is_glb <;> assumption
  · grind only

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
  join_is_lub := join_is_lub
  meet_is_glb := meet_is_glb

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
    simp only [Widen.widen, widen, Min.min]
    simp only [meet]
    simp only [mk.injEq, Bool.eq_self_and, Bool.or_eq_true]
    constructor
    · apply WidenLawful.covering_left
    · intros ; left ; assumption
  covering_right := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp only [Widen.widen, widen, Min.min]
    simp only [meet]
    simp only [mk.injEq, Bool.eq_self_and, Bool.or_eq_true]
    constructor
    · apply WidenLawful.covering_right
    · intros ; right ; assumption

instance : NarrowLawful (Undefined α) where
  bounding_low := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Narrow.narrow, narrow, Min.min]
    simp only [meet]
    simp
    rw [← ι.meet_associative]
    apply NarrowLawful.bounding_low
  bounding_high := by
    intros x y n
    let ⟨x, b⟩ := x
    let ⟨y, b'⟩ := y
    unfold BoundedLattice.IsSubset
    simp [Narrow.narrow, narrow, Min.min]
    simp only [meet]
    simp
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
    simp [Undefined.bot, Bot.bot]
    infer_instance

  bounding_low := NarrowLawful.bounding_low
  bounding_high := NarrowLawful.bounding_high
end Undefined
end Lustrean
