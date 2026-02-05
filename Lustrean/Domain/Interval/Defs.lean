import Lustrean.Domain.NonRelational
import Mathlib.Order.WithBot
import Mathlib.Order.BoundedOrder.Lattice

import Lean

-- set_option trace.profiler true
namespace WithBot

def hle{α : Type} [LE α] : WithBot α → WithTop α → Prop
  | (x : α), (y : α) => x ≤ y
  | _, _ => True

notation x:60 "≤∘" y:61 => hle x y

@[simp, grind .] theorem hle_top {α : Type} [LE α] : ∀ (x : WithBot α), x ≤∘ ⊤
  := by rintro ⟨⟩ <;> simp only [hle]
@[simp, grind .] theorem bot_hle {α : Type} [LE α] : ∀ (x : WithTop α), ⊥ ≤∘ x
  := by intro; simp only [hle]
@[simp, grind =] theorem coe_hle_coe {α : Type} [LE α] (x y: α): (x ≤∘ (y : WithTop α)) = (x ≤ y)
  := rfl

-- theorem not_hle {α : Type} [LinearOrder α] (x : WithBot α) (y : WithTop α)
-- : ¬ x ≤∘ y → ∃ (a b: α), x = a ∧ y = b ∧ b ≤ a
-- := by
--   match x, y with
--   | ⊥, _ => simp
--   | _, ⊤ => simp
--   | (a : α), (b : α) => grind

instance {α : Type} [LE α] [ι : DecidableLE α] : DecidableRel (hle (α := α))
| (x : α), (y : α) => ι x y
| ⊥, _ | _, ⊤ => by simp; infer_instance

instance instLeHle
  {α : Type} [LE α]
  [ι : Trans (LE.le (α := α)) (LE.le (α := α)) (LE.le (α := α))]
  : Trans (LE.le (α := WithBot α)) hle hle
where
    trans := by
        intros x y z
        match x, y, z with
        | x, ⊥, z => simp only [WithBot.le_bot_iff, hle, forall_const]; rintro rfl; dsimp
        | x, (y : α), ⊤ => cases x <;> simp
        | x, (y : α), (z : α) =>
          cases x <;> simp [hle]
          intro h_y hyz
          apply ι.trans
          · apply h_y
          · apply hyz

instance instHleLe
  {α : Type} [LE α]
  [ι : Trans (LE.le (α := α)) (LE.le (α := α)) (LE.le (α := α))]
  : Trans hle (LE.le (α := WithTop α)) hle
where
    trans := by
        intros x y z
        match x, y, z with
        | x, y, ⊤ => cases x <;> simp
        | x, ⊤, (z : α) => simp
        | x, (y : α), (z : α) =>
          cases x <;> simp [hle]
          intro h_y hyz
          apply ι.trans
          · apply h_y
          · apply hyz

def hMax {α : Type} [Max α] : WithBot α → WithTop α → WithTop α
| (x : α), (y : α) => (x ⊔ y : α)
| _, y => y

@[simp] theorem hMax_top{α : Type} [Max α](x : WithBot α)
: WithBot.hMax x ⊤ = ⊤
:= by cases x <;> rfl

@[simp] theorem coe_hMax_coe{α : Type} [Max α](x y: α)
: WithBot.hMax x y = WithTop.some (x ⊔ y: α)
:= rfl

def hMin {α : Type} [Min α] : WithBot α → WithTop α → WithBot α
| (x : α), (y : α) => (x ⊓ y : α)
| x, _ => x -- Cannot fuse with case above because they're different ⊥'s

@[simp] theorem bot_hMin{α : Type} [Min α](x : WithTop α)
: WithBot.hMin ⊥ x = ⊥
:= rfl

@[simp] theorem coe_hMin_coe{α : Type} [Min α](x y: α)
: WithBot.hMin x y = WithBot.some (x ⊓ y: α)
:= rfl

end WithBot

section WithBotWithTopDefinitions

instance : Add (WithBot Int) where add
| (x : Int), (y : Int) => x + y
| _, _ => ⊥

instance : Add (WithTop Int) where add
| (x : Int), (y : Int) => x + y
| _, _ => ⊤


def WithBot.neg{α : Type} [Neg α] : WithBot α → WithTop α
| ⊥ => ⊤
| (x : α) => (-x: α)

def WithTop.neg{α : Type} [Neg α] : WithTop α → WithBot α
| ⊤  => ⊥
| (x : α) => (-x: α)

instance instTopTopMul{α : Type} [Mul α] : HMul (WithTop α) (WithTop α) (WithTop α) where
  hMul
  | (x : α), (y : α) => (x * y : α)
  | ⊤, _ | _, ⊤ => ⊤

instance instBotBotMul{α : Type} [Mul α] : HMul (WithBot α) (WithBot α) (WithTop α) where
  hMul
  | (x : α), (y : α) => (x * y : α)
  | ⊥, _ | _, ⊥ => ⊤

instance instBotTopMul{α : Type} [Mul α] : HMul (WithBot α) (WithTop α) (WithBot α) where
  hMul
  | (x : α), (y : α) => (x * y : α)
  | ⊥, _ | _, ⊤ => ⊥

instance instTopBotMul{α : Type} [Mul α] : HMul (WithTop α) (WithBot α) (WithBot α) where
  hMul x y := y * x

instance {α : Type} [ι :Zero α] : Zero (WithTop α) where zero := ι.zero

instance {α : Type} [ι :Zero α] : Zero (WithBot α) where zero := ι.zero

end WithBotWithTopDefinitions

namespace Lustrean

def Interval.NonEmpty :=  {p : WithBot Int ×  WithTop Int // p.1 ≤∘ p.2}
deriving BEq, DecidableEq

namespace Interval.NonEmpty

@[match_pattern]
abbrev mk(l : WithBot Int) (h : WithTop Int) (inv : l ≤∘ h): NonEmpty := ⟨(l,h),inv⟩

instance (n : Nat): OfNat (Interval.NonEmpty) n where
  ofNat := mk (n : Int) (n : Int) (by simp only [WithBot.coe_hle_coe, le_refl])

instance : Repr NonEmpty where
  reprPrec
  | ⟨(l, h), _⟩, _ =>
    let lhs := match l with
               | ⊥ => "(-∞"
               | (l : Int) => s!"[{l}"
    let rhs := match h with
               | ⊤ => "∞)"
               | (h : Int) => s!"{h}]"
    Std.Format.text s!"{lhs}, {rhs}"

instance : ToString NonEmpty where toString := toString ∘ repr

instance : LE Interval.NonEmpty where
  le
  | ⟨(l, h), _⟩, ⟨(l', h'), _⟩ => l' ≤ l ∧ h ≤ h'

@[simp]
theorem mk_le_mk (l l': WithBot Int) (h h': WithTop Int)
  (inv : l ≤∘ h)
  (inv': l' ≤∘ h')
:  mk l h inv  ≤ mk l' h' inv'
-- :  instLE.le (⟨⟨l, h⟩,inv⟩: NonEmpty) (⟨⟨l', h'⟩, inv'⟩ : NonEmpty)
↔ l' ≤ l ∧ h ≤ h' := by rfl

instance : Preorder Interval.NonEmpty where
  le_refl := by
    rintro ⟨⟨l, h⟩, _⟩; simp only [mk_le_mk, Std.IsPreorder.le_refl, and_self]
  le_trans := by
    rintro ⟨⟨l₁, h₁⟩, _⟩ ⟨⟨l₂, h₂⟩, _⟩ ⟨⟨l₃, h₃⟩, _⟩
    simp only [mk_le_mk]
    rintro ⟨l21, h12⟩ ⟨l32, h23⟩
    constructor
    · trans <;> assumption
    · trans <;> assumption

instance : PartialOrder Interval.NonEmpty where
  le_antisymm := by
    rintro ⟨⟨l, h⟩, _⟩ ⟨⟨l, h⟩, _⟩
    simp only [mk_le_mk]
    intro ⟨lyx, hxy⟩ ⟨lxy, hyx⟩
    rw [Subtype.mk.injEq, Prod.mk.injEq]
    constructor
    · apply le_antisymm <;> assumption
    · apply le_antisymm <;> assumption

instance : Top Interval.NonEmpty where
  top := ⟨(⊥, ⊤), WithBot.bot_hle _⟩

def join: NonEmpty → NonEmpty → NonEmpty
| ⟨⟨h, l⟩, _⟩, ⟨⟨h', l'⟩, _⟩ => {
  val := ((h ⊓ h'),(l ⊔ l')),
  property := by
    simp only [max_def, min_def]
    split <;> split
    · calc h
        _ ≤  h' := by assumption
        _ ≤∘ l' := by assumption
    · assumption
    · assumption
    · calc h'
        _ ≤∘ l' := by assumption
        _ ≤  l  := by have := Std.IsLinearOrder.le_total l l'; grind
}

instance : SemilatticeSup Interval.NonEmpty where
  sup := join
  le_sup_left x y := by
    fun_cases (x.join y)
    dsimp only [instPartialOrder, instPreorder, instLE] at *
    constructor <;> grind
  le_sup_right x y := by
    fun_cases (x.join y)
    dsimp only [instPartialOrder, instPreorder, instLE] at *
    constructor <;> grind
  sup_le x y z := by
    fun_cases (x.join y)
    rcases z with ⟨⟨l,h⟩, _⟩
    simp only [mk_le_mk, le_inf_iff, sup_le_iff, and_imp]
    grind

instance : OrderTop Interval.NonEmpty where
  le_top := by
    rintro ⟨⟨l, h⟩, inv⟩
    dsimp [instLE]
    constructor <;> simp only [le_top, bot_le]

instance {α : Type} [Sub α] : HSub (WithTop α) (WithBot α) (WithTop α) where
  hSub
  | (x : α), (y : α) => x - y
  | _, _ => ⊤

instance {α : Type} [Sub α] : HSub (WithBot α) (WithTop α) (WithBot α) where
  hSub
  | (x : α), (y : α) => x - y
  | _, _ => ⊥

def add: NonEmpty → NonEmpty → NonEmpty
| ⟨(xl,xh),xinv⟩, ⟨(yl,yh),yinv⟩ => {
    val := (xl + yl, xh + yh),
    property := by
      dsimp at yinv xinv ⊢
      match xl, xh, yl, yh with
      | (xl : Int), (xh : Int), (yl : Int), (yh : Int) =>
        dsimp only [HAdd.hAdd]
        dsimp only [Add.add] at xinv yinv ⊢
        grind [WithBot.hle] -- HERE
      | ⊥, _, _, _
      | (_ : Int), _, ⊥, _ =>
        dsimp only [HAdd.hAdd]
        dsimp only [Add.add]
        apply WithBot.bot_hle
      | _, ⊤, _, _
      | _, (_ : Int), _, ⊤ =>
        dsimp only [HAdd.hAdd]
        dsimp only [Add.add]
        apply WithBot.hle_top
  }

instance : Add NonEmpty where add := add

def neg: NonEmpty → NonEmpty
| .mk l h o => .mk h.neg l.neg <| by
  match l, h with
  | ⊥, _ | _, ⊤ =>
    simp only [WithTop.neg, WithBot.neg, WithBot.hle_top, WithBot.bot_hle]
  | (l : Int), (h : Int) =>
    simpa only [WithTop.neg, WithBot.neg, WithBot.coe_hle_coe, Int.neg_le_neg_iff, ge_iff_le]

instance : Neg NonEmpty where neg := neg

def sub: NonEmpty → NonEmpty → NonEmpty
| ⟨(xl,xh),xinv⟩, ⟨(yl,yh), yinv⟩ => {
  val := (xl - yh, xh - yl),
  property := by
    match xl, yh with
    | (xl : Int), (yh : Int) =>
      match xh, yl with
      | (xh : Int), (yh : Int) =>
        simp only [WithBot.hle] at xinv yinv ⊢
        grind
      | ⊤, _
      | _, ⊥ =>
        simp only [HSub.hSub, WithBot.hle_top]
    | ⊥, _ | _, ⊤ =>
      simp only [HSub.hSub, WithBot.bot_hle]
}

instance : Sub NonEmpty where sub := sub

def mul: NonEmpty → NonEmpty → NonEmpty
| ⟨(xl,xh), xinv⟩, ⟨(yl,yh),yinv⟩ =>
  let ll := xl * yl
  let hh := xh * yh
  let lh := xl * yh
  let hl := xh * yl
  {
    val := ( (lh ⊓ hl).hMin (ll ⊓ hh)
           , (lh ⊔ hl).hMax (ll ⊔ hh)
           )
    property := by
      dsimp only [ll, hh, lh, hl]
      match xl, xh, yl, yh with
      | (xl : Int), (xh : Int), (yl : Int), (yh : Int) =>
        dsimp only [instTopTopMul, instBotBotMul, instBotTopMul, instTopBotMul]
        dsimp only [Min.min, SemilatticeInf.inf, WithBot.map₂_coe_coe]
        dsimp only [Max.max, SemilatticeSup.sup, WithTop.map₂_coe_coe]
        dsimp only [WithBot.coe_hMax_coe, WithBot.coe_hMin_coe,
                    WithBot.coe_hle_coe]
        have: ∀ (x y: Int), Lattice.inf x y = min x y := fun x y => rfl
        grind
      | ⊥, _, _, _
      | _, ⊤, _, _
      | _, _, ⊥, _
      | _, (_ : Int), _, ⊤ =>
        simp only [HMul.hMul,
          min_bot_left, min_bot_right,
          max_top_left, max_top_right,
          WithBot.bot_hMin, WithBot.hMax_top,
          WithBot.hle_top, WithBot.bot_hle
        ]
  }

instance : Mul NonEmpty where mul := mul

end Interval.NonEmpty

def Interval := WithBot Interval.NonEmpty
deriving LE, Repr, Bot, Top, SemilatticeSup, OrderTop,
   Coe Interval.NonEmpty, BoundedOrder, BEq, DecidableEq

namespace Interval

@[match_pattern]
abbrev mk(low : WithBot Int) (high : WithTop Int) (h : low ≤∘ high := by constructor): Interval :=
  NonEmpty.mk low high h

@[grind] instance : EmptyCollection Interval where emptyCollection := ⊥
@[grind] instance : Top Interval where top := mk ⊥ ⊤ (WithBot.hle_top _)

@[cases_eliminator, elab_as_elim]
def recOpenClose{motive : Interval → Sort _}
  (empty : motive ⊥)
  (nonempty : ∀ (int : Interval.NonEmpty), motive (int : WithBot _))
  (int : Interval)
: motive int
:= match int with
  | ⊥ => empty
  | (int : NonEmpty) => nonempty int

section Domain

def ofPair(x : WithBot Int) (y : WithTop Int): Interval :=
  if h : x ≤∘ y then
    .mk x y h
  else ⊥

/- We can't define `meet` for `NonEmpty` since the internsection
  may be empty itself. -/
def meet: Interval → Interval → Interval
| .mk h l _, .mk h' l' _ =>
  ofPair (h ⊔ h') (l ⊓ l')
| _, _ => ⊥

instance : Min Interval where min := meet

theorem meet_commutative (x y : Interval) : x ⊓ y = y ⊓ x := by
  dsimp [Min.min]
  match x, y with
  | .mk h l _, .mk h' l' _ =>
    simp only [meet, sup_comm, inf_comm]
  | ⊥, .mk ..
  | .mk .., ⊥
  | ⊥, ⊥ => simp only [meet]

set_option maxHeartbeats 10000000 in
theorem inf_le_left (x y : Interval): x ⊓ y ≤ x := by
    match x, y with
    | ⊥, _
    | (_ : NonEmpty), ⊥ => dsimp [Min.min, meet]; constructor
    | .mk l h inv, .mk l' h' inv' =>
      dsimp only [min]
      simp only [meet, ofPair]
      split
      · apply WithBot.coe_le_coe.mpr
        simp only [NonEmpty.mk_le_mk, le_sup_left, _root_.inf_le_left, and_self]
      · constructor

instance : SemilatticeInf Interval where
  inf := Min.min
  inf_le_left := inf_le_left
  inf_le_right x y := meet_commutative _ _ ▸ inf_le_left y x
  le_inf x y z := by
    dsimp [Min.min]
    match y, z, x with
    | .mk yl yh yinv, .mk zl zh zinv, .mk xl xh xinv =>
      simp only [mk, meet, ofPair]
      intro hxy hxz
      obtain hxy := WithBot.coe_le_coe.mp hxy
      obtain hxz := WithBot.coe_le_coe.mp hxz
      simp only [NonEmpty.mk_le_mk] at hxy hxz
      split <;> rename_i cond
      · -- Intersection is nonempty
        apply WithBot.coe_le_coe.mpr
        simp only [NonEmpty.mk_le_mk]
        obtain ⟨_,_⟩ := hxy
        obtain ⟨_,_⟩ := hxz
        constructor
        · apply sup_le <;> assumption
        · apply le_inf <;> assumption
        -- simp? [*]
      · -- Intersection is empty
        exfalso
        apply cond
        calc _ ≤  xl := by grind
             _ ≤∘ xh := by assumption
             _ ≤  _  := by rw [min_def]; split <;> grind
    | .mk yl yh yinv, .mk zl zh zinv, ⊥  => intros; constructor
    | ⊥, _, _
    | .mk l h inv, ⊥, _ => intros; simpa

instance : Lattice Interval where

end Domain

end Interval

end Lustrean
