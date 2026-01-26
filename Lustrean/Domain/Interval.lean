import Lustrean.Domain.NonRelational
import Mathlib.Order.WithBot
import Mathlib.Order.BoundedOrder.Lattice

import Lean

-- set_option trace.profiler true
namespace Lustrean

def hle{α: Type}[LE α]: WithBot α → WithTop α → Prop
  | (x: α), (y: α) => x ≤ y
  | _, _ => True

notation x:60 "≤∘" y:61 => hle x y

@[simp, grind .] theorem hle_top {α: Type}[LE α]: ∀ (x: WithBot α), x ≤∘ ⊤
  := by rintro ⟨⟩ <;> simp only [hle]
@[simp, grind .] theorem bot_hle {α: Type}[LE α]: ∀ (x: WithTop α), ⊥ ≤∘ x
  := by intro; simp only [hle]
@[simp, grind =] theorem coe_hle_coe {α: Type}[LE α] (x y: α): (x ≤∘ (y: WithTop α)) = (x ≤ y)
  := rfl

theorem not_hle {α: Type}[LinearOrder α] (x: WithBot α)(y: WithTop α)
: ¬ x ≤∘ y → ∃ (a b: α), x = a ∧ y = b ∧ b ≤ a
:= by
  match x, y with
  | ⊥, _ => simp
  | _, ⊤ => simp
  | (a: α), (b: α) => grind

instance{α: Type}[LE α][ι: DecidableLE α]: DecidableRel (hle (α := α))
| (x: α), (y: α) => ι x y
| ⊥, _ | _, ⊤ => by simp; infer_instance

instance instLeHle
  {α: Type}[LE α]
  [ι: Trans (LE.le (α := α)) (LE.le (α := α)) (LE.le (α := α))]
: Trans (LE.le (α := WithBot α)) hle hle where
    trans := by
        intros x y z
        match x, y, z with
        | x, ⊥, z => simp only [WithBot.le_bot_iff, hle, forall_const]; rintro rfl; dsimp
        | x, (y: α), ⊤ => cases x <;> simp
        | x, (y: α), (z: α) =>
          cases x <;> simp [hle]
          intro h_y hyz
          apply ι.trans
          · apply h_y
          · apply hyz

instance instHleLe
  {α: Type}[LE α]
  [ι: Trans (LE.le (α := α)) (LE.le (α := α)) (LE.le (α := α))]
: Trans hle (LE.le (α := WithTop α)) hle where
    trans := by
        intros x y z
        match x, y, z with
        | x, y, ⊤ => cases x <;> simp
        | x, ⊤, (z: α) => simp
        | x, (y: α), (z: α) =>
          cases x <;> simp [hle]
          intro h_y hyz
          apply ι.trans
          · apply h_y
          · apply hyz

def Interval.NonEmpty :=  {p : WithBot Int ×  WithTop Int // p.1 ≤∘ p.2}
deriving BEq, DecidableEq

instance(n: Nat): OfNat (Interval.NonEmpty) n where
  ofNat := ⟨((n: Int),(n: Int)), by simp only [coe_hle_coe, le_refl]⟩

namespace Interval.NonEmpty

instance: Repr NonEmpty where
  reprPrec
  | ⟨(l, h), _⟩, _ =>
    let lhs := match l with
               | ⊥ => "(-∞"
               | (l: Int) => s!"[{l}"
    let rhs := match h with
               | ⊤ => "+∞)"
               | (h: Int) => s!"{h}]"
    Std.Format.text s!"{lhs},{rhs}"

instance: LE Interval.NonEmpty where
  le
  | ⟨(l, h), _⟩, ⟨(l', h'), _⟩ => l' ≤ l ∧ h ≤ h'

@[simp]
theorem mk_le_mk (l l': WithBot Int) (h h': WithTop Int)
  (inv : l ≤∘ h)
  (inv': l' ≤∘ h')
:  instLE.le (⟨⟨l, h⟩,inv⟩: NonEmpty) (⟨⟨l', h'⟩, inv'⟩ : NonEmpty)
↔ l' ≤ l ∧ h ≤ h' := by rfl

instance: Preorder Interval.NonEmpty where
  le_refl := by
    rintro ⟨⟨l, h⟩, _⟩; simp
  le_trans := by
    rintro ⟨⟨l₁, h₁⟩, _⟩ ⟨⟨l₂, h₂⟩, _⟩ ⟨⟨l₃, h₃⟩, _⟩
    simp only [mk_le_mk]
    rintro ⟨l21, h12⟩ ⟨l32, h23⟩
    constructor
    · trans <;> assumption
    · trans <;> assumption

instance: PartialOrder Interval.NonEmpty where
  le_antisymm := by
    rintro ⟨⟨l, h⟩, _⟩ ⟨⟨l, h⟩, _⟩
    simp only [mk_le_mk]
    intro ⟨lyx, hxy⟩ ⟨lxy, hyx⟩
    rw [Subtype.mk.injEq, Prod.mk.injEq]
    constructor
    · apply le_antisymm <;> assumption
    · apply le_antisymm <;> assumption

instance: Top Interval.NonEmpty where
  top := ⟨(⊥, ⊤), bot_hle _⟩

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

instance: SemilatticeSup Interval.NonEmpty where
  sup := join
  le_sup_left x y := by
    fun_cases (x.join y)
    simp
  le_sup_right x y := by
    fun_cases (x.join y)
    simp
  sup_le x y z := by
    fun_cases (x.join y)
    rcases z with ⟨⟨l,h⟩, _⟩
    simp only [mk_le_mk, le_inf_iff, sup_le_iff, and_imp]
    grind

instance: OrderTop Interval.NonEmpty where
  le_top := by
    rintro ⟨⟨l, h⟩, inv⟩
    dsimp [instLE]
    constructor <;> simp only [le_top, bot_le]

instance {α: Type}[Sub α]: HSub (WithTop α) (WithBot α) (WithTop α) where
  hSub
  | (x: α), (y: α) => x - y
  | _, _ => ⊤

instance {α: Type}[Sub α]: HSub (WithBot α) (WithTop α) (WithBot α) where
  hSub
  | (x: α), (y: α) => x - y
  | _, _ => ⊥

def sub: NonEmpty → NonEmpty → NonEmpty
| ⟨(xl,xh),xinv⟩, ⟨(yl,yh), yinv⟩ => {
  val := (xl - yh, xh - yl),
  property := by
    match xl, yh with
    | (xl: Int), (yh: Int) =>
      match xh, yl with
      | (xh: Int), (yh: Int) =>
        simp only [hle] at xinv yinv ⊢
        grind
      | ⊤, _
      | _, ⊥ =>
        simp only [HSub.hSub, hle_top]
    | ⊥, _ | _, ⊤ =>
      simp only [HSub.hSub, bot_hle]
}

instance: Sub NonEmpty where sub := sub

end Interval.NonEmpty

def Interval := WithBot Interval.NonEmpty
deriving LE, Repr, Bot, Top, SemilatticeSup, OrderTop,
   Coe Interval.NonEmpty, BoundedOrder, BEq, DecidableEq

namespace Interval

@[match_pattern]
abbrev mk(low: WithBot Int)(high: WithTop Int)(h: low ≤∘ high): Interval :=
  let x : NonEmpty := {val := (low, high), property := h }
  x

@[grind] instance: EmptyCollection Interval where emptyCollection := ⊥
@[grind] instance: Top Interval where top := mk ⊥ ⊤ (hle_top _)

@[cases_eliminator, elab_as_elim]
def recOpenClose{motive: Interval → Sort _}
  (empty: motive ⊥)
  (nonempty: ∀ (int: Interval.NonEmpty), motive (int : WithBot _))
  (int: Interval)
: motive int
:= match int with
  | ⊥ => empty
  | (int: NonEmpty) => nonempty int

section Domain

def ofPair(x: WithBot Int)(y: WithTop Int): Interval :=
  if h : x ≤∘ y then
    .mk x y h
  else ⊥

def meet: Interval → Interval → Interval
| .mk h l _, .mk h' l' _ =>
  ofPair (h ⊔ h') (l ⊓ l')
| _, _ => ⊥

instance: Min Interval where min := meet

theorem meet_commutative (x y : Interval) : x ⊓ y = y ⊓ x := by
  dsimp [Min.min]
  match x, y with
  | .mk h l _, .mk h' l' _ =>
    simp only [meet, sup_comm, inf_comm]
  | ⊥, .mk ..
  | .mk .., ⊥
  | ⊥, ⊥ => simp only [meet]

theorem inf_le_left (x y : Interval): x ⊓ y ≤ x := by
    match x, y with
    | ⊥, _
    | (_: NonEmpty), ⊥ => dsimp [Min.min, meet]; constructor
    | .mk l h inv, .mk l' h' inv' =>
      dsimp [Min.min]
      simp only [meet, ofPair]
      split
      · apply WithBot.coe_le_coe.mpr
        simp
      · constructor

instance: SemilatticeInf Interval where
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
        simp [*]
      · -- Intersection is empty
        exfalso
        apply cond
        calc _ ≤  xl := by grind
             _ ≤∘ xh := by assumption
             _ ≤  _  := by rw [min_def]; split <;> grind
    | .mk yl yh yinv, .mk zl zh zinv, ⊥  => intros; constructor
    | ⊥, _, _
    | .mk l h inv, ⊥, _ => intros; simpa

instance: Lattice Interval where

end Domain

section Operators

def _root_.WithBot.lift₂{α: Type}(op: α × α → α): WithBot α → WithBot α → WithBot α
| (x: α), (y : α) => op (x,y)
| _, _ => ⊥

instance: Add (WithBot Int) where
  add := .lift₂ (fun (x,y) => x + y)

def _root_.WithTop.lift₂{α: Type}(op: α × α → α): WithTop α → WithTop α → WithTop α
| (x: α), (y : α) => op (x,y)
| _, _ => ⊤

instance: Add (WithTop Int) where
  add := .lift₂ (fun (x,y) => x + y)

-- TODO: Move to a better place
def NonEmpty.add: NonEmpty → NonEmpty → NonEmpty
| ⟨(xl,xh),xinv⟩, ⟨(yl,yh),yinv⟩ => {
    val := (xl + yl, xh + yh),
    property := by
      dsimp at yinv xinv ⊢
      match xl, xh, yl, yh with
      | (xl: Int), (xh: Int), (yl: Int), (yh: Int) =>
        dsimp [HAdd.hAdd];
        dsimp [Add.add, WithBot.lift₂, WithTop.lift₂]  at xinv yinv ⊢
        grind
      | ⊥, _, _, _
      | (_: Int), _, ⊥, _ =>
        dsimp [HAdd.hAdd]
        dsimp [Add.add, WithBot.lift₂]
        apply bot_hle
      | _, ⊤, _, _
      | _, (_: Int), _, ⊤ =>
        dsimp [HAdd.hAdd]
        dsimp [Add.add, WithTop.lift₂]
        apply hle_top
  }

-- TODO: Move to a better place
instance: Add NonEmpty where add := NonEmpty.add

def add: Interval → Interval → Interval
| (x: NonEmpty), (y: NonEmpty) => x + y
| ⊥, _ | _, ⊥ => ⊥

instance : Add (Interval) where add := add

-- TODO: Move to a better place
def _root_.WithBot.neg{α : Type}[Neg α]: WithBot α → WithTop α
| ⊥ => ⊤
| (x: α) => (-x: α)

-- TODO: Move to a better place
def _root_.WithTop.neg{α : Type}[Neg α]: WithTop α → WithBot α
| ⊤  => ⊥
| (x: α) => (-x: α)

def neg: Interval → Interval
| ⊥ => ⊥
| .mk l h o => .mk h.neg l.neg <| by
  match l, h with
  | ⊥, _ | _, ⊤ =>
    simp only [WithTop.neg, WithBot.neg, hle_top, bot_hle]
  | (l: Int), (h: Int) =>
    simpa [WithTop.neg, WithBot.neg]

instance : Neg Interval where neg := neg

-- We need the lift to be able to move around the defs...
def sub : Interval → Interval → Interval
| (x: NonEmpty), (y: NonEmpty) => x - y
| ⊥, other => -other
| other, ⊥ =>  other

instance : Sub Interval where sub := sub

-- TODO: Move to a better place
instance instTopTopMul{α: Type}[Mul α]: HMul (WithTop α) (WithTop α) (WithTop α) where
  hMul
  | (x: α), (y: α) => (x * y : α)
  | ⊤, _ | _, ⊤ => ⊤

-- TODO: Move to a better place
instance instBotBotMul{α: Type}[Mul α]: HMul (WithBot α) (WithBot α) (WithTop α) where
  hMul
  | (x: α), (y: α) => (x * y : α)
  | ⊥, _ | _, ⊥ => ⊤

-- TODO: Move to a better place
instance instBotTopMul{α: Type}[Mul α]: HMul (WithBot α) (WithTop α) (WithBot α) where
  hMul
  | (x: α), (y: α) => (x * y : α)
  | ⊥, _ | _, ⊤ => ⊥

-- TODO: Move to a better place
instance instTopBotMul{α: Type}[Mul α]: HMul (WithTop α) (WithBot α) (WithBot α) where
  hMul x y := y * x

-- TODO: Move to a better place
def _root_.WithBot.hMax {α: Type}[Max α]: WithBot α → WithTop α → WithTop α
| (x: α), (y: α) => (x ⊔ y : α)
| _, y => y

-- TODO: Move to a better place
@[simp] theorem _root_.WithBot.hMax_top{α: Type}[Max α](x: WithBot α)
: WithBot.hMax x ⊤ = ⊤
:= by cases x <;> rfl

-- TODO: Move to a better place
@[simp] theorem _root_.WithBot.coe_hMax_coe{α: Type}[Max α](x y: α)
: WithBot.hMax x y = WithTop.some (x ⊔ y: α)
:= rfl

-- TODO: Move to a better place
def _root_.WithBot.hMin {α: Type}[Min α]: WithBot α → WithTop α → WithBot α
| (x: α), (y: α) => (x ⊓ y : α)
| x, _ => x -- Cannot fuse with case above because they're different ⊥'s

-- TODO: Move to a better place
@[simp] theorem _root_.WithBot.bot_hMin{α: Type}[Min α](x: WithTop α)
: WithBot.hMin ⊥ x = ⊥
:= rfl

-- TODO: Move to a better place
@[simp] theorem _root_.WithBot.coe_hMin_coe{α: Type}[Min α](x y: α)
: WithBot.hMin x y = WithBot.some (x ⊓ y: α)
:= rfl

-- TODO: Move to a better place
def NonEmpty.mul: NonEmpty → NonEmpty → NonEmpty
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
      | (xl: Int), (xh: Int), (yl: Int), (yh: Int) =>
        dsimp only [instTopTopMul, instBotBotMul, instBotTopMul, instTopBotMul]
        dsimp only [Min.min, SemilatticeInf.inf, WithBot.map₂_coe_coe]
        dsimp only [Max.max, SemilatticeSup.sup, WithTop.map₂_coe_coe]
        dsimp only [WithBot.coe_hMax_coe, WithBot.coe_hMin_coe,
                    coe_hle_coe]
        have: ∀ (x y: Int), Lattice.inf x y = min x y := fun x y => rfl
        grind
      | ⊥, _, _, _
      | _, ⊤, _, _
      | _, _, ⊥, _
      | _, (_: Int), _, ⊤ =>
        simp only [HMul.hMul,
          min_bot_left, min_bot_right,
          max_top_left, max_top_right,
          WithBot.bot_hMin, WithBot.hMax_top,
          hle_top, bot_hle
        ]
  }

-- TODO: Move to a better place
instance: Mul NonEmpty where mul := NonEmpty.mul

def mul: Interval → Interval → Interval
| (x: NonEmpty), (y: NonEmpty) => (x * y: NonEmpty)
| ⊥, _ | _, ⊥ => ⊥

instance: Mul Interval where mul := mul

-- TODO: Move to a better place
instance{α: Type}[ι :Zero α]: Zero (WithTop α) where zero := ι.zero

-- TODO: Move to a better place
instance{α: Type}[ι :Zero α]: Zero (WithBot α) where zero := ι.zero

def divPos: Interval → Interval → Interval
| .mk _ xh _, .mk _ yh _ =>
  match xh, yh with
  | _, (0: Int) => ⊥
  | ⊤, _ => .mk 0 ⊤ (hle_top 0)
  | _, ⊤ => (0: NonEmpty)
  | (x: Int), (y: Int) =>
    if hyp: 0 ≤ x / y then
      .mk 0 (x / y) hyp
    else
      ⊥
| ⊥, _ | _, ⊥ => ⊥

def NonEmpty.splitAt (n: Int): NonEmpty → Interval × Interval
| ⟨(xl,xh),xinv⟩ =>
  if h: xl ≤∘ n ∧ n ≤∘ xh then
    have ⟨hl, hh⟩ := h
    (mk xl n hl, mk n xh hh)
  else if n ≤ xl then
    (⊥, mk xl xh xinv)
  else
    (mk xl xh xinv, ⊥)

def div: Interval → Interval → Interval
| (x: NonEmpty), (y: NonEmpty) =>
  let (x1, x2) := x.splitAt 0
  let (y1, y2) := y.splitAt 0
  (  ( x2).divPos ( y2))  ⊔
  (-((-x1).divPos ( y2))) ⊔
  (-(( x2).divPos (-y1))) ⊔
  (  (-x1).divPos (-y1))
| ⊥, _ | _, ⊥ => ⊥

instance: Div Interval where div := div

instance: ToString Interval where toString
| ⊥ => "∅"
| .mk ⊥ ⊤ _ =>               s!"(-∞, ∞)"
| .mk (x: Int) ⊤ _ =>        s!"[{x}, ∞)"
| .mk ⊥ (y: Int) _ =>        s!"(-∞, {y}]"
| .mk (x: Int) (y: Int) _ => s!"[{x}, {y}]"

end Operators

private def _root_.List.tighestLowerBound(cts: List Int)(n: WithBot Int): WithBot Int :=
  (cts.filter (fun x => ↑(x: Int) ≤ n)).min?

private def _root_.List.tighestLowerBound.spec (cts: List Int)(n: WithBot Int)
: cts.tighestLowerBound n ≤ n
:= by
  dsimp [List.tighestLowerBound]
  generalize ls_def: cts.filter _ = ls
  have mem_ls: ∀ z ∈ ls, z ≤ n := by grind
  match ls with
  | [] =>
    have: none = (⊥: WithBot Int) := rfl
    grind [bot_le, List.min?]
  | x :: xs =>
    rw [List.min?_eq_some_min (by grind only)]
    apply mem_ls
    apply List.min_mem

local instance: Std.LawfulOrderLeftLeaningMax Int where
  max_eq_left := by grind
  max_eq_right := by grind

private def _root_.List.tighestUpperBound(cts: List Int)(n: WithTop Int): WithTop Int :=
  (cts.filter (fun x => n ≤ ↑(x: Int))).max?

private def _root_.List.tighestUpperBound.spec (cts: List Int)(n: WithTop Int)
: n ≤ cts.tighestUpperBound n
:= by
  dsimp [List.tighestUpperBound]
  generalize ls_def: cts.filter _ = ls
  have mem_ls: ∀ z ∈ ls, n ≤ z := by grind
  match ls with
  | [] =>
    have: none = (⊤: WithTop Int) := rfl
    grind [le_top, List.max?]
  | x :: xs =>
    rw [List.max?_eq_some_max (by grind only)]
    apply mem_ls
    apply List.max_mem

def widen (cts: List Int) (limit : Nat) (x y : Interval) (n : Nat): Interval :=
  if n <= limit then
    x ⊔ y
  else
    match x, y with
    | .mk xl xh _, .mk yl yh yinv =>
      let zl := if xl ≤ yl then xl else cts.tighestLowerBound yl
      let zh := if xh ≥ yh then xh else cts.tighestUpperBound yh
      have zinv: zl ≤∘ zh := by
        calc zl
          _ ≤  yl := by
            have := List.tighestLowerBound.spec
            grind only
          _ ≤∘ yh := yinv
          _ ≤  zh := by
            have := List.tighestUpperBound.spec cts yh
            grind
      .mk zl zh zinv
    | ⊥, other | other, ⊥ =>  other

def instWidenLawfulOfListInt(cts: List Int)(limit: Nat): WidenLawful Interval where
  widen := widen (cts := cts) (limit := limit)
  covering_left x y n := by
    simp only [BoundedLattice.IsSubset, left_eq_inf]
    fun_cases (widen cts limit x y n)
    case case1 => apply le_sup_left
    case case4 => rfl
    case case3 => apply bot_le
    case case2 _ xl xh xinv yl yh yinv zl zh zinv =>
      apply WithBot.coe_le_coe.mpr
      simp only [NonEmpty.mk_le_mk]
      have := List.tighestLowerBound.spec
      have := List.tighestUpperBound.spec
      constructor
      · grind
      · dsimp [zh]; split
        · simp
        · trans yh
          · apply Std.le_of_not_ge (α := WithTop Int)
            grind
          · apply List.tighestUpperBound.spec
  covering_right x y n := by
    simp only [BoundedLattice.IsSubset, left_eq_inf]
    fun_cases (widen cts _ x y n)
    case case1 => apply le_sup_right
    case case4 => apply bot_le
    case case3 => rfl
    case case2 _ xl xh xinv yl yh yinv zl zh zinv =>
      apply WithBot.coe_le_coe.mpr
      simp only [NonEmpty.mk_le_mk]
      have := List.tighestLowerBound.spec
      have := List.tighestUpperBound.spec
      constructor
      · grind
      · dsimp [zh]; split
        · assumption
        · apply List.tighestUpperBound.spec

def narrow (x y : Interval)(_: Nat): Interval := x ⊓ y

instance : NarrowLawful (Interval) where
  narrow := narrow
  bounding_low  := by grind [BoundedLattice.IsSubset, narrow]
  bounding_high := by grind [BoundedLattice.IsSubset, narrow]

def measure : CompareOp → Nat
  | .eq => 0
  | .neq => 3
  | .le => 0
  | .lt => 1
  | .ge => 2
  | .gt => 2

def refineEq: NonEmpty → NonEmpty → Interval
| x, y => x ⊓ y

def refineLe: NonEmpty → NonEmpty → Interval
| ⟨(xl,_),_⟩, ⟨(_,yh), _⟩ =>
  ofPair xl (xl ⊓ yh)

def refineLt: NonEmpty → NonEmpty → Interval
| x, y =>
  let one: NonEmpty := (1: NonEmpty)
  let res := refineLe (x + one) y
  res - ↑one


def refine (op : CompareOp): Interval → Interval → Interval
| (x: NonEmpty), (y: NonEmpty) =>
  match op with
  | .eq  => refineEq x y
  | .lt  => refineLt x y
  | .le  => refineLe x y
  | .neq => refineLt x y ⊔ refineLt y x
  | .gt  => refineLt y x
  | .ge  => refineLe y x
| ⊥, _ | _, ⊥ => ⊥


-- TODO: Move to a better place
def _root_.Lustrean.CompareOp.opposite : CompareOp → CompareOp
| .eq => .eq
| .neq => .neq
| .le => .ge
| .ge => .le
| .lt => .gt
| .gt => .lt

instance: BoundedLattice Interval := BoundedLattice.ofLatticeAndBoundedOrder

def ofConstantsAndLimit(cts: List Int := [])(limit : Nat := 10): ValueDomain Interval :=
  have : WidenLawful Interval := Interval.instWidenLawfulOfListInt (cts := cts) (limit := limit)
  {
    nil := ⊤                    -- we have no better approximation for nil in this domain than ⊤
    rand
      | .some x, .some y =>
        if h : x ≤ y then
          mk x y h
        else
          ∅
      | .none, .some y => .mk ⊥ y <| by constructor
      | .some x, .none => .mk (x) ⊤ <| by constructor
      | .none, .none => .mk ⊥ ⊤ <| by constructor
    compare op x y := (x.refine op y, y.refine op.opposite x)

    -- TODO: pourquoi ça n'infère pas ??
    covering_left := WidenLawful.covering_left
    covering_right := WidenLawful.covering_right

    -- TODO: pourquoi ça n'infère pas ??
    bounding_low := NarrowLawful.bounding_low
    bounding_high := NarrowLawful.bounding_high
  }
end Interval
end Lustrean
