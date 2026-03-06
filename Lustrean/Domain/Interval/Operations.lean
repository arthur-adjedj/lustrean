import Lustrean.Domain.Interval.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop -- Includes WithBot.add

section WithBotWithTopDefinitions

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

namespace Lustrean.Interval

namespace NonEmpty

def add: NonEmpty → NonEmpty → NonEmpty
| .mk xl xh xinv, .mk yl yh yinv => {
    val := (xl + yl, xh + yh),
    property := by
      dsimp at yinv xinv ⊢
      match xl, xh, yl, yh with
      | (xl : Int), (xh : Int), (yl : Int), (yh : Int) =>
        dsimp only [HAdd.hAdd]
        simp only [Add.add, Option.map₂, Option.bind, Option.map]
        grind only [= WithBot.coe_hle_coe, WithBot.hle]
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
| .mk l h inv => .mk h.neg l.neg <| by
  match l, h with
  | ⊥, _ | _, ⊤ =>
    simp only [WithTop.neg, WithBot.neg, WithBot.hle_top, WithBot.bot_hle]
  | (l : Int), (h : Int) =>
    simpa only [WithTop.neg, WithBot.neg, WithBot.coe_hle_coe, Int.neg_le_neg_iff, ge_iff_le]

instance : Neg NonEmpty where neg := neg

def sub: NonEmpty → NonEmpty → NonEmpty
| .mk xl xh xinv, .mk yl yh yinv => {
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
| .mk xl xh xinv, .mk yl yh yinv =>
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

def length: NonEmpty → WithTop Int
| .mk xl xh .. => xh - xl

end NonEmpty

section Operators

def add: Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) => (x + y : NonEmpty)
| ⊥, _ | _, ⊥ => ⊥

instance : Add (Interval) where add := add

def neg: Interval → Interval
| (x : NonEmpty) => (- x: NonEmpty)
| ⊥ => ⊥

instance : Neg Interval where neg := neg

def sub : Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) => (x - y : NonEmpty)
| ⊥, _ | _, ⊥ => ⊥

instance : Sub Interval where sub := sub

def mul: Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) => (x * y: NonEmpty)
| ⊥, _ | _, ⊥ => ⊥

instance : Mul Interval where mul := mul

def divPos: Interval → Interval → Interval
| .mk _ xh _, .mk _ yh _ =>
  match xh, yh with
  | _, (0 : Int) => ⊥
  | ⊤, _ => .mk 0 ⊤ (WithBot.hle_top 0)
  | _, ⊤ => (0 : NonEmpty)
  | (x : Int), (y : Int) =>
    if hyp: 0 ≤ x / y then
      .mk 0 (x / y) hyp
    else
      ⊥
| ⊥, _ | _, ⊥ => ⊥

-- This definition needs to be here since it uses Interval
def NonEmpty.splitAt (n : Int): NonEmpty → Interval × Interval
| ⟨(xl,xh),xinv⟩ =>
  if h: xl ≤∘ n ∧ n ≤∘ xh then
    have ⟨hl, hh⟩ := h
    (mk xl n hl, mk n xh hh)
  else if n ≤ xl then
    (⊥, mk xl xh xinv)
  else
    (mk xl xh xinv, ⊥)

def div: Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) =>
  let (x1, x2) := x.splitAt 0
  let (y1, y2) := y.splitAt 0
  (  ( x2).divPos ( y2))  ⊔
  (-((-x1).divPos ( y2))) ⊔
  (-(( x2).divPos (-y1))) ⊔
  (  (-x1).divPos (-y1))
| ⊥, _ | _, ⊥ => ⊥

instance : Div Interval where div := div

instance : ToString Interval where toString
| ⊥ => "∅"
| .mk ⊥ ⊤ _ =>               s!"(-∞, ∞)"
| .mk (x : Int) ⊤ _ =>        s!"[{x}, ∞)"
| .mk ⊥ (y : Int) _ =>        s!"(-∞, {y}]"
| .mk (x : Int) (y : Int) _ => s!"[{x}, {y}]"

end Operators
