import Lustrean.Domain.Interval.Defs

namespace Lustrean.Interval

section Operators

def add: Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) => x + y
| ⊥, _ | _, ⊥ => ⊥

instance : Add (Interval) where add := add

def neg: Interval → Interval
| (x : NonEmpty) => (- x: NonEmpty)
| ⊥ => ⊥

instance : Neg Interval where neg := neg

def sub : Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) => x - y
| ⊥, other => -other
| other, ⊥ =>  other

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
