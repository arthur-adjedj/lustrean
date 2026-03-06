import Lustrean.Domain.Interval.Defs
import Lustrean.Domain.Interval.Operations
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop -- For one instance

namespace List

private def tighestLowerBound(cts : List Int) (n : WithBot Int): WithBot Int :=
  (cts.filter (fun x => ↑(x : Int) ≤ n)).min?

private def tighestLowerBound.spec (cts : List Int) (n : WithBot Int)
: cts.tighestLowerBound n ≤ n
:= by
  dsimp [List.tighestLowerBound]
  generalize ls_def: cts.filter _ = ls
  have mem_ls: ∀ z ∈ ls, z ≤ n := by grind
  match ls with
  | [] =>
    have: none = (⊥ : WithBot Int) := rfl
    grind [bot_le, List.min?]
  | x :: xs =>
    rw [List.min?_eq_some_min (by grind only)]
    apply mem_ls
    apply List.min_mem

-- TODO: Remove once https://github.com/leanprover/lean4/pull/12181 is included
local instance : Std.LawfulOrderLeftLeaningMax Int where
  max_eq_left := by grind
  max_eq_right := by grind

private def tighestUpperBound(cts : List Int) (n : WithTop Int): WithTop Int :=
  (cts.filter (fun x => n ≤ ↑(x : Int))).max?

private def tighestUpperBound.spec (cts : List Int) (n : WithTop Int)
: n ≤ cts.tighestUpperBound n
:= by
  dsimp [List.tighestUpperBound]
  generalize ls_def: cts.filter _ = ls
  have mem_ls: ∀ z ∈ ls, n ≤ z := by grind
  match ls with
  | [] =>
    have: none = (⊤ : WithTop Int) := rfl
    grind [le_top, List.max?]
  | x :: xs =>
    rw [List.max?_eq_some_max (by grind only)]
    apply mem_ls
    apply List.max_mem

end List

namespace Lustrean.Interval

def widen (cts : List Int) (limit : Nat) (x y : Interval) (n : Nat): Interval :=
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

def instWidenLawfulOfConstantsAndLimit (cts : List Int) (limit : Nat) : WidenLawful Interval where
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
      · dsimp only [zh]; split
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
      · dsimp only [zh]; split
        · assumption
        · apply List.tighestUpperBound.spec

def narrow (x y : Interval) (_ : Nat): Interval := x ⊓ y

instance : NarrowLawful (Interval) where
  narrow := narrow
  bounding_low  := by grind [BoundedLattice.IsSubset, narrow]
  bounding_high := by grind [BoundedLattice.IsSubset, narrow]

def refineEq: NonEmpty → NonEmpty → Interval
| x, y => x ⊓ y

def refineLe: NonEmpty → NonEmpty → Interval
| .mk xl xh _, .mk _ yh _  =>
  ofPair xl (xh ⊓ yh)

def refineLt: NonEmpty → NonEmpty → Interval
| x, y => (refineLe (x + ↑1) y) - ↑(1 : NonEmpty)

def refineGe: NonEmpty → NonEmpty → Interval
| .mk xl xh _, .mk yl _ _  =>
  ofPair (xl ⊔ yl) xh

def refineGt: NonEmpty → NonEmpty → Interval
| x, y => (refineGe (x - ↑1) y) + ↑(1 : NonEmpty)

def refine (op : CompareOp): Interval → Interval → Interval
| (x : NonEmpty), (y : NonEmpty) =>
  match op with
  | .eq  => refineEq x y
  | .le  => refineLe x y
  | .lt  => refineLt x y
  | .ge  => refineGe x y
  | .gt  => refineGt x y
  | .neq => refineLt x y ⊔ refineGt x y
| ⊥, _ | _, ⊥ => ⊥

def rand: Option Int → Option Int → Interval
| .some x, .some y => ofPair x y
| .none,   .some y => .mk ⊥ y
| .some x, .none   => .mk x ⊤
| .none,   .none   => .mk ⊥ ⊤

instance : BoundedLattice Interval := BoundedLattice.ofLatticeAndBoundedOrder

def ofConstantsAndLimit (cts : List Int := []) (limit : Nat := 10) : ValueDomain Interval :=
  have : WidenLawful Interval := instWidenLawfulOfConstantsAndLimit
    (cts := cts) (limit := limit)
  {
    nil := ⊤ -- we have no better approximation for nil in this domain than ⊤
    rand := rand
    compare op x y := (x.refine op y, y.refine op.symm x)
  }
