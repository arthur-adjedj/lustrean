import Lustrean.Domain.Interval.Galois -- Galois connection of Interval domain
import Lustrean.Domain.Interval.Operations -- Arithmetic operaitons
import Lustrean.Domain.Interval.ValueDomain -- Value domain operations
import Lustrean.Domain.GaloisConnection -- Extra definitions on Galois connections
import Mathlib.Algebra.Group.Pointwise.Set.Basic -- Set operations
import Mathlib.Algebra.Group.Defs -- For sub_eq_add_neg

attribute [-simp] bot_eq_zero' bot_eq_one' «Prop».bot_eq_false

namespace Lustrean.Interval

section OperationCorrectness
open Pointwise

@[simp] -- TODO: How to put a `grind` attribute here?
theorem concrete_ofNat(n: Nat): concrete (ofNat(n): NonEmpty) = {(n: Int)} := by
  simp only [concrete, WithBot.coe_le_coe]
  apply le_antisymm
  · intros e e_h
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe] at e_h
    simp only [Set.mem_singleton_iff, le_antisymm e_h.1 e_h.2]
  · rintro e rfl
    simp only [WithTop.coe_natCast, Set.mem_setOf_eq, le_refl, and_self]

lemma neg_correct
: gc.IsBestAbstraction (- ·) (- ·)
:= by
  intros x
  match x with
  | .mk xl xh xinv =>
    dsimp [Neg.neg, neg]
    dsimp [NonEmpty.neg]
    have remember(x: Int): x.neg = -x := rfl
    dsimp [concrete]
    match xl, xh with
    | (xl: Int), (xh: Int) =>
      simp only [WithBot.coe_le_coe, WithTop.coe_le_coe, WithTop.neg, WithBot.neg]
      grind
    | ⊥, ⊤ => simp only [bot_le, le_top, and_self, Set.setOf_true, WithTop.neg, WithBot.neg]
    | ⊥, (_: Int)
    | (_: Int), ⊤ =>
      simp only [remember, bot_le, WithTop.coe_le_coe, true_and, WithTop.neg, WithBot.coe_le_coe,
        WithBot.neg, le_top, and_true]
      grind
  | ⊥ =>
    simp only [Neg.neg, concrete, Set.preimage_empty, neg]

@[simp, grind=]
theorem concrete_neg(x: Interval): (-x).concrete = - x.concrete := by rw [←neg_correct]

-- TODO: Clean up this horrible proof
lemma add_correct
: gc.IsBestBinAbstraction (· + ·) (· + ·)
:= by
  /-   PROOF SKETCH (of the tedious part)

  (xl,yh)                         (q-yh,yh)               (xh,yh)
         ↘                             ▼                 ↙
           ┌───┬───┬───┬───┬───┬───┬───╲───┬───┬───┬───┐ ───yh
           │   │   │   │   │   │   │   │ ╲ │   │   │   │
           ├───┼───┼───┼───┼───┼───┼───┼───╲───┼───r───┤
           │   │   │   │   │   │   │   │   │ ╲ │   │ ╲ │
(xl,s-xl)► ╲───┼───┼───┼───p───┼───┼───┼───┼───╲───┼───╲ ◄(xh,s-yh)
           │ ╲ │   │   │   │ ╲ │   │   │   │   │ ╲ │   │
           ├───╲───┼───┼───┼───╲───┼───┼───┼───┼───q───┤
           │   │ ╲ │   │   │   │ ╲ │   │   │   │   │   │
           ├───┼───s───┼───┼───┼───╲───┼───┼───┼───┼───┤
           │   │   │   │   │   │   │ ╲ │   │   │   │   │
           └───┴───┴───┴───┴───┴───┴───╲───┴───┴───┴───┘ ───yl
         ↗ │                           ▲               │ ↖
  (xl,yl)  │                      (p-yl,yl)            │  (xh,yl)
           │                                           │
           xl                                          xh

  -/
  intros x y
  match x, y with
  | .mk xl xh xinv, .mk yl yh yinv =>
    dsimp only [HAdd.hAdd]; dsimp only [Add.add, add]
    dsimp only [HAdd.hAdd]; dsimp only [Add.add, NonEmpty.add]
    dsimp only [Int.add_def, concrete, Set.image2_add]
    apply le_antisymm
    · intros e e_h
      obtain ⟨e₁, e₁_x, e₂, e₂_y, rfl⟩ := e_h
      simp only [Set.mem_setOf_eq] at e₁_x e₂_y
      simp only [Set.mem_setOf_eq, WithBot.coe_add, WithTop.coe_add]
      constructor
      · apply add_le_add <;> simp only [*]
      · apply add_le_add <;> simp only [*]
    · intros e e_h
      simp only [Set.mem_setOf_eq] at e_h
      apply Set.mem_add.mpr
      match xl, xh, yl, yh with
      | (xl: Int), xh, yl, (yh: Int) =>
        /-
            ┌────
            │\ \
            │\
        -/
        simp only [WithBot.hle_iff_coe_le, WithBot.hle_iff_le_coe] at *
        if h: e ≤ xl + yh then
          -- We are below the main diagonal
          -- Could probably collapse this under the case `yn = ⊤`
          refine ⟨xl, ?_, e - xl, ?_, add_sub_cancel _ _⟩
          · simpa only [WithBot.coe_le_coe, Set.mem_setOf_eq, le_refl, true_and] using xinv
          · simp only [WithTop.coe_le_coe, Set.mem_setOf_eq, tsub_le_iff_right, add_comm, and_true,
              h]
            -- Pretty much done
            match yl with
            | (yl: Int) =>
              have remember_add(x y: Int): WithBot.some (x + y) = x + y := rfl
              simp only [←remember_add, WithBot.coe_le_coe, ge_iff_le] at *
              grind only
            | ⊥ => constructor
        else
          refine ⟨e-yh, ?_, yh, ?_, sub_add_cancel _ _⟩
          · simp only [WithBot.coe_le_coe, Set.mem_setOf_eq]
            match xh with
            | (xh: Int) =>
              have remember_add(x y: Int): WithTop.some (x + y) = x + y := rfl
              simp only [←remember_add, not_le, WithTop.coe_le_coe, implies_true,
                tsub_le_iff_right] at *
              grind only
            | ⊤ =>
              simp only [le_top, and_true, ge_iff_le]
              grind only
          · simpa only [WithTop.coe_le_coe, Set.mem_setOf_eq, le_refl, and_true] using yinv
      | (xl: Int), xh, yl, ⊤ =>
        /-
            │\
            │\
            │\
        -/
        refine ⟨xl, ?_, e - xl, ?_, add_sub_cancel _ _⟩
        · simpa only [WithBot.coe_le_coe, Set.mem_setOf_eq, le_refl, true_and,
          WithBot.hle_iff_coe_le] using xinv
        · simp only [le_top, and_true, Set.mem_setOf_eq]
          match yl with
          | (yl: Int) =>
            have remember_add(x y: Int): WithBot.some (x + y) = x + y := rfl
            simp only [←remember_add, WithBot.coe_le_coe, ge_iff_le] at *
            grind only
          | ⊥ => constructor
      | ⊥, xh, yl, (yh: Int) =>
        /-
            ─────
            \ \ \

        -/
        refine ⟨e-yh, ?_, yh, ?_, sub_add_cancel _ _⟩
        · simp only [bot_le, true_and, Set.mem_setOf_eq]
          match xh with
          | (xh: Int) =>
            have remember_add(x y: Int): WithTop.some (x + y) = x + y := rfl
            simp only [←remember_add, WithBot.bot_add, bot_le, true_and, WithTop.coe_le_coe] at *
            grind only
          | ⊤ => constructor
        · simpa only [WithTop.coe_le_coe, Set.mem_setOf_eq, le_refl, and_true,
          WithBot.hle_iff_le_coe] using yinv
      | ⊥, (xh: Int), (yl: Int), ⊤ =>
        /-
               \│
             \ \│
            ────┘
        -/
        if e ≤ xh + yl then
          refine ⟨e - yl, ?_, yl, ?_, sub_add_cancel _ _⟩
          · simp only [bot_le, WithTop.coe_le_coe, true_and, Set.mem_setOf_eq, tsub_le_iff_right,
            *]
          · simp only [WithBot.coe_le_coe, le_top, and_true, Set.mem_setOf_eq, le_refl]
        else
          refine ⟨xh, ?_, e -xh, ?_, add_sub_cancel _ _⟩
          · simp only [bot_le, WithTop.coe_le_coe, true_and, Set.mem_setOf_eq, le_refl]
          · simp only [WithBot.coe_le_coe, le_top, and_true, Set.mem_setOf_eq]
            grind only
      | ⊥, ⊤, (yl: Int), ⊤ =>
        /-

            \ \ \
            ─────
        -/
        refine ⟨e - yl, ?_, yl, ?_, sub_add_cancel _ _⟩
        · simp only [bot_le, le_top, and_self, Set.setOf_true, Set.mem_univ]
        · simp only [WithBot.coe_le_coe, le_top, and_true, Set.mem_setOf_eq, le_refl]
      | ⊥, (xh: Int), ⊥, ⊤ =>
        /-
              \│
              \│
              \│
        -/
        refine ⟨xh, ?_, e -xh, ?_, add_sub_cancel _ _⟩
        · simp only [bot_le, WithTop.coe_le_coe, true_and, Set.mem_setOf_eq, le_refl]
        · simp only [bot_le, le_top, and_self, Set.setOf_true, Set.mem_univ]
      | ⊥, ⊤, ⊥, ⊤ =>
        /-
            ↑
          ←   →
            ↓
        -/
        exists e
        simp only [bot_le, le_top, and_self, Set.setOf_true, Set.mem_univ, add_eq_left, true_and,
          exists_eq]
  | ⊥, _ | .mk .., ⊥ =>
    simp only [concrete, Set.empty_add, Set.add_empty]
    rfl

@[simp, grind=]
theorem concrete_add(x y: Interval): (x + y).concrete = x.concrete + y.concrete := by
  rw [←add_correct]

lemma NonEmpty.sub_eq_add_neg(x y: NonEmpty)
: x - y = x + (-y)
:= by
  rcases x with ⟨⟨xl, xh⟩, xinv⟩
  rcases y with ⟨⟨yl, yh⟩, yinv⟩
  cases yl <;> cases yh <;>
  cases xl <;> cases xh <;>
  rfl

lemma sub_eq_add_neg(x y: Interval)
: x - y = x + (-y)
:= by
  match x, y with
  | .mk xl xh xinv, .mk yl yh yinv =>
    dsimp only [HSub.hSub, HAdd.hAdd, Neg.neg]
    simp only [Sub.sub, Add.add, sub, add, neg, NonEmpty.sub_eq_add_neg]
  | ⊥, _
  | .mk .., ⊥ =>
    rfl

theorem sub_correct
: gc.IsBestBinAbstraction (· - ·) (· - ·)
:= by
  intros x y
  have := add_correct x (-y)
  have := neg_correct y
  dsimp only at *
  rw [sub_eq_add_neg, _root_.sub_eq_add_neg]
  simp only [add_correct, neg_correct]

@[simp, grind=]
theorem concrete_sub(x y: Interval): (x - y).concrete = x.concrete - y.concrete := by
  rw [←sub_correct]

lemma mul_correct
: gc.IsBinAbstraction (· * ·) (· * ·)
:= by
  sorry

lemma div_correct
: gc.IsBinAbstraction (· / ·) (· / ·)
:= by
  sorry

#synth SemilatticeSup (WithBot Int)
#synth Max (WithBot Int)

theorem NonEmpty.refineEq_correct (x y: Interval.NonEmpty)
: (refineEq x y).concrete ⊆ { e | e ∈ Interval.concrete x
                                  ∧ (∃ e' ∈ Interval.concrete y, e = e') }
:= by
  rcases x with ⟨⟨xl, xh⟩, xinv⟩
  rcases y with ⟨⟨yl, yh⟩, yinv⟩
  dsimp only [refineEq, Min.min]
  dsimp [meet, ofPair]
  split <;> rename_i cond
  · dsimp [concrete]
    intros e e_x
    simp only [↓existsAndEq, and_true, Set.mem_setOf_eq]
    simp only [sup_le_iff, le_inf_iff, Set.mem_setOf_eq] at e_x
    grind
  · dsimp [concrete]
    apply Set.empty_subset

theorem NonEmpty.refineLe_correct (x y: Interval.NonEmpty)
: (refineLe x y).concrete ⊆ { e | e ∈ Interval.concrete x
                                  ∧ (∃ e' ∈ Interval.concrete y, e ≤ e') }
:= by
  rcases x with ⟨⟨xl, xh⟩, xinv⟩
  rcases y with ⟨⟨yl, yh⟩, yinv⟩
  dsimp [refineLe, ofPair]
  split <;> rename_i cond
  · dsimp [concrete]
    intros e e_x
    simp only [le_inf_iff, Set.mem_setOf_eq] at e_x
    simp only [Set.mem_setOf_eq]
    simp only [WithBot.hle_min_iff] at *
    constructor
    · grind only
    · match yl with
      | (yl: Int) =>
        exists (yl ⊔ e)
        simp only [WithBot.hle_iff_coe_le] at yinv
        simp only [WithBot.coe_sup, le_sup_left, WithTop.coe_sup, sup_le_iff, and_self,
          le_sup_right, yinv, e_x]
      | ⊥ =>
        exists e
        simp only [bot_le, and_self, le_refl, e_x]
  · dsimp [concrete]
    apply Set.empty_subset

attribute [-simp] WithBot.coe_one WithTop.coe_one WithBot.coe_add
theorem NonEmpty.refineLt_correct (x y: Interval.NonEmpty)
: (refineLt x y).concrete ⊆ { e | e ∈ Interval.concrete x
                                  ∧ (∃ e' ∈ Interval.concrete y, e < e') }
:= by
  dsimp only [refineLt]
  simp only [concrete_sub, concrete_ofNat, Nat.cast_one, Set.sub_singleton, Set.image_subset_iff,
    Set.preimage_setOf_eq, Order.sub_one_lt_iff]
  rintro e e_ref
  have := NonEmpty.refineLe_correct (x + 1) y e_ref
  have remember(x y: NonEmpty): (x + y : NonEmpty) = (x: Interval) + (y: Interval) := rfl
  simp only [remember, Set.mem_setOf_eq] at this
  -- TODO: I don't want WithBot.add to appear here! CURR
  have t2:= concrete_add x (1: NonEmpty)
  -- The issue here is `WithBot.add` being used. In particular, `WithBot.coe_add`
  -- Should I maybe reuse that definition?
  dsimp [HAdd.hAdd] at this
  dsimp [Add.add] at this
  sorry

theorem NonEmpty.refineGe_correct (x y: Interval.NonEmpty)
: (refineGe x y).concrete ⊆ { e | e ∈ Interval.concrete x
                                  ∧ (∃ e' ∈ Interval.concrete y, e ≥ e') }
:= by
  sorry

theorem NonEmpty.refineGt_correct (x y: Interval.NonEmpty)
: (refineGt x y).concrete ⊆ { e | e ∈ Interval.concrete x
                                  ∧ (∃ e' ∈ Interval.concrete y, e > e') }
:= by
  dsimp [refineGt]
  -- TODO: Possibly use some kind of correctness for add here
  sorry

-- TODO: Refactor `ValueDomain.compare` and `CompareOp`'s to use less
-- operations, before doing proofs here.
theorem refine_correct (ord : CompareOp) (x y: Interval)
: (x.refine ord y).concrete ⊆ { e | e ∈ x.concrete
                                  ∧ (∃ e' ∈ y.concrete, ord.toProp e e') }
:= by
  fun_cases (x.refine ord y) with
  | case1 x y =>
    apply NonEmpty.refineEq_correct
  | case2 x y =>
    apply NonEmpty.refineLe_correct
  | case3 x y =>
    apply NonEmpty.refineLt_correct x y
  | case4 x y =>
    apply NonEmpty.refineGe_correct x y
  | case5 x y =>
    apply NonEmpty.refineGt_correct x y
  | case6 x y =>
    sorry
  | case7
  | case8 =>
    simp only [concrete, Set.mem_empty_iff_false, false_and, Set.setOf_false,
      subset_refl, concrete, Set.mem_empty_iff_false, false_and, exists_const,
      and_false, Set.setOf_false, subset_refl]

theorem rand_correctness (l? r?: Option Int)
: { e | (∀ l ∈ l?, l ≤ e) ∧ (∀ r ∈ r?, e ≤ r)} ⊆ (rand l? r?).concrete
:= by
  simp only [Option.mem_def, concrete]
  fun_cases (rand l? r?)
  <;> intros e e_l
  · simp only [Option.some.injEq, forall_eq', Set.mem_setOf_eq] at e_l
    rename_i x y
    have: x ≤ y := by cases e_l; trans <;> assumption
    simp only [ofPair, this, WithBot.coe_hle_coe, reduceDIte, Set.mem_setOf_eq, WithBot.coe_le_coe, WithTop.coe_le_coe, e_l]
    trivial
  · simpa only [bot_le, WithTop.coe_le_coe, true_and, Set.mem_setOf_eq, reduceCtorEq,
    IsEmpty.forall_iff, implies_true, Option.some.injEq, forall_eq'] using e_l
  · simpa only [WithBot.coe_le_coe, le_top, and_true, Set.mem_setOf_eq, Option.some.injEq,
    forall_eq', reduceCtorEq, IsEmpty.forall_iff, implies_true] using e_l
  · simp only [bot_le, le_top, and_self, Set.setOf_true, Set.mem_univ]

end OperationCorrectness
