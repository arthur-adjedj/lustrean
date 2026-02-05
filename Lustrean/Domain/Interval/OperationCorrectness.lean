import Lustrean.Domain.Interval.Galois -- Galois connection of Interval domain
import Lustrean.Domain.Interval.Operations -- Arithmetic operaitons
import Lustrean.Domain.Interval.ValueDomain -- Value domain operations
import Lustrean.Domain.GaloisConnection -- Extra definitions on Galois connections
import Mathlib.Algebra.Group.Pointwise.Set.Basic -- Set operations

attribute [-simp] bot_eq_zero' bot_eq_one' «Prop».bot_eq_false

namespace Lustrean.Interval

section OperationCorrectness
open Pointwise

lemma add_correct
: gc.IsBinAbstraction (· + ·) (· + ·)
:= by
  sorry

lemma sub_correct
: gc.IsBinAbstraction (· - ·) (· - ·)
:= by
  sorry

lemma neg_correct
: gc.IsAbstraction (- ·) (- ·)
:= by
  sorry

lemma mul_correct
: gc.IsBinAbstraction (· * ·) (· * ·)
:= by
  sorry

lemma div_correct
: gc.IsBinAbstraction (· / ·) (· / ·)
:= by
  sorry

theorem refine_correct (ord : CompareOp) (x y: Interval)
: (x.refine ord y).concrete ⊆ { e | e ∈ x.concrete
                                  ∧ (∃ e' ∈ y.concrete, ord.toProp e e') }
:= by
  sorry

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
