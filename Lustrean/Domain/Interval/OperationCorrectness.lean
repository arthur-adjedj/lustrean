import Lustrean.Domain.Interval.Galois -- Galois connection of Interval domain
import Lustrean.Domain.Interval.Operations -- Arithmetic operaitons
import Lustrean.Domain.Interval.ValueDomain -- Value domain operations
import Lustrean.Domain.GaloisConnection -- Extra definitions on Galois connections
import Mathlib.Algebra.Group.Pointwise.Set.Basic -- Set operations

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

end OperationCorrectness
