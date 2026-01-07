import Lustrean.Domain.Domain
import Lustrean.Domain.NonRelational
import Lustrean.Domain.Undefined
import Lustrean.Domain.Integers
import Lustrean.Domain.Domain
-- import Lustrean.Domain.Sign
-- import Lustrean.Domain.Interval
-- import Lustrean.Imp

-- open Lustrean NonRelational

-- def zero {n} : IExpr n := IExpr.const 0
-- def one {n} : IExpr n := IExpr.const 1
-- def zero_one {n} : IExpr n := IExpr.rand (some 0) (some 1)

-- #eval (BoundedLattice.bot : Interval [])
-- #eval (BoundedLattice.top : Interval [])
-- #eval eval (α := Interval []) (n := 0) ⊥ zero
-- #eval eval (α := Interval []) (n := 0) ⊥ zero_one
-- #eval eval (α := Interval []) (n := 0) ⊥ zero ⊑ eval (α := Interval []) (n := 0) ⊥ zero_one
-- #eval eval (α := Interval []) (n := 0) ⊥ (IExpr.cmpop zero .le zero_one)
-- #eval eval (α := Interval []) (n := 0) ⊥ (IExpr.cmpop one .le zero)
