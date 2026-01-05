import Lean.Exception

namespace Lustrean
def CounterT := StateT Nat

namespace CounterT
universe u
variable {m : Type -> Type} [Monad m]


instance : Monad (CounterT m) :=
  inferInstanceAs (Monad (StateT Nat m))
instance [LawfulMonad m] : LawfulMonad (CounterT m) :=
  inferInstanceAs (LawfulMonad (StateT Nat m))
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (CounterT m) :=
  inferInstanceAs (MonadExceptOf ε (StateT Nat m))
instance [Lean.MonadError m] : Lean.MonadError (CounterT m) where
  getRef x := do
    let r ← Lean.MonadRef.getRef
    pure (r,x)
  withRef stx x n := Lean.MonadRef.withRef stx (x n)
  add stx m := pure (stx, m)

variable {α}

def incr : CounterT m Nat := fun c => pure (c, c+1)
protected def run (a : CounterT m α) : m α := do
  let (x, _) ← a 0
  return x

protected def monadLift (x : m α) : CounterT m α :=
  fun c => do return (← x, c)

instance : MonadLift m (CounterT m) where
  monadLift := CounterT.monadLift
end CounterT

abbrev CounterM := CounterT Id
end Lustrean
