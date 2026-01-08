import Lustrean.Domain.Domain
import Lustrean.Domain.NonRelational.ValueDomain
import Lustrean.Domain.NonRelational.Basic
import Lustrean.Domain.NonRelational.JoinLemmas
import Lustrean.Domain.NonRelational.MeetLemmas
import Lustrean.Domain.NonRelational.Lattice
import Lustrean.Domain.NonRelational.Narrow
import Lustrean.Domain.NonRelational.Widen
import Misc

namespace Lustrean

namespace NonRelational
variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α] [DecidableEq α]
variable (x : NonRelational α n)

def get (i : Fin n) : α := match x with
  | .non_rel x => x.val.get i
  | .bot => ⊥

def update (i : Fin n) (a : α) : NonRelational α n :=
  x.mapNil fun x => x.set i a

def eval : IExpr n → α
  | .nil => nil
  | .var i => get x i
  | .rand a b => ι.rand a b
  | .neg e => - eval e
  | .not e => if e matches .rand (some (-1)) (some (-1)) then 1 else -1
  | .binop e₁ op e₂ =>
    let i₁ := eval e₁
    let i₂ := eval e₂
    match op with
    | .add => i₁ + i₂
    | .sub => i₁ - i₂
    | .mul => i₁ * i₂
    | .div => i₁ / i₂
    | .or => i₁ ⊔ i₂
    | .and => i₁ ⊓ i₂
  | .cmpop e₁ op e₂ =>
    let i₁ := eval e₁
    let i₂ := eval e₂
    match op with --TODO surely this is wrong
      | .eq  => if i₁ = i₂ then 1 else -1
      | .neq => if i₁ = i₂ then -1 else 1
      | .le  => if i₁ ⊑ i₂ then 1 else -1
      | .lt  => if i₁ ⊑ i₂ ∧ i₁ ≠ i₂ then 1 else -1
      | .ge  => if i₂ ⊑ i₁ then 1 else -1
      | .gt  => if i₂ ⊑ i₁ ∧ i₁ ≠ i₂ then 1 else -1


def assign (i : Fin n) (e : IExpr n) : NonRelational α n :=
  update x i <| eval x e

def backwardEval (e : IExpr n) (r : α) : NonRelational α n :=
  have : DecidablePred BoundedLattice.IsBot := ι.dec_bot -- help class inference
  match e with
  | .nil => if ι.IsBot (r ⊓ nil)
    then ⊥
    else x
  | .var i => update x i ((get x i) ⊓ r)
  | .rand a b => if ι.IsBot (r ⊓ (ι.rand a b))
    then ⊥
    else x
  | .neg e =>
    let i := eval x e
    let r := ι.backwardNeg i r
    backwardEval e r
  | .not e =>
    let i := eval x e
    let r := ι.backwardNot i r
    backwardEval e r
  | .binop e₁ op e₂ =>
    let i₁ := eval x e₁
    let i₂ := eval x e₂
    let (r₁, r₂) := match op with
    | .add => ι.backwardAdd i₁ i₂ r
    | .sub => ι.backwardSub i₁ i₂ r
    | .mul => ι.backwardMul i₁ i₂ r
    | .div => ι.backwardDiv i₁ i₂ r
    | .or => (i₁ ⊔ i₂,i₁ ⊔ i₂)
    | .and => (i₁ ⊓ i₂,i₁ ⊓ i₂)
    backwardEval e₁ r₁ ⊓ backwardEval e₂ r₂
  | .cmpop e₁ op e₂ =>
    let i₁ := eval x e₁
    let i₂ := eval x e₂
    let (r₁, r₂) := ι.compare op i₁ i₂
    backwardEval e₁ r₁ ⊓ backwardEval e₂ r₂

instance : Domain (NonRelational α n) where
  nb_var := n
  dec_bot x := match h: x with
  | .non_rel _ => isFalse (by simp)
  | .bot       => isTrue  (by simp)

  assign := assign
  guard := (backwardEval · · ⊥)
end NonRelational
end Lustrean
