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
variable [ι : ValueDomain α]

section ops
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
  | .binop e₁ op e₂ =>
    let i₁ := eval e₁
    let i₂ := eval e₂
    match op with
    | .iadd => i₁ + i₂
    | .isub => i₁ - i₂
    | .imul => i₁ * i₂
    | .idiv => i₁ / i₂

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
    | .binop e₁ op e₂ =>
      let i₁ := eval x e₁
      let i₂ := eval x e₂
      let (r₁, r₂) := match op with
      | .iadd => ι.backwardAdd i₁ i₂ r
      | .isub => ι.backwardSub i₁ i₂ r
      | .imul => ι.backwardMul i₁ i₂ r
      | .idiv => ι.backwardDiv i₁ i₂ r
      backwardEval e₁ r₁ ⊓ backwardEval e₂ r₂

  def guard : BExpr n → NonRelational α n
  | .random | .const true => x
  | .const false => ⊥
  | .compare e₁ op e₂ =>
    let i₁ := eval x e₁
    let i₂ := eval x e₂
    let (r₁, r₂) := ι.compare op i₁ i₂
    backwardEval x e₁ r₁ ⊓ backwardEval x e₂ r₂
  | .or b₁ b₂ => guard b₁ ⊔ guard b₂
  | .and b₁ b₂ => guard b₁ ⊓ guard b₂
end ops

instance : Domain (NonRelational α n) where
  nb_var := n
  dec_bot x := match h: x with
  | .non_rel _ => isFalse (by simp)
  | .bot       => isTrue  (by simp)

  assign := assign
  guard := guard
  -- TODO: pourquoi ça n'infère pas ??
  covering_left := WidenLawful.covering_left
  covering_right := WidenLawful.covering_right

  bounding_low := NarrowLawful.bounding_low
  bounding_high := NarrowLawful.bounding_high

end NonRelational
end Lustrean
