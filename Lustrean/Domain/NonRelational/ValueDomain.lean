import Lustrean.Domain.Domain

namespace Lustrean
class ValueDomain (α : Type)[BEq α]
extends Add α, Neg α, Mul α, Sub α, Div α, BoundedLattice α,
  ToString α, WidenLawful α, NarrowLawful α
where
  -- interval [a, b]
  rand : Option Int → Option Int → α
  nil : α
  dec_bot: DecidablePred (· = bot) := by
    exact fun x => (inferInstance: Decidable (x = ⊥))
  -- compare op x y = (x', y') where
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' }
  compare : CompareOp → α → α → α × α

export ValueDomain (nil)

namespace ValueDomain
variable {α : Type} [BEq α][ι: ValueDomain α]

instance: DecidablePred (· = (⊥: α)) := ι.dec_bot

-- backward operations :
-- backward_op x y r = (x', y') where
-- x' = { v ∈ x | ∃ v' ∈ y, v op v' ∈ r }
-- y' = { v' ∈ y | ∃ v ∈ x, v op v' ∈ r }
def backwardNeg (x r : α) : α := (-r) ⊓ x

def backwardAdd (x y r : α) : α × α :=
  (x ⊓ (r - y), y ⊓ (r - x))

def backwardSub (x y r : α) : α × α :=
  (x ⊓ (r + y), y ⊓ (x - r))

def backwardMul (x y r : α) : α × α :=
  (x ⊓ (r / y), y ⊓ (r / x))

def backwardDiv (x y r : α) : α × α :=
  (x ⊓ (r * y), y ⊓ (x / r))
end ValueDomain

end Lustrean
