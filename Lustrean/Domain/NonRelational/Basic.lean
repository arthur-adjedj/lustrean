import Lustrean.Domain.NonRelational.ValueDomain
import Misc

namespace Lustrean

/--
  Given an abstract domain `α` over values `C`, constructs a
  non-relational abstract domain of `Set C`.
-/
inductive NonRelational (α : Type) [BEq α][ValueDomain α]: Nat → Type where
| non_rel {n: Nat}(env : { env : Vector α (n+1) // ∀ i : Fin (n+1), env.get i ≠ ⊥ }) : NonRelational α (n+1)
| bot {n: Nat}: NonRelational α n

namespace NonRelational

variable {α : Type} {n : Nat} [BEq α]
variable [ι : ValueDomain α]

instance : BEq (NonRelational α n) where
  beq
  | .non_rel env, .non_rel env' => env == env'
  | .bot,         .bot          => true
  | _,            _             => false


protected def toString : NonRelational α n → String
  | .bot => "⊥"
  | .non_rel env => toString env.val.toArray

instance : ToString (NonRelational α n) where
  toString := NonRelational.toString

def coalesce (env : Vector α n) : NonRelational α n :=
  match n with
  | 0 => .bot
  | m+1 =>
    if H: ∀ (i: Fin (m+1)), env.get i ≠ ⊥ then
      .non_rel ⟨env, H⟩
    else
      .bot

def mapNil (x: NonRelational α n)(f : Vector α n → Vector α n) : NonRelational α n :=
  match x with
  | .non_rel x => coalesce <| f x.val
  | .bot => .bot

section ops
variable (x y : NonRelational α n)
def map2Nil (f : Vector α n → Vector α n → Vector α n) : NonRelational α n :=
  match x, y with
  | .non_rel x, .non_rel y => coalesce (f x.val y.val)
  | _, _ => .bot

protected def add :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i + y.get i

instance : Add (NonRelational α n) where
  add := NonRelational.add

protected def neg :=
  mapNil x fun x => Vector.ofFn fun i => -x.get i

instance : Neg (NonRelational α n) where
  neg := NonRelational.neg

protected def sub :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i - y.get i

instance : Sub (NonRelational α n) where
  sub := NonRelational.sub

protected def mul :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i * y.get i

instance : Mul (NonRelational α n) where
  mul := NonRelational.mul

protected def div :=
  map2Nil x y fun x y => Vector.ofFn fun i => x.get i / y.get i

instance : Div (NonRelational α n) where
  div := NonRelational.div

theorem join_neq_bot : ∀ (x y : { env : Fin n → α // ∀ i, env i ≠ ⊥}) i,
  x.val i ⊔ y.val i ≠ ⊥ := by
  intros x y i
  let ⟨y, H⟩ := y
  simp [BoundedLattice.join_eq_bot_iff_bot]
  intros
  apply H

def join : NonRelational α n := match x, y with
  | .non_rel ⟨x, H⟩, .non_rel ⟨y, _⟩ =>
    .non_rel <| .mk (Vector.ofFn fun i => x.get i ⊔ y.get i) <| (by
      intros i
      simp only [Vector.get_of_fn_fin, ne_eq, BoundedLattice.join_eq_bot_iff_bot, not_and]
      intro
      exfalso
      apply H
      assumption)
  | .bot, z | z, .bot => z

def meet : NonRelational α n := map2Nil x y fun x y => Vector.ofFn fun i => x.get i ⊓ y.get i
end ops

def top : NonRelational α n :=
  if h: (⊤: α) = (⊥: α) then
    .bot
  else
    match n with
    | 0 => .bot
    | m+1 =>
      .non_rel ⟨Vector.replicate _ ⊤, by simp only [Vector.get_mk_vector_fin, ne_eq, h,
        not_false_eq_true, implies_true]⟩

end NonRelational
end Lustrean
