import Mathlib.Order.GaloisConnection.Defs

/-!
# Galois Connection

See [wikipedia](https://en.wikipedia.org/wiki/Galois_connection).

A Galois connection between two partially ordered sets A and C
(called respectively _abstract domain_ and _concrete domain_)
is a pair of functions α: C → A and γ: A → C such that

                ∀ a c, α c ≤ a ↔ c ≤ γ a

The function α gives an abstract representation to the concrete
element c, while γ gives the concrete representation of the
abstract element α. In practice, abstract domains act as a type
of approximation of the elements in the concrete domain. The
previous condition guarantees that α gives the best abstraction
possible for any c, that is

                  α c = ⊓ { a : A // c ≤ γ a }

where ⊔ identifies the greatest lower bound (if it exists).

Galois connections are relevant in abstract interpretation since
they give a relation between the domain we want to reason about
and the approximation we are able to do so with.

We take the Galois connection definition from Mathlib, and make
new definitions here which are specific to its use in abstract
interpretation.
-/
variable {A C: Type}[PartialOrder A][PartialOrder C]{γ: A → C}{α: C → A}

namespace GaloisConnection

/-- A function `g` is an abstraction of `f` if it the concretization
of its outputs contain the result of concretizing its inputs. In short,
if it is sound. -/
abbrev IsAbstraction (_gc: GaloisConnection α γ)(f: C → C) (g: A → A) :=
  ∀ a, f (γ a) ≤ γ (g a)

/-- A function `g` is an abstraction of `f` if it is a natural
transformation (when seeing the concretization and abstraction
functions as functors between preorders). In short, if it is
sound and complete. -/
abbrev IsBestAbstraction (_gc: GaloisConnection α γ)(f: C → C) (g: A → A) :=
  ∀ a, f (γ a) = γ (g a)

@[inherit_doc IsAbstraction]
abbrev IsBinAbstraction (_gc: GaloisConnection α γ)(f: C → C → C) (g: A → A → A) :=
  ∀ a a', f (γ a) (γ a') ≤ γ (g a a')

@[inherit_doc IsBestAbstraction]
abbrev IsBestBinAbstraction(_gc: GaloisConnection α γ) (f: C → C → C) (g: A → A → A) :=
  ∀ a a', f (γ a) (γ a') = γ (g a a')

end GaloisConnection


/-- A Galois embedding is a Galois connection for which
concreticising and abstracting successively over an abstract
element does not make us loose precision. As a useful corolary,
if the concretization of two abstract elements are related in
a concrete domain of a Galois embedding, they are related in
the abstract domain. This can be useful in proofs, since it's
easier to reason in the concrete domain.  -/
abbrev GaloisEmbedding(γ: A → C)(α: C → A) := GaloisInsertion γ α
