#import "@preview/touying:0.6.1": *

#let desc(content) = {
  set text(fill: red.lighten(30%))
  content
}

= New in the abstract interpreter
The quest towards the partition domain

== Preliminaries
Recap of what we have
#pause 
- Interval value domain
#pause 
- `Undefined` value domain combinator
#pause 
- `NonRelationa` domain combinator

#pause

We want more

== More domains

Two ways to increase the amount of domains we have
- New basic domains #only(2)[#text(fill:red)[← `Sign` value domain]]
- New domain combinators #only(2)[#text(fill:red)[← `Partition` domains]]

== Sign domain - Definition

#image("resources/sign-lattice.jpg")

---
```
Sign             Interval
────             ────────
[⊥]       ↦         ∅
[⊤]       ↦      (-∞, +∞)
[=0]      ↦      [ 0,  0]
[>0]      ↦      [ 0, +∞)
[<0]      ↦      (-∞,  0)
[≥0]      ↦      [ 0, +∞)
[≤0]      ↦      (-∞,  0]
[≠0]      ↦        ????
```
---
```
Sign             Interval
────             ────────
[⊥]       ↦         ∅
[⊤]       ↦      (-∞, +∞)
[=0]      ↦      [ 0,  0]
[>0]      ↦      [ 0, +∞)
[<0]      ↦      (-∞,  0)
[≥0]      ↦      [ 0, +∞)
[≤0]      ↦      (-∞,  0]
[≠0]      ↦     [<0] ⊔ [>0]
```
---

Demo!

== Sign domain - Implementation

We registered new domains by implementing the `ValueDomain` typeclass 
#only("3")[which itself makes use of the `BoundedLattice` typeclass.]

#only("2")[
```lean
class ValueDomain (α : Type)[BEq α] 
extends Add α, Neg α, Mul α, Sub α, Div α, BoundedLattice α, 
        ToString α, WidenLawful α, NarrowLawful α
where
  -- interval [a, b]
  rand : Option Int → Option Int → α
  nil : α
  dec_bot: DecidablePred (· = bot) := by
    exact fun x => (inferInstance: Decidable (x = ⊥))
  -- compare op x y = (x', y') such that
  -- x' = { v ∈ x | ∃ v' ∈ y, v op v' }
  -- y' = { v' ∈ y | ∃ v ∈ x, v op v' }
  compare : CompareOp → α → α → α × α
```
]
#only("3")[
```lean
class BoundedLattice (α : Type) where
  // ...
  join_commutative : ∀ (x y : α), join x y = join y x
  join_associative : ∀ (x y z : α), join (join x y) z = join x (join y z)
  join_absorption  : ∀ (x y : α), join x (meet x y) = x
  join_bot         : ∀ (x : α), join x bot = x
  join_top         : ∀ (x : α), join x top = top
  meet_commutative : ∀ (x y : α), meet x y = meet y x
  meet_associative : ∀ (x y z : α), meet (meet x y) z = meet x (meet y z)
  meet_absorption  : ∀ (x y : α), meet x (join x y) = x
  meet_top         : ∀ (x : α), meet x top = x
  meet_bot         : ∀ (x : α), meet x bot = bot
  non_trivial      : top ≠ bot 
    := by decide
```
]

#speaker-note[
However, for this implementation, I decided to go beyond that, proving the
correctness of all operations.

To do so, we use the concept of a Galois connection.
]

---

#rect(inset: 1em)[
A *Galois connection* between two partially ordered sets $A$ and $C$
(referred to respectively as _abstract domain_ and _concrete domain_)
is a pair of functions $α: C → A$ and $γ: A → C$ such that $∀ (a:A) (c:C)$

$
                α space c ≤ a arrow.l.r.long c ≤ γ space a
$
]


---

#rect(inset: 1em)[
A function $g$ is an #only("2-")[*binary*] #only(3)[*perfect*] *abstraction* of $f$ if the _concretization of 
its outputs_ #alternatives[contains][contains][corresponds to] the result over the concretized inputs. 
#text(fill: gray)[(In short, sound #only(3)[and complete])]
$
  #alternatives[
                  $∀ (a: A), f (γ space a) ≤ γ (g space a)$
  ][
                  $∀ (a a': A), f (γ space a) (γ a') ≤ γ (g space a space a')$
  ][
                  $∀ (a a': A), f (γ space a) (γ a') = γ (g space a space a')$
  ]
$
]

---

#align(center)[
```lean
/-- Abstraction over sets of integers. The only
    information retained is the sign of the elements
    of the set.  -/
structure Sign where mk ::
  hasPos:  Bool := false
  hasZero: Bool := false
  hasNeg:  Bool := false
  deriving DecidableEq, Repr, Inhabited
```
]

---

#image("resources/mathlib-galois-connection.png")

---

#grid(columns: 2, inset: 10pt)[

```lean
@[grind =]
noncomputable 
def abstract(X: Set Int): Sign := {
  hasZero := 0 ∈ X
  hasPos := ∃ z ∈ X, z > 0
  hasNeg := ∃ z ∈ X, z < 0
}
```
][
```lean

@[grind =]
def concrete(a: Sign): Set Int := 
  setOf λ z ↦ match compare z 0 with
  | .lt => a.hasNeg
  | .eq => a.hasZero
  | .gt => a.hasPos
```
]

---
