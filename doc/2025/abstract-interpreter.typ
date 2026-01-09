#import "@preview/touying:0.6.1": *
#import "@preview/cades:0.3.1": qr-code
#import "@preview/sicons:16.0.0": *

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
== Sign domain - Demo!

Consider the following:

#align(center)[
#show raw.where(lang: "lustre"): it => [
  #let ident-color = rgb(214, 58, 73)
  #let regex-union(..elements) = "(" + elements.pos().flatten().map(x => "\\b" + x + "\\b").join("|") + ")"
  #show regex(regex-union(
    ("lustre", "node", "where", "assert", "if", "then", "else")
  )) : set text(fill: ident-color)
  #it
]

```lustre
lustre 
  node f(x) = y
  where   y = if x ≥ 0 then x + 1 else x - 1
  assert  y ≠ 0
``` 
]

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

```lean
def gc: GaloisConnection Sign.abstract Sign.concrete := by
    rintro X ⟨p,z,n⟩
    constructor <;> grind [LE.le]
```

#uncover(2)[
  #align(center)[
    #text(emoji.party, size: 4em)
  ]
]

---

```lean
noncomputable
instance ge: GaloisEmbedding abstract concrete := gc.toGaloisInsertion <| by
  rintro ⟨hasPos, z, hasNeg⟩
  simp [Sign.abstract, Sign.concrete, LE.le, Sign.incl]
  apply And.intro
  · if h: hasPos then apply Or.inr; exists 1  else grind
  · if h: hasNeg then apply Or.inr; exists -1 else grind
```

---

#align(top)[
```lean
def add(a b : Sign): Sign :=
  if a = .None ∨ b = .None then
    .None
  else
    {
      hasZero := a.hasZero && b.hasZero ||
                 a.hasNeg  && b.hasPos  ||
                 a.hasPos  && b.hasNeg
      -- Safe since we assume the other is non-empty
      hasPos  := a.hasPos  || b.hasPos
      -- Safe since we assume the other is non-empty
      hasNeg  := a.hasNeg  || b.hasNeg
    }
```
]

#align(bottom)[
```lean
theorem add_correct
: Sign.gc.IsBinAbstraction (· + ·) Sign.add
:= by // ...
```
]
---

#align(top)[
```lean
def neg(a: Sign): Sign := {
  a with
  hasNeg := a.hasPos
  hasPos := a.hasNeg
}
```
]

#align(bottom)[
```lean
def neg_complete
: Sign.gc.IsBestAbstraction (-·) Sign.neg
:= by
  intros x
  simp only [Neg.neg, Sign.concrete, Set.preimage_setOf_eq, Sign.neg]
  grind [Sign.neg, Sign.concrete]
```
]

---

#align(top)[
```lean
def mul (a b: Sign): Sign := {
    hasPos  := a.hasPos && b.hasPos ||
               a.hasNeg && b.hasNeg
    hasZero := a.hasZero || b.hasZero,
    hasNeg  := a.hasNeg && b.hasPos ||
               a.hasPos && b.hasNeg
  }
```
]

#align(bottom)[
```lean
theorem mul_correct
: Sign.gc.IsBinAbstraction (· * ·) Sign.mul
:= by // ...
```
]

---

For more examples, see the github repository

#align(center)[
#qr-code("https://github.com/arthur-adjedj/lustrean", width: 8cm)
#link("https://github.com/arthur-adjedj/lustrean")[#box(fill: gray.lighten(70%), stroke: gray.lighten(40%), radius: 5pt, outset: 4pt)[#text()[
    // #sicon(slug: "github", size: 1em)
    arthur-adjedj/lustrean]]]
]

== Mathlib - What else can we get out of Mathlib?

#grid(columns: (2fr, 1fr), inset: 1em)[
#align(top)[
#image("resources/mathlib-lattice.png", width: 17.5cm)
]
][
  Seems to have all we need, we're just lacking laws about $top$ and $bot$


]

#grid(columns: (2fr, 1fr), inset: 1em)[
#align(top)[
#image("resources/mathlib-bounded-order.png", width: 17.5cm)
]
][
  We can combine this with `Lattice` to obtain something close to our 
  `BoundedLattice` definition!
]

---

```lean
def BoundedLattice.ofLatticeAndBoundedOrder {α: Type}[Lattice α][BoundedOrder α] 
: BoundedLattice α where
  // ...
  join_commutative := by grind
  join_associative := by grind
  join_absorption x y := by grind only [inf_le_left, sup_of_le_left]
  join_bot := by grind only [bot_le, sup_of_le_left]
  join_top := by simp
  meet_commutative := by grind
  meet_associative := by grind
  meet_absorption x y := by simp
  meet_bot := by simp
  meet_top := by simp
  join_is_lub := by grind [left_eq_inf, sup_le_iff]
  meet_is_glb := by grind [left_eq_inf, le_inf_iff]
```

== Partition domain

#text(fill: white)[Demo]

---

#align(center)[
```lean
def concrete(p: Partition D₀ D₁): Set C :=
  { e | ∀ d : D₀, e ∈ γ₀ d → e ∈ γ₁ (p d)}
```
\

```lean
def abstract(X: Set C): Partition D₀ D₁ :=
  λ x ↦ α₁ (X ∩ γ₀ x)
```
]

---

```lean 
def gcOfSubterms(gc₀: GaloisConnection α₀ γ₀)(gc₁: GaloisConnection α₁ γ₁)
: GaloisConnection (β := Partition D₀ D₁) (α := Set C)
  (abstract (α₁ := α₁) (γ₀ := γ₀))
  (concrete (γ₀ := γ₀) (γ₁ := γ₁)) := by
  have α₀_mon := gc₀.monotone_l
  have α₁_mon := gc₁.monotone_l
  have γ₀_mon := gc₀.monotone_u
  have γ₁_mon := gc₁.monotone_u
  intros X Y
  dsimp [LE.le, abstract, concrete, Set.Subset, Subset]
  constructor <;> intros hyp
  · intros e e_X z e_Cz
    specialize hyp z
    rw [gc₁] at hyp; apply hyp; simp [*]
  · intros z; rw [gc₁]; intros e e_int
    simp only [Set.mem_inter_iff] at e_int
    apply hyp <;> simp [*]

```

---


