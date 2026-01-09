#import "@preview/touying:0.6.1": *
#import themes.metropolis: *
#import emoji: *


#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Lustrean],
    subtitle: [Lean + Lustre],
    logo: image(
      "./resources/lean-logo-official-TM-transparent-2400x900.png",
      width: 5em
    ),
    author: [
      Arthur ADJEDJ \
      Fernando LEAL SANCHEZ \
      Léo LEESCO
    ],
    date: datetime(year: 2026, month: 1, day: 9),
  ),
    config-colors(
      primary: rgb("#eb811b"),
      primary-light: rgb("#d6c6b7"),
      secondary: rgb("#23373b"),
      neutral-lightest: rgb("#fafafa"),
      neutral-dark: rgb("#23373b"),
      neutral-darkest: rgb("#23373b"),
    ),
)

== What is Lustrean ?

#grid(rows: (50%,50%),
  align(center,image("resources/lustrean.png"))
,
[
Lustrean is an abstract interpreter of a precise semantics of a core subset
of Lustre in Lean.
- It embeds a subset of Lustre as a DSL in Lean.
- It gives a precise semantics of that language, even to non-statically
  schedulable programs.
- It interprets them in an abstract domain to check for the absence of
  runtime errors.
])
= Refactors, debugging, and the hopes for a concrete interpreter

== The need for refactors

The original Lustrean project was great a great toy project, but needed lots of reworks to make it scalable and maintainable:
- Did not respect the usual code conventions 
  #uncover("2-")[- Refactored the entire project to respect conventions, and added lots of docs]
- Lots of hardcoded features, no good debugging infrastructure
  #uncover("3-")[
  - Added great debug traces that allowed us to fix many bugs in the initial implementation
  - Added a test suite and a CI to check for breakages]
- Could not rely on Mathlib, or any of the lean recent features
  #uncover("4-")[
  - Made the project compatible with the most recent release (v4.27.0-rc1) 
  - Refactored the formalisation of Domain Theory to rely on Mathlib (See Fernando's part)]


== Debugging

Lean is extensible, let's make great use of it
- 

== The hope for a concrete interpreter

Lean has dependent types
Objective: use those to make a correct-by-construction concrete interpreter 
How: using CoStreams and heterogeneous lists:

```lean

def HList : List (Type u) → Type u
  | [] => PUnit
  | α::tl => α × HList tl

structure CoStream (σ α : Type _) where
  init : σ
  step : σ → α × σ
```

== Concrete interpretatation example

 
#grid(columns : (25%,80%),[
```haskell
node f(i) = o where
    x = pre i + 1
    o = x+i
```   
],scale(95%)[
```lean
def x {σ} (i : CoStream σ ValType) : CoStream (HList [ValType, σ]) ValType :=
  let pre_i := i.pre none
  let one := CoStream.const (some 1)
  let pre_i_add_1 := pre_i.map₂ (c₂ := one) (· + ·)
  pre_i_add_1

def o {σ} (i : CoStream σ ValType) (x : CoStream (HList [ValType, σ]) ValType) : CoStream (HList [HList [ValType, σ], σ]) ValType :=
  let x_add_1 := x.map₂ (c₂ := i) (· + ·) 
  x_add_1

def f {σ} (i : CoStream σ ValType) :=
  let x := x i
  let o := o i x
  o
```])

== Issues

Good ideas, bad execution.
- The codebase does not already have a scheduler, having a concrete interpreter would mean suddenly refusing more programs
#pause
- Turns out dependent types are hard..
#pause
- I spent too much time on refactors instead of this  #emoji.face.melt

#pause
In the end:

- Basic API for `CoStreams` and `HList`, allowing for efficient implementation of lustre programs #text(style: "italic")[by hand]
- Hopes and dreams I will find time to complete the implementation someday