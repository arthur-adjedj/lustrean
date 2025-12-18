#import "@preview/touying:0.6.1": *

#let desc(content) = {
  set text(fill: red.lighten(30%))
  content
}

= Abstract interpretation
New domains

== Preliminaries
#desc[
Some information about the existing work.
- Definitions for lattices
]
== New additions
#desc[
Description of the new additions being made, mainly:
  - Inclusion of mathlib (Although this is not a contribution perse, it is a different design decision that will keep popping up when talking about the other domains. I also feel like it's important to mention that we're reusing Mathlib, since I feel that Mathlib is one of the big current selling points of Lean, and it's cool that we're able to reuse some of the tooling there.)
  - Sign domain
  - Partition domain #emoji.hourglass.flow

// Maybe we can also talk a bit about the implementation? Not going through the proofs directly, but maybe talk about how using `grind` felt for the proofs, or go over how things are tested. More software engineering stuff.
 
]

== Sign domain
#desc[
Talk about the Galois connection, and the proven correctness of all our operations.
  This last point is an addition with respect to the other domains present.

Also brief explanation of how it works and why it's interesting.
  - It's a simpler version of the interval domain
  - It's finite and distributive (complete under disjunction)
  - Since it's finite, it can be used with the Partition domain
]


== Partition domain
#desc[
Talk about the design decisions, how it's implemented, what restrictions it
  imposes on the "condition" domain ($D_0$). Maybe also offer a description of
  the choice between `Std.HashMap` and `Std.ExtHashMap`.
]
