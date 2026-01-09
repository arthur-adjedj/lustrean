#import "@preview/touying:0.6.1": *
#import "@preview/cades:0.3.1": qr-code
#import "@preview/sicons:16.0.0": *

#import themes.metropolis: *

#let lean-extra-keywords = (
  "return", "for", "mut", "as", "partial_fixpoint",
  "decreasing_by", "termination_by", "rec", "where",
  "deriving",
)
#let lean-tactics = (
  "native_decide", "scalar_tac", "revert", "progress",
  "simp", "case", "decide", "congr", "split"
)
#show raw.where(lang: "lean"): it => [
  #let ident-color = rgb(214, 58, 73)
  #let regex-union(..elements) = "(" + elements.pos().flatten().map(x => "\\b" + x + "\\b").join("|") + ")"
  #show regex(regex-union(
    lean-extra-keywords,
    lean-tactics
  )) : set text(fill: ident-color)
  // I hardcode progress* because * is considered a word boundary (\W),
  // and so it seems to mess up with the \b added to the keywords by 
  // `regex-union`
  #show regex("\\bprogress\*"): set text(fill: ident-color)
  #show regex("\\bprogress\*\?"): set text(fill: ident-color)
  #show regex("\\bsorry\\b"): set text(fill: rgb(100%, 0%, 100%))
  #it
]

#show raw.where(lang: "lustre"): it => [
  #let ident-color = rgb(214, 58, 73)
  #let regex-union(..elements) = "(" + elements.pos().flatten().map(x => "\\b" + x + "\\b").join("|") + ")"
  #show regex(regex-union(
    ("lustre", "node", "where", "assert", "if", "then", "else", "pre", "->")
  )) : set text(fill: ident-color)
  #it
]


#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Lustrean],
    subtitle: [Lean + Lustre],
    // logo: image(
    //   "./resources/lean-logo-official-TM-transparent-2400x900.png",
    //   width: 5em,
    // ),
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
#title-slide()

  #align(center)[
  #let github-qrcode = qr-code("https://github.com/arthur-adjedj/lustrean", width: 8cm)
  #github-qrcode
  #link("https://github.com/arthur-adjedj/lustrean")[
      #box(fill: gray.lighten(70%), stroke: gray.lighten(40%), radius: 5pt, outset: 4pt)[
      #box(inset: 2pt)[#sicon(slug: "github", size: 1em)]
      #text(baseline: -6pt)[
      arthur-adjedj/lustrean
      ]
    ]
    ]
  ]

---

#include "arthur.typ"
#include "language-extensions.typ"
#include "abstract-interpreter.typ"

---

  #align(center)[
  #let github-qrcode = qr-code("https://github.com/arthur-adjedj/lustrean", width: 8cm)
  #github-qrcode
  #link("https://github.com/arthur-adjedj/lustrean")[
      #box(fill: gray.lighten(70%), stroke: gray.lighten(40%), radius: 5pt, outset: 4pt)[
      #box(inset: 2pt)[#sicon(slug: "github", size: 1em)]
      #text(baseline: -6pt)[
      arthur-adjedj/lustrean
      ]
    ]
    ]
  ]
