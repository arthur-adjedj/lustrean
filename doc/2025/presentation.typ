#import "@preview/touying:0.6.1": *
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
#title-slide()

#include("arthur.typ")
#include("language-extensions.typ")
#include("abstract-interpreter.typ")
