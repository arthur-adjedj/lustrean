#import "@preview/touying:0.6.1": *
#import themes.metropolis: *

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

#include("language-extensions.typ")
#include("abstract-interpreter.typ")
#include("concrete-interpreter.typ")
