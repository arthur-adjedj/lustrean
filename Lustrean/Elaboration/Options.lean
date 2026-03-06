import Lean
import Lustrean.Elaboration.Syntax

-- TODO: Consider reimplementing using
-- https://lean-lang.org/doc/api/Lean/Elab/Tactic/Config.html#Lean.Elab.Tactic.configElab

namespace Lustrean.Elaboration

open Lean

variable {m : Type → Type} [Monad m] [MonadError m]

/--
  Enumeration of all available domains. So far, the
  supported domains are:
  - **`UndefinedInterval`** The non-relational domain of
    undefined values, using integer intervals as a
    value domain.
  - **`Sign`** The non-relational domain of signs of
    integer intervals.
-/
inductive AvailableDomain where
| UndefinedInterval
| Sign
deriving DecidableEq, Repr, Inhabited

namespace AvailableDomain

/-- Parse supported domains from an identifier syntax -/
def ofSyntax: TSyntax `ident → m AvailableDomain
| `(ident| UndefinedInterval) => pure .UndefinedInterval
| `(ident| Sign) => pure .Sign
| value => throwErrorAt value s!"Unrecognized option: \"{value.getId}\""

end AvailableDomain

/--
  Options for a `lustre` statement. These include
  - dom: The name of the domain to be used.
-/
structure Options: Type where
  dom: AvailableDomain := .UndefinedInterval
  deriving DecidableEq, Repr, Inhabited

def Options.ofSyntax (stx : TSyntax `lustre_ops): m Options := do
  let `(lustre_ops| $[$keys := $values],*) := stx
    | Elab.throwUnsupportedSyntax
  let mut opts: Options := {}
  for key in keys, value in values do
    match key with
    | `(ident| domain) => do
      let value ← AvailableDomain.ofSyntax value
      opts := {opts with dom := value}
    | _ =>
      throwErrorAt key s!"Unrecognized option: \"{key.getId}\""
  return opts