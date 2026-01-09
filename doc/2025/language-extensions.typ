= Extending `Lustrean`
New primitives

// `pre`, →, `fby`
== `pre`

=== Syntax.lean
```lean
syntax " pre " lustre_expr : lustre_expr
```

=== Reify.lean

```lean
inductive MonOp where
  | «pre»
  deriving Repr, Inhabited

namespace MonOp
protected def toString : MonOp → String
  | «pre» => "pre"
```

#pagebreak()
=== Normalize.lean

```lean
partial def elabExprAux {n m : Nat} (nod : NodeN n m) : Indicise.Expr n m → NormalizeM (AuxExpr n m)
| .mon_op .pre ⟨e, _⟩ => do
    let ⟨m', _, e, nod⟩ ← elabExprAux nod e
    let ⟨m', _, x, nod⟩ ← addVarIfNotBvar default e nod
    return {
      m' := m'
      e := .simple <| .var (.old_bound_var x)
      nod := nod
    }
```

== `fby` and →

=== Syntax.lean

```lean
syntax:35 lustre_expr:36 " fby " lustre_expr:35 : lustre_expr
syntax:35 lustre_expr:36 " -> " lustre_expr:35 : lustre_expr
```

=== Reify.lean

```lean
namespace Reify
inductive BinOp where
  | fby
  | arr
  deriving Repr, Inhabited

namespace BinOp
protected def toString : BinOp → String
  | .fby => "fby"
  | .arr => "->"
```

=== Normalize.lean

```lean
partial def elabExprAux {n m : Nat} (nod : NodeN n m) : Indicise.Expr n m → NormalizeM (AuxExpr n m)
  | .bin_op .fby ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, _, e₂, nod⟩ ← elabExprAux nod (e₂.upcast m_leq_m₁)
    let ⟨m', _, x, nod⟩ ← addVarIfNotBvar default e₂ nod
    let cond := .cmp_op .eq (.var .step) (.interval 0 0)
    return {
      m' := m'
      e := .ite cond (e₁.upcast <| by omega) (.var <| .old_bound_var x)
      nod := nod
    }
```

#pagebreak()
```lean
  | .bin_op .arr ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, _, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast m_leq_m₁)
    let cond := .cmp_op .eq (.var .step) (.interval 0 0)
    return {
      m' := m₂
      e := .ite cond (e₁.upcast <| by omega) (e₂.upcast <| by omega)
      nod := nod
    }
```
== Rejecting ill-formed programs

=== Examples

```lustre
node f(x) = x where
```

```lustre
node f(x,x) = y where
```

```lustre
node f(x) = y,y where
```
→ here we can redefine `z = y` in the body

```lustre
node f() where
  x = 0
  x = 1
```

#pagebreak()
=== Implementation

```lean
def elabNode (s : TSyntax `lustre_node) : CoreM (&Node) :=
  withTraceNode `Lustrean.Elab.Reify
    (msg := fun e =>
      return m!"{exceptEmoji e} elabNode\n{s}\n⇒\n{if let .ok n := e then toMessageData n else ""}") do
  match s with
  | `(lustre_node| node $name($inputs:ident,*) $[= $output_vars,*]? $[guard $guards*]?
                   where $decls* $[assert $asserts*]?) =>
    let name := ⟨name.getId, name⟩
    let input_vars := inputs.getElems.map fun x => ⟨x.getId, x⟩

    /- we reject programs with input having repetitions -/
    if !input_vars.allDiff then throwIllFormedSyntax
```
#pagebreak()
```
let bound_vars ← decls.mapM fun
  | `(lustre_node_decl| $vars:ident,* = $expr:lustre_expr) => do pure {
    names := vars.getElems.map fun var => ⟨var.getId, var⟩
    value := ← elabExpr expr
  }
  | ref => withRef ref throwUnsupportedSyntax

/- we reject programs with multiple redefinitions of the same variable -/
if !(bound_vars.map (BoundVars.names)).allDiff then throwIllFormedSyntax

let output_vars : Array &Name := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
```
#pagebreak()
```lean
    /- we reject programs with output having repetitions -/
    if !output_vars.allDiff then throwIllFormedSyntax

    /- we reject programs with input ∩ output ≠ ø -/
    if !(intersect (input_vars.map (Variable.name) ) output_vars).isEmpty then throwIllFormedSyntax

    let guards ← guards.getD #[] |>.mapM elabBoolExpr
    let asserts ← asserts.getD #[] |>.mapM elabBoolExpr
    return ⟨{name, input_vars, bound_vars, output_vars, guards, asserts}, s⟩
  | _ =>
    throwUnsupportedSyntax
```

== Type checking

- pour l'instant, `int` and `bool`, avec une possibilité d'étendre le typesystem facilement
- opérations arithmétiques → type check pour avoir des `int` (statiquement)
- opérations booléennes → type check pour avoir des `bool`
- comparaisons → type check pour avoir les mêmes types

=== Design choices

`int` are really implemented as singleton intervals in the reify phase (during elaboration)

`bool` were represented as `0` or anything else other than `0`.

The type-checker does not care about the actual implementation, and focuses only on the carried type (anyway, it is thrown away at runtime).

== TODO

=== Language extensions

`when`, `merge`

=== Type checking clocks

Currently hard to do because we currently rely on a program-wide clock, which we cannot type without doing a complete overhaul of the system.
