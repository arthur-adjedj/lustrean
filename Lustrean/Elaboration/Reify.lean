import Lustrean.Elaboration.Syntax
import Misc.Lean
import Misc.WithRef

open Lean Meta Elab

namespace Lustrean.Elaboration

-- Reify phase.  This is the bridge between the parser and the elaborator.

inductive LowerBound where
  | nat (n : Nat)
  | minf
  deriving Repr, Inhabited

namespace LowerBound
protected def toString : LowerBound → String
  | .nat n => toString n
  | .minf => "-∞"

instance : ToString LowerBound where
  toString := LowerBound.toString

instance (n : Nat) : OfNat LowerBound n where
  ofNat := .nat n
end LowerBound

inductive UpperBound where
  | nat (n : Nat)
  | pinf
  deriving Repr, Inhabited

namespace UpperBound
protected def toString : UpperBound → String
  | .nat n => toString n
  | .pinf => "∞"

instance : ToString UpperBound where
  toString := UpperBound.toString

instance (n : Nat) : OfNat UpperBound n where
  ofNat := .nat n
end UpperBound

inductive MonOp where
  | neg
  | «pre»
  deriving Repr, Inhabited

namespace MonOp
protected def toString : MonOp → String
  | neg => "-"
  | «pre» => "pre"

instance : ToString MonOp where
  toString := MonOp.toString
end MonOp

inductive CmpOp where
  | eq
  | leq
  | lt
  deriving Repr, Inhabited

namespace CmpOp
protected def toString : CmpOp → String
  | eq => "="
  | leq => "≤"
  | lt => "<"

instance : ToString CmpOp where
  toString := CmpOp.toString
end CmpOp

namespace Reify
inductive BinOp where
  | add
  | sub
  | mul
  | fby
  | arr
  | and
  | or
  deriving Repr, Inhabited

namespace BinOp
protected def toString : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .fby => "fby"
  | .arr => "->"
  | and => "∧"
  | or => "∨"

instance : ToString BinOp where
  toString := BinOp.toString
end BinOp
inductive Expr : Type where
  | interval (lb : &LowerBound) (up : &UpperBound)
  | var (name : &Name)
  | mon_op (op : MonOp) (e : &Expr)
  | bin_op (op : BinOp) (left right : &Expr)
  | node (name : &Name) (args : Array (&Expr))
  | ite (cond : &Expr) (tb : &Expr) (eb : &Expr)
  | cmp_op (op : CmpOp) (left right : &Expr)
  deriving Repr, Inhabited

partial def Expr.toString : Expr → String
  | .interval {value := .nat n,..} {value := .nat k,..} => if n = k then s!"{n}" else s!"[{n},{k}]"
  | .interval lb up => s!"[{lb},{up}]"
  | .var v => v.value.toString
  | .mon_op op e => s!"{op.toString} {Expr.toString e}"
  | .bin_op op e₁ e₂ => s!"{Expr.toString e₁} {op.toString} {Expr.toString e₂}"
  | .node n args => s!"{n.value}({args.map (Expr.toString ∘ WithRef.value) |>.toStringNoBrackets})"
  | .ite cond tb eb => s!"if {Expr.toString cond} then {Expr.toString tb} else {Expr.toString eb}"
  | .cmp_op op left right => s!"{Expr.toString left.value} {op.toString} {Expr.toString right.value}"

instance : ToString Expr where
  toString := Expr.toString

structure Variable where
  name : &Name
  deriving Repr, Inhabited

structure BoundVars where
  names : Array (&Name)
  value : &Expr
  deriving Repr, Inhabited

structure Node where
  name : &Name
  input_vars : Array Variable
  bound_vars : Array BoundVars
  output_vars : Array (&Name)
  guards : Array (&Expr)
  asserts : Array (&Expr)
deriving Repr, Inhabited

section

open Std.Format

def formatInputVars (input_vars : Array Variable) : Format :=
  paren (joinSep (input_vars.map Variable.name |>.toList) ",")

def formatBoundVars (bound_vars : Array BoundVars) : Format :=
  Std.Format.indentD <| "where " ++ Std.Format.indentD (joinSep (bound_vars.toList.map formatBvar) Format.line)
where
  formatBvar bvar :=
    joinSep (bvar.names |>.toList) "," ++ " = " ++ toString bvar.value

def formatOutputVars (output_vars : Array (&Name)) : Format :=
  if output_vars.size = 0 then "" else
  " = " ++ joinSep (output_vars |>.toList) ","

def formatGuards (guards : Array (&Expr)) : Format :=
  if guards.size = 0 then "" else
  Std.Format.indentD <| "guard" ++ Std.Format.indentD (joinSep (guards |>.toList) Format.line)

def formatAsserts (asserts : Array &Expr) : Format :=
  if asserts.size = 0 then "" else
  Std.Format.indentD <| "assert" ++ Std.Format.indentD (joinSep (asserts |>.toList) Format.line)

instance : ToFormat Node where
  format n :=
    (format ("node " ++ n.name.value.toString)) ++
    (formatInputVars n.input_vars) ++
    (formatOutputVars n.output_vars)  ++
    (formatGuards n.guards) ++
    (formatBoundVars n.bound_vars) ++
    (formatAsserts n.asserts)
end


partial def elabExpr (s : TSyntax `lustre_expr) : CoreM &Expr :=
  WithRef.withRef s do
  withTraceNode `Lustrean.Elab.Reify (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{s}\n⇒\n{e.toOption.map toString}") do
    match s with
    | `(lustre_expr| $n:num) =>
      let n₁ := ⟨.nat n.getNat, n⟩
      let n₂ := ⟨.nat n.getNat, n⟩
      return .interval n₁ n₂
    | `(lustre_expr| [$lbs, $ups]) =>
      let lb ← match lbs with
        | `(lustre_lower_bound| -∞) => pure .minf
        | `(lustre_lower_bound| $n:num) => pure <| .nat n.getNat
        | _ => throwUnsupportedSyntax
      let up ← match ups with
        | `(lustre_upper_bound| ∞) => pure .pinf
        | `(lustre_upper_bound| $n:num) => pure <| .nat n.getNat
        | _ => throwUnsupportedSyntax
      return .interval ⟨lb, lbs⟩ ⟨up, ups⟩
    | `(lustre_expr| $v:ident) => return .var ⟨v.getId, v⟩
    | `(lustre_expr| $l + $r) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .add left right
    | `(lustre_expr| $l fby $r) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .fby left right
    | `(lustre_expr| $l -> $r) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .arr left right
    | `(lustre_expr| - $e) =>
      let e ← elabExpr e
      return .mon_op .neg e
    | `(lustre_expr| pre $e) =>
      let e ← elabExpr e
      return .mon_op .pre e
    | `(lustre_expr| $l * $r) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .mul left right
    | `(lustre_expr| $l - $r) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .sub left right
    | `(lustre_expr| $f:ident($args:lustre_expr,*)) =>
      let args ← args.getElems.mapM elabExpr
      return .node ⟨f.getId, f⟩ args
    | `(lustre_expr| if $c then $tb else $eb) =>
      let c ← elabExpr c
      let tb ← elabExpr tb
      let eb ← elabExpr eb
      return .ite c tb eb
    | `(lustre_expr| $l:lustre_expr ≤ $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .leq left right
    | `(lustre_expr| $l:lustre_expr = $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .eq left right
    | `(lustre_expr| $l:lustre_expr < $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .lt left right
    | `(lustre_expr| $l:lustre_expr ∧ $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .and left right
    | `(lustre_expr| $l:lustre_expr ∨ $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .bin_op .or left right
    | _ =>
      throwErrorAt s m!"invalid syntax {s}"

def elabNode (s : TSyntax `lustre_node) : CoreM (&Node) :=
  withTraceNode `Lustrean.Elab.Reify
    (msg := fun e =>
      return m!"{exceptEmoji e} elabNode\n{s}\n⇒\n{if let .ok n := e then toMessageData n else ""}") do
  match s with --  $[assert $asserts*]?
  | `(lustre_node| node $name($inputs,*) $[ = $output_vars:ident,*]? $[ guard $[$guards]*]? where $decls* $[ assert $[$asserts]*]?) =>
    let name := ⟨name.getId, name⟩
    let input_vars := inputs.getElems.map fun x => ⟨x.getId, x⟩
    let bound_vars ← decls.mapM fun
      | `(lustre_node_decl| $vars:ident,* = $expr:lustre_expr) => do pure {
        names := vars.getElems.map fun var => ⟨var.getId, var⟩
        value := ← elabExpr expr
      }
      | ref => withRef ref throwUnsupportedSyntax
    let output_vars := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
    let guards ← guards.getD #[] |>.mapM elabExpr
    let asserts ← asserts.getD #[] |>.mapM elabExpr
    return ⟨{name, input_vars, bound_vars, output_vars, guards, asserts}, s⟩
  | _ =>
    throwUnsupportedSyntax

def elabLustre (nodes : TSyntaxArray `lustre_node) : CoreM (Array (&Node)) :=
  nodes.mapM elabNode

end Reify
end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab.Reify (inherited := true)
