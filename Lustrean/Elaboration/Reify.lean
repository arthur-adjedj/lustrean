import Lustrean.Elaboration.Syntax
import Misc.Lean
import Misc.WithRef

open Lean Meta Elab

namespace Lustrean.Elaboration

-- Reify phase.  This is the bridge between the parser and the elaborator.

inductive LowerBound where
  | int (n : Int)
  | minf
  deriving Repr, Inhabited

namespace LowerBound
protected def toString : LowerBound → String
  | int n => toString n
  | .minf => "-∞"

instance : ToString LowerBound where
  toString := LowerBound.toString

instance (n : Nat) : OfNat LowerBound n where
  ofNat := int n
end LowerBound

inductive UpperBound where
  | int (n : Int)
  | pinf
  deriving Repr, Inhabited

namespace UpperBound
protected def toString : UpperBound → String
  | int n => toString n
  | .pinf => "∞"

instance : ToString UpperBound where
  toString := UpperBound.toString

instance (n : Nat) : OfNat UpperBound n where
  ofNat := int n
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
  | etrue | efalse
  deriving Repr, Inhabited

partial def Expr.toString : Expr → String
  | .interval {value := .int n,..} {value := .int k,..} => if n = k then s!"{n}" else s!"[{n},{k}]"
  | .interval lb up => s!"[{lb},{up}]"
  | .var v => v.value.toString
  | .mon_op op e => s!"{op.toString} {Expr.toString e}"
  | .bin_op op e₁ e₂ => s!"{Expr.toString e₁} {op.toString} {Expr.toString e₂}"
  | .node n args => s!"{n.value}({args.map (Expr.toString ∘ WithRef.value) |>.toStringNoBrackets})"
  | .ite cond tb eb => s!"if {Expr.toString cond} then {Expr.toString tb} else {Expr.toString eb}"
  | .cmp_op op left right => s!"{Expr.toString left.value} {op.toString} {Expr.toString right.value}"
  | .etrue => "true"
  | .efalse => "false"

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

inductive Ty where
  | int : Ty
  | bool : Ty
deriving BEq

namespace Ty
protected def toString : Ty → String
  | .int => "ℕ"
  | .bool => "Bool"

instance : ToString Ty where
  toString := Ty.toString

structure VarsEnv where
  map : Std.HashMap Name Ty
  deriving Inhabited

namespace VarsEnv
def merge (e1 e2 : VarsEnv) : CoreM VarsEnv := do
  let mergedMap ← e2.map.foldM (init := e1.map) fun acc name ty2 => do
    match acc.get? name with
    | some ty1 =>
      if ty1 == ty2 then
        return acc -- They match, no action needed
      else
        throwError m!"Type conflict for variable '{name}': '{ty1}' vs '{ty2}'"
    | none =>
      return acc.insert name ty2
  return { map := mergedMap }

protected def toString (env : VarsEnv) : String :=
  env.map.toList |>
  List.map (fun (name,ty) => s!"{name}:{ty}") |>
  String.intercalate ", "

instance : ToString VarsEnv where
  toString := VarsEnv.toString

end VarsEnv

abbrev NodeEnv := Std.HashMap Name (Array Ty × Array Ty)

instance : ToString (Array Ty) where
  toString := fun lTy =>
    lTy.map Ty.toString |>
    Array.toList |>
    String.intercalate ", "

namespace NodeEnv
protected def toString (env : NodeEnv) : String :=
  env.toList |>
  List.map (fun (name, in_types, out_types) => 
    s!"{name}({in_types}) -> ({out_types})"
  )
  |> String.intercalate "\n"

instance : ToString NodeEnv where
  toString := NodeEnv.toString

instance : ToString (Expr × VarsEnv × Option Ty) where
  toString := fun (e,vars,ty?) =>
    match ty? with
    | some ty => s!"{e}:{ty} where {vars}"
    | none => s!"{e} where {vars}"

partial def elabExpr (s : TSyntax `lustre_expr) (nodeEnv : NodeEnv) (varEnv : VarsEnv) (expectedType? : Option Ty) : CoreM (&Expr × VarsEnv × (Option Ty)) :=
  WithRef.withRef s do
  withTraceNode `Lustrean.Elab.Reify (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{s}\n⇒\n{e.toOption.map toString}") do
    match s with
    | `(lustre_expr| true) =>
      return (Expr.etrue,varEnv,some Ty.bool)
    | `(lustre_expr| false) =>
      return (Expr.efalse,varEnv,some Ty.bool)
    | `(lustre_expr| $n:num) =>
      let n₁: &LowerBound := ⟨.int n.getNat, n⟩
      let n₂: &UpperBound := ⟨.int n.getNat, n⟩
      return (Expr.interval n₁ n₂, varEnv, some Ty.int)
    | `(lustre_expr| [$lbs, $ups]) =>
      let lb ← match lbs with
        | `(lustre_lower_bound| -∞) => pure LowerBound.minf
        | `(lustre_lower_bound| $n:num) => pure <| LowerBound.int n.getNat
        | _ => throwUnsupportedSyntax
      let up ← match ups with
        | `(lustre_upper_bound| ∞) => pure UpperBound.pinf
        | `(lustre_upper_bound| $n:num) => pure <| UpperBound.int n.getNat
        | _ => throwUnsupportedSyntax
      return (Expr.interval ⟨lb, lbs⟩ ⟨up, ups⟩,varEnv,some Ty.int)
    | `(lustre_expr| $v:ident) => return (Expr.var ⟨v.getId, v⟩,varEnv,none)
    | `(lustre_expr| $l + $r) =>
      let (left, lenv, lty) ← elabExpr l nodeEnv varEnv (some Ty.int)
      let (right, renv, rty) ← elabExpr r nodeEnv varEnv (some Ty.int)

      if lty != some Ty.int then
        throwError m!"application type mismatch, expected{indentD (toMessageData Ty.int)}\nbut has{indentD (toMessageData lty)}"
      if rty != some Ty.int then
        throwError m!"application type mismatch, expected{indentD (toMessageData Ty.int)}\nbut has{indentD (toMessageData rty)}"

      let env <- lenv.merge renv

      return (Expr.bin_op .add left right, env, some Ty.int)
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
    | `(lustre_expr| $l:lustre_expr ≤ $r:lustre_expr) | `(lustre_expr| $r:lustre_expr ≥ $l:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .leq left right
    | `(lustre_expr| $l:lustre_expr = $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .eq left right
    | `(lustre_expr| $l:lustre_expr ≠ $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .mon_op .neg ⟨.cmp_op .eq left right, s⟩
    | `(lustre_expr| $l:lustre_expr < $r:lustre_expr) | `(lustre_expr| $r:lustre_expr > $l:lustre_expr) =>
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
  registerTraceClass `Lustrean.Elab.Reify (inherited := .true)
