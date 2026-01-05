import Lustrean.Elaboration.Syntax
import Misc.Lean

open Lean Meta Elab

-- Reify phase.  This is the bridge between the parser and the elaborator.

namespace Lustrean.Elaboration
structure WithRef (α : Type _) where
  value : α
  ref : Syntax
  deriving Repr, Inhabited

namespace WithRef
prefix:arg "&" => WithRef

-- instance (α : Type _) : Coe (&α) α where
  -- coe := value

instance (α : Type _) : CoeSort &α α where
  coe := value

protected def toString {α} [ToString α] (self : &α) :=
  toString self.value

instance {α} [ToString α] : ToString &α where
  toString := WithRef.toString


instance {α} [ToMessageData α] : ToMessageData &α where
  toMessageData x := toMessageData x.value

protected abbrev map {α β} (self : &α) (f : α → β) : &β where
  ref := self.ref
  value := f self.value

protected abbrev mapM {α β m} [Monad m] (self : &α) (f : α → m β) : m &β := do
  let ⟨value, ref⟩ := self
  let value' ← f value
  return ⟨value', ref⟩

def withRef {α m} [Monad m] (ref : Syntax) (value : m α) : m &α := do
  return {
    value := ← value
    ref
  }

instance {α : Type _} : Membership α &α where
  mem aref a  := a = aref.value

def attach {α : Type _}  (xs : &α) : &{ x // x ∈ xs } :=
  {value := ⟨xs.value,rfl⟩, ref := xs.ref}

def unattach {α : Type _} {p : α → Prop} (xs : &{ x // p x }) : &α  :=
  {value := xs.value.val, ref := xs.ref}

@[wf_preprocess] theorem map_wfParam {α β : _} {xs : &α} {f : α → β} :
  (wfParam xs).map f = xs.attach.unattach.map f := by
rfl

@[wf_preprocess] theorem map_unattach {α  β : _} {P : α → Prop} {xs : &(Subtype P)} {f : α → β} :
  xs.unattach.map f = xs.map fun ⟨x, h⟩ =>
    binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
rfl

theorem sizeOf_lt_of_mem  {α : Type _} {a : α} [inst : SizeOf α] {as : &α}: a ∈ as → sizeOf a < sizeOf as := by
  intro h
  cases as
  cases h
  decreasing_trivial

macro "sizeOf_withRef_dec" : tactic =>
  `(tactic| first
    | with_reducible apply sizeOf_lt_of_mem ; assumption; done
    | with_reducible
        apply Nat.lt_of_lt_of_le (sizeOf_lt_of_mem  ?h)
        case' h => assumption
      simp +arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| sizeOf_withRef_dec)

end WithRef

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

inductive BoolBinOp where
  | and
  | or
  deriving Repr, Inhabited

namespace BoolBinOp
protected def toString : BoolBinOp → String
  | and => "∧"
  | or => "∨"

instance : ToString BoolBinOp where
  toString := BoolBinOp.toString

end BoolBinOp

namespace Reify
inductive BinOp where
  | add
  | sub
  | mul
  | fby
  | arr
  deriving Repr, Inhabited

namespace BinOp
protected def toString : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .fby => "fby"
  | .arr => "->"

instance : ToString BinOp where
  toString := BinOp.toString
end BinOp

mutual
inductive Expr where
  | interval (lb : &LowerBound) (up : &UpperBound)
  | var (name : &Name)
  | mon_op (op : MonOp) (e : &Expr)
  | bin_op (op : BinOp) (left right : &Expr)
  | node (name : &Name) (args : Array (&Expr))
  | ite (cond : &BoolExpr) (tb : &Expr) (eb : &Expr)
  deriving Repr, Inhabited

inductive BoolExpr where
  | cmp_op (op : CmpOp) (left right : &Expr)
  | bin_op (op : BoolBinOp) (left right : &BoolExpr)
  deriving Repr, Inhabited
end

mutual
partial def Expr.toString : Expr → String
  | .interval {value := .nat n,..} {value := .nat k,..} => if n = k then s!"{n}" else s!"[{n},{k}]"
  | .interval lb up => s!"[{lb},{up}]"
  | .var v => toString v.value
  | .mon_op op e => s!"{op.toString} {Expr.toString e}"
  | .bin_op op e₁ e₂ => s!"{Expr.toString e₁} {op.toString} {Expr.toString e₂}"
  | .node n args => s!"{n.value}({args.map (Expr.toString ∘ WithRef.value) |>.toStringNoBrackets})"
  | .ite cond tb eb => s!"if {BoolExpr.toString cond} then {Expr.toString tb} else {Expr.toString eb}"

partial def BoolExpr.toString : BoolExpr → String
  | .cmp_op op left right => s!"{Expr.toString left.value} {op.toString} {Expr.toString right.value}"
  | .bin_op op left right => s!"{BoolExpr.toString left.value} {op.toString} {BoolExpr.toString right.value}"
end

instance : ToString Expr where
  toString := Expr.toString

instance : ToString BoolExpr where
  toString := BoolExpr.toString

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
  guards : Array (&BoolExpr)
  asserts : Array (&BoolExpr)
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

def formatGuards (guards : Array (&BoolExpr)) : Format :=
  if guards.size = 0 then "" else
  Std.Format.indentD <| "guard" ++ Std.Format.indentD (joinSep (guards |>.toList) Format.line)

def formatAsserts (asserts : Array (&BoolExpr)) : Format :=
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

mutual
partial def elabExpr (s : TSyntax `lustre_expr ) : CoreM (&Expr) :=
  WithRef.withRef s do
  withTraceNode `Lustrean.Elab.Reify (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{s}\n⇒\n{e.toOption.map toString}") do
    match s with
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
      let c ← elabBoolExpr c
      let tb ← elabExpr tb
      let eb ← elabExpr eb
      return .ite c tb eb
    | _ =>
      throwErrorAt s m!"{repr s}"

partial def elabBoolExpr (s : TSyntax `lustre_assertion) : CoreM (&BoolExpr) :=
  WithRef.withRef s do
  withTraceNode `Lustrean.Elab.Reify (msg := fun e => return m!"{exceptEmoji e} elabBoolExpr\n{s}\n⇒\n{e.toOption.map toString}") do
  match s with
    | `(lustre_assertion| $l:lustre_expr ≤ $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .leq left right
    | `(lustre_assertion| $l:lustre_expr = $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .eq left right
    | `(lustre_assertion| $l:lustre_expr < $r:lustre_expr) =>
      let left ← elabExpr l
      let right ← elabExpr r
      return .cmp_op .lt left right
    | `(lustre_assertion| $l:lustre_assertion ∧ $r:lustre_assertion) =>
      let left ← elabBoolExpr l
      let right ← elabBoolExpr r
      return .bin_op .and left right
    | `(lustre_assertion| $l:lustre_assertion ∨ $r:lustre_assertion) =>
      let left ← elabBoolExpr l
      let right ← elabBoolExpr r
      return .bin_op .or left right
    | ref =>
      println! s!"{repr ref}"
      withRef ref throwUnsupportedSyntax
end

def elabNode (s : TSyntax `lustre_node) : CoreM (&Node) :=
  withTraceNode `Lustrean.Elab.Reify
    (msg := fun e =>
      return m!"{exceptEmoji e} elabNode\n{s}\n⇒\n{if let .ok n := e then toMessageData n else ""}") do
  match s with
  | `(lustre_node| node $name($inputs:ident,*) $[= $output_vars,*]? $[guard $guards*]?
                   where $decls* $[assert $asserts*]?) =>
    let name := ⟨name.getId, name⟩
    let input_vars := inputs.getElems.map fun x => ⟨x.getId, x⟩
    let bound_vars ← decls.mapM fun
      | `(lustre_node_decl| $vars:ident,* = $expr:lustre_expr) => do pure {
        names := vars.getElems.map fun var => ⟨var.getId, var⟩
        value := ← elabExpr expr
      }
      | ref => withRef ref throwUnsupportedSyntax
    let output_vars := output_vars.map (·.getElems.map (fun var => ⟨var.getId, var⟩)) |>.getD default
    let guards ← guards.getD #[] |>.mapM elabBoolExpr
    let asserts ← asserts.getD #[] |>.mapM elabBoolExpr
    return ⟨{name, input_vars, bound_vars, output_vars, guards, asserts}, s⟩
  | _ =>
    throwUnsupportedSyntax

def elabLustre (nodes : TSyntaxArray `lustre_node) : CoreM (Array (&Node)) :=
  nodes.mapM elabNode

end Reify
end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab.Reify (inherited := true)
