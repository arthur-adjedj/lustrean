import Lustrean.Elaboration.Reify
import Lustrean.Elaboration.Inline
import Misc

open Lean
open Meta Elab
open Std (HashMap)

-- Indicise phase.  This is responsible for resolving all the variable names, and replace them
-- with indices in the local context.  This is akin to a de Bruijn transformation, except that it
-- must take into account the fact that all the bindings are mutually recursive.

namespace Lustrean.Elaboration
namespace Indicise
inductive VarRef (n m : Nat) where
  | input_var (k : Fin n)
  | bound_var (k : Fin m)
  deriving Repr

def VarRef.upcast {n m m' : Nat} (h : m ≤ m') : VarRef n m → VarRef n m'
  | .input_var k => .input_var k
  | .bound_var k => .bound_var (k.castLE h)

mutual
inductive Expr (n m : Nat) where
  | interval (lb : &LowerBound) (up : &UpperBound)
  | var (k : &(VarRef n m))
  | mon_op (op : MonOp) (e : &(Expr n m))
  | bin_op (op : Reify.BinOp) (left right : &(Expr n m))
  | ite (cond : &(BoolExpr n m)) (tb : &(Expr n m)) (eb : &(Expr n m))
  deriving Repr, Inhabited

inductive BoolExpr (n m : Nat) where
  | cmp_op (op : CmpOp) (left right : &(Expr n m))
  | bin_op (op : BoolBinOp) (left right : &(BoolExpr n m))
  deriving Repr, Inhabited
end

mutual
variable {n m m' : Nat} (h : m ≤ m')

def Expr.upcast : Expr n m → Expr n m'
  | .interval lb up => .interval lb up
  | .var ⟨v, ref⟩ => .var ⟨v.upcast h, ref⟩
  | .mon_op op ⟨e, ref⟩ => .mon_op op ⟨e.upcast, ref⟩
  | .bin_op op ⟨e₁, ref₁⟩ ⟨e₂, ref₂⟩ => .bin_op op ⟨e₁.upcast, ref₁⟩ ⟨e₂.upcast, ref₂⟩
  | .ite ⟨cond, ref_c⟩ ⟨e₁, ref₁⟩ ⟨e₂, ref₂⟩ => .ite ⟨cond.upcast, ref_c⟩ ⟨e₁.upcast, ref₁⟩ ⟨e₂.upcast, ref₂⟩

def BoolExpr.upcast : BoolExpr n m → BoolExpr n m'
  | .cmp_op op ⟨l, ref_l⟩ ⟨r, ref_r⟩ => .cmp_op op ⟨l.upcast, ref_l⟩ ⟨r.upcast, ref_r⟩
  | .bin_op op ⟨l, ref_l⟩ ⟨r, ref_r⟩ => .bin_op op ⟨l.upcast, ref_l⟩ ⟨r.upcast, ref_r⟩
end

/-- A local variable in a node, that is, a variable that is only available in the local scope.
    This can be either an input variable, or a locally bound variable.  -/
structure Var where
  name : &Name
  deriving Repr, Inhabited

/-- A locally bound variable.  This is a local variable that is bound to a value -/
structure BoundVar (n m : Nat) extends Var where
  value : &(Expr n m)
  deriving Repr, Inhabited

mutual
variable {n m : Nat} (input_vars : Vector Var n) (bound_vars : Vector (BoundVar n m) m)

def Expr.toString : Expr n m → String
  | .interval lb up => s!"[{lb}, {up}]"
  | .var ⟨.input_var k, _⟩ => input_vars[k].name.toString
  | .var ⟨.bound_var k, _⟩ => bound_vars[k].name.toString
  | .mon_op op ⟨e, _⟩ => s!"({op} {e.toString})"
  | .bin_op op ⟨l, _⟩ ⟨r, _⟩ => s!"({l.toString} {op} {r.toString})"
  | .ite ⟨cond, _⟩ ⟨tb, _⟩ ⟨eb, _⟩ => s!"(if {cond.toString} then {tb.toString} else {eb.toString})"

def BoolExpr.toString : BoolExpr n m → String
  | .cmp_op op ⟨left, _⟩ ⟨right, _⟩
  | .bin_op op ⟨left, _⟩ ⟨right, _⟩ => s!"({left.toString} {op} {right.toString})"
end

structure Node where
  name : Name
  n : Nat
  m : Nat
  input_vars : Vector Var n
  bound_vars : Vector (BoundVar n m) m
  output_vars : Array &(VarRef n m)
  guards : Array &(BoolExpr n m)
  asserts : Array &(BoolExpr n m)
  deriving Repr, Inhabited

namespace Node
protected def getElem {n m} (nod : Node) (vr : VarRef n m) (p : n = nod.n ∧ m = nod.m) : Var :=
  match vr with
  | .input_var k => nod.input_vars[k]
  | .bound_var k => nod.bound_vars[k].toVar

instance (n m : Nat) : GetElem Node (VarRef n m) Var fun nod _ => n = nod.n ∧ m = nod.m where
  getElem := Node.getElem
end Node

section
open Std.Format

variable {n m : Nat} (input_vars : Vector Var n) (bound_vars : Vector (BoundVar n m) m)

def formatInputVars (input_vars :  Vector Var n) : Format :=
  paren (joinSep (input_vars.map Var.name |>.toList) ",")

def formatBoundVars (bound_vars : Vector (BoundVar n m) m) : Format :=
  Std.Format.indentD <| "where " ++ Std.Format.indentD (joinSep (bound_vars.toList.map formatBvar) Format.line)
where
  formatBvar bvar :=
    (format bvar.name.value) ++ " = " ++ Expr.toString input_vars bound_vars bvar.value

def formatOutputVars (nod : Node) (output_vars : Array &(VarRef n m)) : Format :=
  if output_vars.size = 0 then "" else
  " = " ++ joinSep (output_vars.map (nod[·.value]!.name) |>.toList) ","

def formatGuards (guards : Array &(BoolExpr n m)) : Format :=
  if guards.size = 0 then "" else
  Std.Format.indentD <| "guard" ++ Std.Format.indentD (joinSep (guards.map (BoolExpr.toString input_vars bound_vars ∘ WithRef.value) |>.toList) Format.line)

def formatAsserts (asserts : Array &(BoolExpr n m)) : Format :=
  if asserts.size = 0 then "" else
  Std.Format.indentD <| "assert" ++ Std.Format.indentD (joinSep (asserts.map (BoolExpr.toString input_vars bound_vars ∘ WithRef.value) |>.toList) Format.line)

instance : ToFormat Node where
  format n :=
    (format ("node " ++ n.name.toString)) ++
    (formatInputVars n.input_vars) ++
    (formatOutputVars n n.output_vars)  ++
    (formatGuards n.input_vars n.bound_vars n.guards) ++
    (formatBoundVars n.input_vars n.bound_vars) ++
    (formatAsserts n.input_vars n.bound_vars n.asserts)
end

section
variable {n m : Nat}
variable (local_vars : HashMap Name (VarRef n m))

  mutual
partial def elabExpr (e : &Inline.Expr) : CoreM &(Expr n m) :=
  e.mapM fun
    | .interval lb up => return .interval lb up
    | .var ⟨name, ref⟩ => do
      let some k := local_vars.get? name | throwErrorAt ref "unbound variable"
      return .var ⟨k, ref⟩
    | .mon_op op e => do
      let e ← elabExpr e
      return .mon_op op e
    | .bin_op op left right => do
      let left ← elabExpr left
      let right ← elabExpr right
      return .bin_op op left right
    | .ite cond tb eb => do
      let cond ← elabBoolexpr cond
      let tb ← elabExpr tb
      let eb ← elabExpr eb
      return .ite cond tb eb

partial def elabBoolexpr (b : &Inline.BoolExpr) : CoreM &(BoolExpr n m) :=
  b.mapM fun
    | .cmp_op op left right => do
      let left ← elabExpr left
      let right ← elabExpr right
      return .cmp_op op left right
    | .bin_op op left right => do
      let left ← elabBoolexpr left
      let right ← elabBoolexpr right
      return .bin_op op left right
end
end

def elabNode (nod : &Inline.Node) : CoreM (&Node) :=
  nod.mapM fun nod =>
  withTraceNode `Lustrean.Elab.Indicise
    (msg := fun e =>
      return m!"{exceptEmoji e} elabNode\n{nod}\n⇒\n{if let .ok n := e then toMessageData n else ""}") do
  let input_vars := Vector.mk nod.input_vars rfl
  let bound_vars := Vector.mk nod.bound_vars rfl
  let n := input_vars.size
  let m := bound_vars.size
  let mut env : HashMap Name (VarRef n m) := {}
  for h : i in [0:n] do
    env := env.insert input_vars[i].name <| .input_var ⟨i, Membership.get_elem_helper h rfl⟩
  for h : i in [0:m] do
    env := env.insert bound_vars[i].name <| .bound_var ⟨i, Membership.get_elem_helper h rfl⟩
  let input_vars := input_vars.map fun { name, } => { name }
  let bound_vars ← bound_vars.mapM fun var => do
    let { name, value } := var
    let value ← elabExpr env value
    return { name, value }
  let output_vars ← nod.output_vars.mapM (m := CoreM) fun var : &Name => do
    let some i := env.get? var | throwErrorAt var.ref "unbound variable"
    return ⟨i, var.ref⟩
  let guards ← nod.guards.mapM <| elabBoolexpr env
  let asserts ← nod.asserts.mapM <| elabBoolexpr env
  return { name := nod.name, n, m, input_vars, bound_vars, guards, asserts, output_vars }

def elabLustre (nodes : Array (&Inline.Node)) : CoreM (Array (&Node)) :=
  nodes.mapM elabNode
end Indicise

end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab.Indicise (inherited := true)
