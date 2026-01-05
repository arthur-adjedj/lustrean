import Lustrean.Elaboration.Reify
import Lustrean.Elaboration.Inline
import Lustrean.Elaboration.Indicise
import Misc

open Lean
open Meta Elab
open Std (HashMap)

-- Normalization phase.  This phase introduces the implicit step variable, used to compile the
-- `->` construct.  It also introduces state variables, that is, variables that represent the
-- persistent state.  They are used to compile the `pre` construct.  It also puts subexpressions
-- into their own variables to ensure every subexpression that requires any persistent state is
-- actually a variable (that is, we name subexpressions that need a persistent state).
--
-- For the sake of simplicity, we aggressively allocate stuff into the persistent state, and not
-- just for variables for which this is useful.

namespace Lustrean.Elaboration

abbrev NormalizeM := CounterT CoreM

namespace Normalize
export Indicise (Var)

inductive VarRef (n m : Nat) where
  | step
  | input_var (k : Fin n)
  | bound_var (k : Fin m)
  | old_bound_var (k : Fin m)
  deriving Repr, Inhabited

def VarRef.upcast {n m m' : Nat} (h : m ≤ m') : VarRef n m → VarRef n m'
  | .step => .step
  | .input_var k => .input_var k
  | .bound_var k => .bound_var <| k.castLE h
  | .old_bound_var k => .old_bound_var <| k.castLE h

def elabVr {n m : Nat} : Indicise.VarRef n m → VarRef n m
  | .input_var k => .input_var k
  | .bound_var k => .bound_var k

inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, Inhabited

  namespace BinOp
protected def toString : BinOp → String
  | add => "+"
  | sub => "-"
  | mul => "*"

instance : ToString BinOp where
  toString := BinOp.toString
end BinOp

section
variable (n m : Nat)

inductive SimpleExpr where
  | interval (lb : LowerBound) (up : UpperBound)
  | var (k : VarRef n m)
  | bin_op (op : BinOp) (left right : SimpleExpr)
  deriving Repr, Inhabited

inductive BoolExpr where
  | cmp_op (op : CmpOp) (left right : SimpleExpr n m)
  | bin_op (op : BoolBinOp) (left right : BoolExpr)
  deriving Repr, Inhabited

inductive Expr where
  | simple (e : SimpleExpr n m)
  | ite (cond : BoolExpr n m) (tb : SimpleExpr n m) (eb : SimpleExpr n m)
  deriving Repr, Inhabited
end

section
variable {n m m' : Nat} (h : m ≤ m')

def SimpleExpr.upcast : SimpleExpr n m → SimpleExpr n m'
  | .interval lb up => .interval lb up
  | .var v => .var (v.upcast h)
  | .bin_op op l r => .bin_op op l.upcast r.upcast

def BoolExpr.upcast : BoolExpr n m → BoolExpr n m'
  | .cmp_op op left right => .cmp_op op (left.upcast h) (right.upcast h)
  | .bin_op op left right => .bin_op op left.upcast right.upcast

def Expr.upcast : Expr n m → Expr n m'
  | .simple e => .simple <| e.upcast h
  | .ite cond tb eb => .ite (cond.upcast h) (tb.upcast h) (eb.upcast h)
end

/-- A locally bound variable.  This is a local variable that is bound to a value -/
structure BoundVar (n m : Nat) extends Var where
  value : Expr n m
  deriving Repr, Inhabited

def BoundVar.upcast {n m m' : Nat} (h : m ≤ m') (self : BoundVar n m) : BoundVar n m' := {
  self with
  value := self.value.upcast h
}

mutual
variable {n m : Nat} (input_vars : Vector Var n) (bound_vars : Vector (BoundVar n m) m)

def SimpleExpr.toString : SimpleExpr n m → String
  | .interval lb up => s!"[{lb}, {up}]"
  | .var (.old_bound_var k) => s!"(pre {bound_vars[k].name})"
  | .var (.input_var k) => s!"{input_vars[k].name.toString}"
  | .var (.bound_var k) => s!"{bound_vars[k].name.toString}"
  | .var .step => "step"
  | .bin_op op l r => s!"({l.toString} {op} {r.toString})"

def BoolExpr.toString : BoolExpr n m → String
  | .cmp_op op left right
  | .bin_op op left right => s!"({left.toString} {op} {right.toString})"

def Expr.toString : Expr n m → String
  | .simple e => e.toString
  | .ite cond tb eb => s!"(if {cond.toString} then {tb.toString} else {eb.toString})"
end

structure Node where
  name : Name
  n : Nat
  m : Nat
  input_vars : Vector Var n
  bound_vars : Vector (BoundVar n m) m
  output_vars : Array &(VarRef n m)
  guards : Array (BoolExpr n m)
  asserts : Array &(BoolExpr n m)
  deriving Repr, Inhabited

namespace Node
protected def getElem {n m} (nod : Node) (vr : VarRef n m) (p : n = nod.n ∧ m = nod.m) : Var :=
  match vr with
  | .input_var k => nod.input_vars[k]
  | .bound_var k | .old_bound_var k => nod.bound_vars[k].toVar
  | .step => { name := ⟨`step, default⟩ } -- TODO: default is a dummy value`

  instance (n m : Nat) : GetElem Node (VarRef n m) Var (fun nod _ => n = nod.n ∧ m = nod.m) where
    getElem := Node.getElem

section
open Std.Format

variable {n m : Nat} (input_vars : Vector Var n) (bound_vars : Vector (BoundVar n m) m)

def formatBoundVars (bound_vars : Vector (BoundVar n m) m) : Format :=
  Std.Format.indentD <| "where " ++ Std.Format.indentD (joinSep (bound_vars.toList.map formatBvar) Format.line)
where
  formatBvar bvar :=
    (format bvar.name.value) ++ " = " ++ Expr.toString input_vars bound_vars bvar.value

def formatOutputVars (nod : Node) (output_vars : Array &(VarRef n m)) : Format :=
  if output_vars.size = 0 then "" else
  " = " ++ joinSep (output_vars.map (nod[·.value]!.name) |>.toList) ","

def formatGuards (guards : Array (BoolExpr n m)) : Format :=
  if guards.size = 0 then "" else
  Std.Format.indentD <| "guard" ++ Std.Format.indentD (joinSep (guards.map (BoolExpr.toString input_vars bound_vars) |>.toList) Format.line)

def formatAsserts (asserts : Array &(BoolExpr n m)) : Format :=
  if asserts.size = 0 then "" else
  Std.Format.indentD <| "assert" ++ Std.Format.indentD (joinSep (asserts.map (BoolExpr.toString input_vars bound_vars ∘ WithRef.value) |>.toList) Format.line)

instance : ToFormat Node where
  format n :=
    (format ("node " ++ n.name.toString)) ++
    (Indicise.formatInputVars n.input_vars) ++
    (formatOutputVars n n.output_vars)  ++
    (formatGuards n.input_vars n.bound_vars n.guards) ++
    (formatBoundVars n.input_vars n.bound_vars) ++
    (formatAsserts n.input_vars n.bound_vars n.asserts)
end

protected def default (n m : Nat) : Node where
  n := n
  m := m
  name := default
  input_vars := Vector.replicate n default
  bound_vars := Vector.replicate m default
  output_vars := default
  guards := default
  asserts := default

def totalVars (self : Node) : Nat :=
  1 + self.n + self.m + self.m -- step + input vars + bound vars + old bound vars
end Node

abbrev NodeN (n m : Nat)  := { t : Node // t.m = m ∧ t.n = n }

namespace NodeN
variable (n m : Nat)

protected def default : NodeN n m where
  val := Node.default n m
  property := by trivial

instance : Inhabited (NodeN n m) where
  default := NodeN.default n m
end NodeN

abbrev BVar (_n m : Nat) := Fin m

/-- If `e` is a not a bound variable, introduce a new bvar `new_var`, and adds `new_var = e` to the node. -/
def addVarIfNotBvar {n m : Nat} (ref : Syntax) (e : Expr n m) (t : NodeN n m) : NormalizeM ((m' : Nat) ×' m ≤ m' ×' BVar n m' × NodeN n m') := do
  if let .simple (.var (.bound_var x)) := e then
    return ⟨m,Nat.le_refl _,x,t⟩
  else
    let ⟨t, ⟨tm_eq_m, tn_eq_n⟩⟩ := t
    let e' : Expr t.n (t.m+1) := tm_eq_m ▸ tn_eq_n ▸ e.upcast (Nat.le_succ m)
    have this : t.m ≤ t.m + 1 := Nat.le_succ _
    let nod : Node := {
      t with
      m := t.m + 1
      bound_vars := t.bound_vars.map (·.upcast this) |>.push {
        name := { value := .str .anonymous s!"x_{← CounterT.incr}", ref }
        value := e'
      }
      output_vars := t.output_vars.map (·.map (·.upcast this))
      guards := t.guards.map (·.upcast this)
      asserts := t.asserts.map (·.map (·.upcast this))
    }
    let new_var : BVar n (m+1) := Fin.last m
    have : nod.m = m + 1 ∧ nod.n = n := by
      constructor
      · show t.m + 1 = m + 1
        rw [tm_eq_m]
      · rw [tn_eq_n]
    return ⟨m+1, Nat.le_succ _, new_var, nod, this⟩

private structure AuxHelper (α : Nat → Nat → Type) (n m : Nat) where
  m' : Nat
  m_leq_m' : m ≤ m' := by omega
  e : α n m'
  nod : NodeN n m'

instance {α : Nat → Nat → Type} (n m : Nat) [Inhabited (α n m)] : Inhabited (AuxHelper α n m) where
  default := {
    m' := m
    e := default
    nod := default
  }

private abbrev AuxExpr := AuxHelper Expr
private abbrev AuxSimpleExpr := AuxHelper SimpleExpr
private abbrev AuxBoolExpr := AuxHelper BoolExpr

mutual
partial def elabSimpleExprAux {n m : Nat} (nod : NodeN n m) (e : Indicise.Expr n m)
                                 : NormalizeM (AuxSimpleExpr n m) := do
  let { m', m_leq_m', e, nod } ← elabExprAux nod e
  match e with
  | .simple e => return { m', m_leq_m', e, nod }
  | .ite cond e₁ e₂ =>
    let ⟨m', _, x, nod⟩ ← addVarIfNotBvar default (.ite cond e₁ e₂) nod -- TODO: default is a dummy value
    return {
      m' := m'
      e := .var <| .bound_var x
      nod
    }

partial def elabExprAux {n m : Nat} (nod : NodeN n m) : Indicise.Expr n m → NormalizeM (AuxExpr n m)
  | .interval lb up =>
    return ⟨m, by simp, .simple (.interval lb up), nod⟩
  | .var ⟨.input_var v, _⟩ =>
    return ⟨m, by simp, .simple <| .var <| .input_var v, nod⟩
  | .var ⟨.bound_var v, _⟩ =>
    return ⟨m, by simp, .simple <| .var <| .bound_var v, nod⟩
  | .mon_op .neg ⟨e, _⟩ => do
    let ⟨m', _, e, nod⟩ ← elabSimpleExprAux nod e
    return {
      m'
      e := .simple <| .bin_op .sub (.interval 0 0) e
      nod := nod
    }
  | .mon_op .pre ⟨e, _⟩ => do
    let ⟨m', _, e, nod⟩ ← elabExprAux nod e
    let ⟨m', _, x, nod⟩ ← addVarIfNotBvar default e nod -- TODO: default is a dummy value
    return {
      m' := m'
      e := .simple <| .var (.old_bound_var x)
      nod := nod
    }
  | .bin_op .add ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, m₁_leq_m₂, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast m_leq_m₁)
    return {
      m' := m₂
      e := .simple <| .bin_op .add (e₁.upcast m₁_leq_m₂) e₂
      nod := nod
    }
  | .bin_op .sub ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, m₁_leq_m₂, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast m_leq_m₁)
    return {
      m' := m₂
      e := .simple <| .bin_op .sub (e₁.upcast m₁_leq_m₂) e₂
      nod := nod }
  | .bin_op .mul ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, m₁_leq_m₂, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast m_leq_m₁)
    return {
      m' := m₂
      e := .simple <| .bin_op .mul (e₁.upcast m₁_leq_m₂) e₂
      nod := nod
    }
  | .bin_op .fby ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, _, e₂, nod⟩ ← elabExprAux nod (e₂.upcast m_leq_m₁)
    let ⟨m', _, x, nod⟩ ← addVarIfNotBvar default e₂ nod -- TODO: default is a dummy value
    -- the condition `n = 0`
    let cond := .cmp_op .eq (.var .step) (.interval 0 0)
    return {
      m' := m'
      e := .ite cond (e₁.upcast <| by omega) (.var <| .old_bound_var x)
      nod := nod
    }
  | .bin_op .arr ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, m_leq_m₁, e₁, nod⟩ ← elabSimpleExprAux nod e₁
    let ⟨m₂, _, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast m_leq_m₁)
    let cond := .cmp_op .eq (.var .step) (.interval 0 0)
    return {
      m' := m₂
      e := .ite cond (e₁.upcast <| by omega) (e₂.upcast <| by omega)
      nod := nod
    }
  | .ite ⟨cond, _⟩ ⟨e₁, _⟩ ⟨e₂, _⟩ => do
    let ⟨_, _, cond, nod⟩ ← elabBoolexprAux nod cond
    let ⟨_, _, e₁, nod⟩ ← elabSimpleExprAux nod (e₁.upcast <| by omega)
    let ⟨m₃, _, e₂, nod⟩ ← elabSimpleExprAux nod (e₂.upcast <| by omega)
    return {
      m' := m₃
      e := .ite (cond.upcast <| by omega) (e₁.upcast <| by omega) e₂
      nod := nod
    }

partial def elabBoolexprAux {n m : Nat} (nod : NodeN n m)
                              : Indicise.BoolExpr n m → NormalizeM (AuxBoolExpr n m)
  | .bin_op op ⟨l, _⟩ ⟨r, _⟩ => do
    let ⟨_, m_leq_m₁, l, nod⟩ ← elabBoolexprAux nod l
    let ⟨m₂, m₁_leq_m₂, r, nod⟩ ← elabBoolexprAux nod (r.upcast m_leq_m₁)
    return {
      m' := m₂
      e := .bin_op op (l.upcast m₁_leq_m₂) r
      nod := nod
    }
  | .cmp_op op ⟨l, _⟩ ⟨r, _⟩ => do
    let ⟨_, m_leq_m₁, l, nod⟩ ← elabSimpleExprAux nod l
    let ⟨m₂, m₁_leq_m₂, r, nod⟩ ← elabSimpleExprAux nod (r.upcast m_leq_m₁)
    return {
      m' := m₂
      e := .cmp_op op (l.upcast m₁_leq_m₂) r
      nod
    }
end

def elabNode (nod : &Indicise.Node) : CoreM &Node :=
  WithRef.withRef nod.ref do
  withTraceNode `Lustrean.Elab.Normalize (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{nod}\n⇒\n{toMessageData e.toOption}") do
  CounterT.run do
  let ⟨nod, _⟩ := nod
  let mut new_nod : { t : Node // nod.n = t.n ∧ nod.m ≤ t.m } := ⟨{
    name := nod.name
    n := nod.n
    m := nod.m
    input_vars := nod.input_vars
    output_vars := nod.output_vars.map (·.map elabVr)
    -- Random garbage, will be filled in later.  This is necessary, because our expressions can
    -- refer to these variables, so they must appear exactly where they originally appear, so
    -- as not to break the references.  Additional bindings must come *after* these.
    bound_vars := nod.bound_vars.map fun bv => { name := bv.name, value := default }
    -- For guards and asserts, on the other hand, we can add them later, which is simpler.
    guards := #[]
    asserts := #[]
  }, rfl, by simp⟩
  for h : i in [0:nod.m] do
    let e : Indicise.Expr new_nod.val.n new_nod.val.m :=
      new_nod.property.1 ▸ nod.bound_vars[i].value.value.upcast new_nod.property.2
    let { m', e, nod := ⟨hnod, hnod_m_m', hnod_n_nod_n⟩, m_leq_m', .. } ←
      elabExprAux ⟨new_nod, rfl, rfl⟩ e
    have : i < hnod.m := by
      have : i < nod.m := by
        apply Membership.get_elem_helper
        · assumption
        · rfl
      omega
    new_nod := .mk {
      hnod with
      bound_vars := hnod.bound_vars |>.set i {
        name := nod.bound_vars[i].name
        value := hnod_m_m' ▸ hnod_n_nod_n ▸ e
      }
    } <| by
      simp
      constructor
      · rewrite [hnod_n_nod_n]
        exact new_nod.property.1
      · calc
        nod.m ≤ new_nod.val.m := new_nod.property.2
        new_nod.val.m ≤ m' := m_leq_m'
        m' = hnod.m := by symm; assumption
  for g in nod.guards do
    let g : Indicise.BoolExpr new_nod.val.n new_nod.val.m :=
      new_nod.property.1 ▸ g.value.upcast new_nod.property.2
    let { m', e, nod := ⟨hnod, hnod_m_m', hnod_n_nod_n⟩, m_leq_m', .. } ←
      elabBoolexprAux ⟨new_nod, rfl, rfl⟩ g
    let b : BoolExpr hnod.n hnod.m := hnod_m_m' ▸ hnod_n_nod_n ▸ e
    new_nod := .mk {
      hnod with
      guards := hnod.guards.push b
    } <| by
      simp
      constructor
      · rewrite [hnod_n_nod_n]
        exact new_nod.property.1
      · calc
        nod.m ≤ new_nod.val.m := new_nod.property.2
        new_nod.val.m ≤ m' := m_leq_m'
        m' = hnod.m := by symm; assumption
  for a in nod.asserts do
    let ref := a.ref
    let a : Indicise.BoolExpr new_nod.val.n new_nod.val.m :=
      new_nod.property.1 ▸ a.value.upcast new_nod.property.2
    let { m', e, nod := ⟨hnod, hnod_m_m', hnod_n_nod_n⟩, m_leq_m', .. } ←
      elabBoolexprAux ⟨new_nod, rfl, rfl⟩ a
    let b : BoolExpr hnod.n hnod.m := hnod_m_m' ▸ hnod_n_nod_n ▸ e
    new_nod := .mk {
      hnod with
      asserts := hnod.asserts.push { value := b, ref }
    } <| by
      simp
      constructor
      · rewrite [hnod_n_nod_n]
        exact new_nod.property.1
      · calc
        nod.m ≤ new_nod.val.m := new_nod.property.2
        new_nod.val.m ≤ m' := m_leq_m'
        m' = hnod.m := by symm; assumption
  return new_nod

def elabLustre (nodes : Array (&Indicise.Node)) : CoreM (Array &Node) :=
  nodes.mapM elabNode

end Normalize
end Lustrean.Elaboration

initialize
  registerTraceClass `Lustrean.Elab.Normalize (inherited := true)
