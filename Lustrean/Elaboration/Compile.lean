import Lustrean.Elaboration.Normalize
import Lustrean.Imp
import Misc.Lean

open Lean
namespace Lustrean.Elaboration.Compile
open Normalize
section
variable {n m : Nat}

def _root_.Lustrean.Elaboration.Normalize.SimpleExpr.to_cfg_expr : SimpleExpr n m → IExpr (1 + n + m + m)
  | .interval lb ub =>
    let lb := match lb with
      | .minf => none
      | .nat n => some n
    let ub := match ub with
      | .pinf => none
      | .nat n => some n
    .rand lb ub
  | .bin_op op l r =>
    let op := match op with
      | .add => .iadd
      | .mul => .imul
      | .sub => .isub
      | .or => .ior l r
      | .and => .iand l r
    .binop l.to_cfg_expr op r.to_cfg_expr
  | .cmp_op op l r =>
    let op := match op with
      | .eq => .eq
      | .lt => .lt
      | .leq => .le
    .compare l.to_cfg_expr op r.to_cfg_expr
  | .var .step => .var <| .mk 0 <| by omega
  | .var (.input_var k) => .var <| .mk (1+k) <| by omega
  | .var (.bound_var k) => .var <| .mk (1+n+k) <| by omega
  | .var (.old_bound_var k) => .var <| .mk (1+n+m+k) <| by omega

def _root_.Lustrean.Elaboration.Normalize.BoolExpr.to_cfg_expr : Expr n m → BExpr (1 + n + m + m)
  | .cmp_op op l r =>
    let op := match op with
      | .eq => .eq
      | .lt => .lt
      | .leq => .le
    .compare l.to_cfg_expr op r.to_cfg_expr
  | .bin_op op l r =>
    let l := l.to_cfg_expr
    let r := r.to_cfg_expr
    match op with
    | .or => .or l r
    | .and => .and l r
end

def step {nod : Normalize.Node}: Fin nod.totalVars := .mk 0 (by grind [Normalize.Node.totalVars])
def input_var {nod : Normalize.Node} (k : Fin nod.n) : Fin nod.totalVars := .mk (1+k) (by grind [Normalize.Node.totalVars])
def bound_var {nod : Normalize.Node} (k : Fin nod.m) : Fin nod.totalVars := .mk (1+nod.n+k) (by grind [Normalize.Node.totalVars])
def old_bound_var {nod : Normalize.Node} (k : Fin nod.m) : Fin nod.totalVars := .mk (1+nod.n+nod.m+k) (by grind [Normalize.Node.totalVars])

structure Result (nod : Normalize.Node) where
  arr : Array (PreNode nod.totalVars)

abbrev ResultM (nod : Normalize.Node) := StateT (Result nod) CoreM

def Result.init {nod : Normalize.Node} : Result nod where
  arr := #[
    { id := 0, out_nodes := [{ out_node := 2, out_inst := .assign step (IExpr.const 0)}] },
    { id := 1, out_nodes := [] }
  ]

def addNewPreNode {nod} (out_nodes : List (OutNode nod.totalVars)) : ResultM nod Unit := do
  let r ← get
  set {r with arr := r.arr.push {id := r.arr.size, out_nodes}}

def addNewPreNodeOutNext {nod} (out_inst : Lustrean.Instruction nod.totalVars) (ref? : Option Syntax := none) : ResultM nod Unit := do
  let r ← get
  set {r with arr := r.arr.push {id := r.arr.size, out_nodes := [{out_node := r.arr.size+1, out_inst, ref?}]}}

def getNextId {nod} : ResultM nod Nat := do
  let r ← get
  return r.arr.size

def addExitNode {nod} : ResultM nod Unit := do
  let r ← get
  set {r with arr[1] := {id := 1, out_nodes := [{ out_node := r.arr.size-1, out_inst := .skip}]}}

/-- How many iterations of the main loop to unroll. -/
def unrollLoop : Nat := 1

def elabResult (nod : Normalize.Node) : ResultM nod Unit := do
  for h : i in [0:nod.m] do
    let k := Fin.mk' i
    addNewPreNodeOutNext (.assign (bound_var k) .nil)
  let unrolled_loop := do
    for h : i in [0:nod.m] do
      let k := Fin.mk' i
      addNewPreNodeOutNext (.assign (old_bound_var k) (.var <| bound_var k))
    for h : i in [0:nod.n] do
      let k := Fin.mk' i
      addNewPreNodeOutNext (.assign (input_var k) (.rand none none))
    for g in nod.guards do
      addNewPreNodeOutNext (.guard g.to_cfg_expr)
    let there_id ← getNextId
    for h : i in [0:nod.m] do
      let k := Fin.mk' i
      match nod.bound_vars[i].value with
      | .simple e =>
        addNewPreNodeOutNext (.assign (bound_var k) e.to_cfg_expr)
      | .ite cond e₁ e₂ =>
        let next_id ← getNextId
        let guard_nodes := [
          { out_node := next_id + 1,  out_inst := .guard cond.to_cfg_expr},
          { out_node := next_id + 2,  out_inst := .guard cond.to_cfg_expr.not}]
        let ite_true_node  := { out_node := next_id+3,  out_inst := .assign (bound_var k) e₁.to_cfg_expr}
        let ite_false_node := { out_node := next_id+3,  out_inst := .assign (bound_var k) e₂.to_cfg_expr}
        addNewPreNode guard_nodes
        addNewPreNode [ite_true_node]
        addNewPreNode [ite_false_node]
    let next_id ← getNextId
    let out_nodes := [
        { out_node := there_id,  out_inst := .skip},                   -- loop again current iteration
        { out_node := 1,  out_inst := .skip},                          -- exit program
        { out_node := next_id + 1, out_inst := .assign step (.binop (.var step) .iadd (IExpr.const 1))} -- next iteration
    ]
    addNewPreNode out_nodes
  for _ in [0:unrollLoop] do
    unrolled_loop
  let here_id ← getNextId
  for h : i in [0:nod.m] do
    let k := Fin.mk' i
    addNewPreNodeOutNext (.assign (old_bound_var k) (.var <| bound_var k))
  for h : i in [0:nod.n] do
    let k := Fin.mk' i
    addNewPreNodeOutNext (.assign (input_var k) (.rand none none))
  for g in nod.guards do
    addNewPreNodeOutNext (.guard g.to_cfg_expr)
  -- Why were we reinitialising bvars each loop cycle ??
  -- for h : i in [0:nod.m] do
    -- let k := Fin.mk' i
    -- addNewPreNodeOutNext (.assign (bound_var k) .nil)
  let there_id ← getNextId
  for h : i in [0:nod.m] do
    let k := Fin.mk' i
    match nod.bound_vars[i].value with
    | .simple e =>
      addNewPreNodeOutNext (.assign (bound_var k) e.to_cfg_expr)
    | .ite cond e₁ e₂ =>
      let next_id ← getNextId
      let guard_nodes := [
        { out_node := next_id + 1,  out_inst := .guard cond.to_cfg_expr},
        { out_node := next_id + 2,  out_inst := .guard cond.to_cfg_expr.not}]
      let ite_true_node  := { out_node := next_id+3,  out_inst := .assign (bound_var k) e₁.to_cfg_expr}
      let ite_false_node := { out_node := next_id+3,  out_inst := .assign (bound_var k) e₂.to_cfg_expr}
      addNewPreNode guard_nodes
      addNewPreNode [ite_true_node]
      addNewPreNode [ite_false_node]
  let next_id ← getNextId
  let out_nodes := [
      { out_node := here_id, out_inst := .assign step (.binop (.var step) .iadd (IExpr.const 1))}, -- go to next iteration
      { out_node := there_id, out_inst := .skip},                   -- loop again current iteration
      { out_node := next_id + 1,  out_inst := .skip}             -- exit program
    ]
  addNewPreNode out_nodes
  for a in nod.asserts do
    addNewPreNodeOutNext (.assert a.value.to_cfg_expr) a.ref
  addNewPreNode []
  addExitNode

structure Node where
  totalVars : Nat
  cfg : Array (PreNode totalVars)
  outputVars : Array &(Fin totalVars)
deriving Repr, Inhabited

def Node.toDot(nod: Node): Std.Format :=
  let outVars := nod.outputVars.toList
    |>.map (λ i ↦ Std.format i ++ " [peripheries=2]")
  let edges := nod.cfg.toList
    |>.flatMap PreNode.toDot
  let content := (outVars ++ edges)
    |> Std.Format.line.joinSep
    |> (.line ++ ·)
    |> .nest 2
    |> Std.Format.group
    |>.append .line
  "digraph Cfg {" ++ content ++ "}"

instance : ToFormat Node where
  format nod := Std.Format.joinSepArray nod.cfg .line

def formatOptionNode {ε} (o : Except ε Node) : Format :=
  if let .ok nod := o then format nod else .nil

def elabIntoCfg (nod : &Normalize.Node) : CoreM &Node :=
  WithRef.withRef nod.ref do
  withTraceNode `Lustrean.Elab.Compile (msg := fun e => return m!"{exceptEmoji e} elabExpr\n{nod}\n⇒\n{formatOptionNode e}") do
  let ((),result) ← elabResult nod |>.run Result.init
  let output_vars := nod.value.output_vars.map (·.map fun
    | .step => step
    | .input_var k => input_var k
    | .bound_var k => bound_var k
    | .old_bound_var k => old_bound_var k)
  return ⟨nod.value.totalVars, result.arr, output_vars⟩

def elabLustre (a : Array &Normalize.Node) : CoreM (Array &Node) :=
  a.mapM elabIntoCfg

end Lustrean.Elaboration.Compile

initialize
  registerTraceClass `Lustrean.Elab.Compile (inherited := true)
