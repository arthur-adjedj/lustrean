namespace Lustrean

inductive BinOp : Type where
| add
| sub
| mul
| div
| and
| or
deriving Repr, Inhabited

namespace BinOp
protected def toString : BinOp → String
  | add => "+"
  | sub => "-"
  | mul => "*"
  | div => "/"
  | and => "∧"
  | or => "∨"

instance : ToString BinOp where
  toString := BinOp.toString
end BinOp

-- TODO: Consider normalizing to `Ord`
inductive CompareOp : Type where
| eq : CompareOp
| neq : CompareOp
| le : CompareOp
| lt : CompareOp
| ge : CompareOp
| gt : CompareOp
deriving Repr, Inhabited

namespace CompareOp
def not : CompareOp → CompareOp
| eq => neq
| neq => eq
| le => gt
| lt => ge
| ge => lt
| gt => le

protected def toString : CompareOp → String
  | eq => "="
  | neq => "≠"
  | le => "≤"
  | lt => "<"
  | ge => "≥"
  | gt => ">"

instance : ToString CompareOp where
  toString := CompareOp.toString
end CompareOp

-- n : number of variable
inductive IExpr (n : Nat): Type where
| nil : IExpr n
| var : (i : Fin n) → IExpr n
| rand : Option Int → Option Int → IExpr n
| neg : IExpr n → IExpr n
| binop : IExpr n → (op : BinOp) → IExpr n → IExpr n
| cmpop : IExpr n → CompareOp → IExpr n → IExpr n
deriving Repr, Inhabited

-- no negated expression. it must be eliminated by simplification
-- inductive BExpr (n : Nat) : Type where
-- | random : BExpr n
-- | const : Bool → BExpr n
-- | compare : IExpr n → CompareOp → IExpr n → BExpr n
-- | and : BExpr n → BExpr n → BExpr n
-- | or : BExpr n → BExpr n → BExpr n
-- deriving Repr, Inhabited

namespace IExpr
variable {n : Nat}

def const (x : Int) : IExpr n:=
  .rand x x

protected def toString : IExpr n → String
  | .nil => "nil"
  | .var ⟨0,_⟩ => s!"step"
  | .var k =>
    s!"x{k.val.toSubscriptString}"
  | .rand left right =>
    let l := match left with
      | some n => toString n
      | none => "-∞"
    let r := match right with
      | some n => toString n
      | none => "∞"
    if l == r then s!"{l}" else s!"[{l}, {r}]"
  | .neg e => s!"(- {e.toString})"
  | .binop left op right
  | .cmpop left op right => s!"({left.toString} {op} {right.toString})"

instance : ToString (IExpr n) where
  toString := IExpr.toString

end IExpr

def CompareOp.toProp{α: Type}[LT α][LE α](ord: CompareOp)(x y: α): Prop :=
  match ord with
  | eq  => x = y
  | neq => x ≠ y
  | le  => x ≤ y
  | lt  => x < y
  | ge  => x ≥ y
  | gt  => x > y

inductive Instruction (n : Nat) : Type where
| skip : Instruction n
| assign : (i : Fin n) → IExpr n→ Instruction n
| guard : IExpr n → Instruction n
| assert : IExpr n → Instruction n
deriving Repr, Inhabited

namespace Instruction
variable {n : Nat}

protected def toString : Instruction n → String
  | .skip => "skip"
  | .assign ⟨0,_⟩ e => s!"step := {e}"
  | .assign k e => s!"x{k.val.toSubscriptString} := {e}"
  | .guard b => s!"guard {b}"
  | .assert b => s!"assert {b}"

instance : ToString (Instruction n) where
  toString := Instruction.toString
end Instruction

structure OutNode (nb_var : Nat)where
  out_node: Nat
  out_inst : Instruction nb_var
  ref? : Option (Lean.Syntax) := none
deriving Repr

structure PreNode (nb_var : Nat) : Type where
  id : Nat
  out_nodes : List (OutNode nb_var)
  deriving Repr, Inhabited

def PreNode.toDot{nb_var: Nat} (curr: PreNode nb_var): List Std.Format :=
  curr.out_nodes
    |>.map (fun neigh =>
      Std.format curr.id ++ " -> " ++ Std.format neigh.out_node ++ " " ++ "[label=\"" ++ Std.format neigh.out_inst ++ "\"]"
    )

section
open Std.Format
open Std.ToFormat

instance {n} : Std.ToFormat (OutNode n) where
  format node :=  format node.out_inst ++ " ⇒ f_" ++ format node.out_node

instance {n} : Std.ToFormat (PreNode n) where
  format p :=
    "node f_" ++ format p.id ++ " where" ++ (indentD <| joinSep p.out_nodes line)
end
end Lustrean
