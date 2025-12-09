import Lean.Log
open Lean

def Lean.logErrorAt? {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  (ref? : Option Syntax) (msgData : MessageData) : m Unit := do
    if let some ref := ref? then
      logErrorAt ref msgData
    else
      logError msgData

def Array.toStringNoBrackets (xs : Array String) : String :=
  (Std.Format.joinSep xs.toList ("," ++ Std.Format.line)) |>.pretty

def Fin.mk' {n : Nat} (val : Nat) (isLt : val < n := by grind) : Fin n := Fin.mk val isLt
def Membership.get_elem_helper' {i n m s: Nat} {h} (h : i ∈ (Std.Range.mk n m s h : Std.Range)) : i < m :=
  Membership.get_elem_helper h rfl

grind_pattern Membership.get_elem_helper' => i ∈ [n:m:s]
