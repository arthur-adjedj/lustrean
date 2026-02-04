import Lean.Log
import Mathlib.Data.Quot
import Std.Data.ExtHashMap.Basic

open Lean

def Lean.logErrorAt? {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  (ref? : Option Syntax) (msgData : MessageData) : m Unit := do
    if let some ref := ref? then
      logErrorAt ref msgData
    else
      logError msgData

def Array.toStringNoBrackets (xs : Array String) : String :=
  (Std.Format.joinSep xs.toList ("," ++ Std.Format.line)) |>.pretty

def Fin.mk' {n : Nat} (val : Nat) (isLt : val < n := by get_elem_tactic) : Fin n := Fin.mk val isLt

def Std.Format.joinSepArray.{u} {α : Type u} [ToFormat α] (xs : Array α) (sep : Format) : Format :=
  if _ : xs.size = 0 then
    .nil
  else  if _ : xs.size = 1 then
    format xs[0]
  else
    xs[1 :].foldl (· ++ sep ++ format ·) (format xs[0])

namespace Std

unsafe def ExtDHashMap.unquot {α β} [BEq α] [Hashable α] (h : ExtDHashMap α β) : DHashMap α β :=
  Quot.unquot h.inner

/-- Transforms the hash map into a list of mappings in some order.
    /!\ This function uses the unsafe `Quot.unquot`, and thus cannot be unfolded/reasoned upon-/
def ExtDHashMap.toList {α β} [BEq α] [Hashable α] (h : ExtDHashMap α β) : List ((a : α) × β a) :=
  unsafe h.unquot.toList

instance {α β} [BEq α] [Hashable α] [Repr α] [∀ a, Repr (β a)] : Repr (ExtDHashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.ExtDHashMap.ofList " ++ reprArg m.toList) prec


unsafe def ExtHashMap.unquot {α β} [BEq α] [Hashable α] (h : ExtHashMap α β) : HashMap α β :=
  .mk (h.inner.unquot)

/-- Transforms the hash map into a list of mappings in some order.
    /!\ This function uses the unsafe `Quot.unquot`, and thus cannot be unfolded/reasoned upon-/
def ExtHashMap.toList {α β} [BEq α] [Hashable α] (h : ExtHashMap α β) : List (α × β) :=
  unsafe h.unquot.toList

instance {α β} [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (ExtHashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.ExtHashMap.ofList " ++ reprArg m.toList) prec

end Std