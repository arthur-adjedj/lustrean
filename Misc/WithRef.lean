import Lean

open Lean

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
