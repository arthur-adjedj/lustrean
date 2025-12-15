import Lustrean.Elaboration.Reify

open Std.Iterators

universe u v w

def HList : List (Type u) → Type u
  | [] => PUnit
  | α::tl => α × HList tl

def HList.get {α} {Ts : List (Type u)} (idx : Nat) (h : Ts[idx]? = some α) (l : HList Ts) : α :=
  match idx,Ts,h,l with
  | 0, _::_, .refl _,⟨a,_⟩ => a
  | n+1,_::_,h,⟨_,tl⟩ => HList.get n h tl

def HList.sigma_fst (Ts : List (Type u)) {C : Type v → Type u → Type w}
  (cs : HList (Ts.map fun α => (σ : Type v) × C σ α)) : List (Type v) :=
  match Ts, cs with
    | [],⟨⟩ => []
    | _::tl, (⟨σ,_⟩,cs') => σ::HList.sigma_fst tl cs'

structure CoStream (σ α : Type _) where
  init : σ
  step : σ → α × σ

@[inline]
def CoStream.unit : CoStream PUnit PUnit where
  init := ⟨⟩
  step := fun _ => (⟨⟩,⟨⟩)

@[inline]
def CoStream.const {α} (a : α) : CoStream PUnit α where
  init := ⟨⟩
  step := fun _ => (a,⟨⟩)

@[inline]
def CoStream.take {σ α} (c : CoStream σ α): α × CoStream σ α :=
  let (v,s) := c.step c.init
  (v, {c with init := s})

@[inline]
def CoStream.next {σ α} (c : CoStream σ α): CoStream σ α :=
  { c with init := c.step c.init |>.2}

def CoStream.taken {σ α} (c : CoStream σ α) : (n : Nat) → (Vector α n × CoStream σ α)
  | 0 => (Vector.mk #[] rfl,c)
  | n+1 =>
    let (l,c) := c.taken n
    let (v,c) := c.take
    (l.push v,c)

@[inline]
def CoStream.iter {α} (init : α) (f : α → α) : CoStream α α where
  init := init
  step x :=
    (x,f x)

@[inline]
def CoStream.extend {σ₁ σ₂ α β} (f : CoStream σ₁ (α → β)) (c : CoStream σ₂ α) : CoStream (σ₁ × σ₂) β where
  init := (f.init,c.init)
  step s :=
    let (s₁,s₂) := s
    let (f,s₁) := f.step s₁
    let (x,s₂) := c.step s₂
    (f x,s₁,s₂)

@[inline]
def CoStream.map {σ α β} (f : α → β) (c : CoStream σ α) : CoStream σ β where
  init := c.init
  step a :=
    let (x,s) := c.step a
    (f x, s)

@[inline]
def CoStream.map₂ {σ₁ σ₂ α β γ} (f : α → β → γ) (c₁ : CoStream σ₁ α) (c₂ : CoStream σ₂ β) : CoStream (σ₁ × σ₂) γ where
  init := (c₁.init,c₂.init)
  step s :=
    let (s₁,s₂) := s
    let (x₁,s₁') := c₁.step s₁
    let (x₂,s₂') := c₂.step s₂
    (f x₁ x₂, s₁',s₂')

@[inline]
def CoStream.mapₙ (Ts : List (Type u))
  (cs : HList (Ts.map fun α => (σ : Type v) × CoStream σ α)) :
  CoStream (HList (HList.sigma_fst Ts cs)) (HList Ts) :=
  match Ts,cs with
  | [],⟨⟩ => CoStream.unit
  | _::Ts,(⟨_,c₁⟩,cs) =>
    let c₂ := CoStream.mapₙ Ts cs
    { init := ⟨c₁.init, c₂.init⟩
      step := fun ⟨s₁,s₂⟩ =>
        let ⟨v₁,s₁⟩ := c₁.step s₁
        let ⟨v₂,s₂⟩ := c₂.step s₂
        ⟨⟨v₁,v₂⟩,s₁,s₂⟩}

@[inline]
def CoStream.pre {σ α} (init : α) (c : CoStream σ α) : CoStream (α × σ) α where
  init := (init, c.init)
  step := fun ⟨s_pre,s⟩ =>
    let ⟨v,s'⟩ := c.step s
    ⟨s_pre,v,s'⟩

@[inline]
def CoStream.projn {σ α} {Ts : List (Type u)} (c : CoStream σ (HList Ts)) (idx : Nat) (h : Ts[idx]? = some α) : CoStream σ α where
  init := c.init
  step σ :=
    let (l,σ) := c.step σ
    (l.get idx h, σ)

def CoStream.apply {α β γ σ₁ σ₂} (f : CoStream σ₁ (α → Option β → γ × (Option β))) (c : CoStream σ₂ α)
  : CoStream (Option β × σ₁ × σ₂) γ where
  init := (none, f.init, c.init)
  step s :=
    let ⟨b,s₁,s₂⟩ := s
    let ⟨a,s₂⟩ := c.step s₂
    let ⟨f,s₁⟩ := f.step s₁
    let ⟨x,b⟩ := f a b
    ⟨x,b,s₁,s₂⟩

/-TODO check this is correct ? the signature in the original paper makes little sense
  TODO prove that apply (lambda (apply f)) = apply f-/
def CoStream.lambda {σ₁ σ₂ α β} (f : CoStream (Option σ₁) α → CoStream σ₂ β) : CoStream (Option σ₁) (α → σ₂ → β × σ₂) where
  init := none
  step s₁ := (fun a s₂ =>
    have c := f { init := s₁, step := fun _ => (a, s₁) };
    c.step s₂,
    s₁)

abbrev ValType := Option Int

/-!
  node f(i) = o where
    x = pre i + 1
    o = x+i -/
namespace test1

def x {σ} (i : CoStream σ ValType) : CoStream ((ValType × σ) × PUnit) ValType :=
  let pre_i := i.pre none
  let one := CoStream.const (some 1)
  let pre_i_add_1 := pre_i.map₂ (c₂ := one) fun i o => do
    let i ← i
    let o ← o
    return i + o
  pre_i_add_1

def o {σ} (x : CoStream ((ValType × σ) × PUnit) ValType) : CoStream (((ValType × σ) × PUnit) × PUnit) ValType :=
  let one := CoStream.const (some 1)
  let x_add_1 := x.map₂ (c₂ := one) fun i o => do
    let i ← i
    let o ← o
    return i + o
  x_add_1

def f {σ} (i : CoStream σ ValType) :=
  let x := x i
  let o := o x
  o
end test1


/-!
  node f(i) = o where
    x = pre i + 1
    o = x+i -/
namespace test2

def x {σ} (i : CoStream σ ValType) : CoStream ((ValType × σ) × PUnit) ValType :=
  let pre_i := i.pre none
  let one := CoStream.const (some 1)
  let pre_i_add_1 := pre_i.map₂ (c₂ := one) fun i o => do
    let i ← i
    let o ← o
    return i + o
  pre_i_add_1

def o {σ} (x : CoStream ((ValType × σ) × PUnit) ValType) : CoStream (((ValType × σ) × PUnit) × PUnit) ValType :=
  let one := CoStream.const (some 1)
  let x_add_1 := x.map₂ (c₂ := one) fun i o => do
    let i ← i
    let o ← o
    return i + o
  x_add_1

def f {σ} (i : CoStream σ ValType) :=
  let x := x i
  let o := o x
  o

end test2
