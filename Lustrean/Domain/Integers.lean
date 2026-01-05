import Lustrean.Domain.NonRelational

namespace Lustrean
inductive Integers where
| bot : Integers
| top : Integers
| int : Int → Integers
deriving DecidableEq, BEq

namespace Integers
def join (x y : Integers) : Integers := match x, y with
  | n, .bot | .bot, n => n
  | .int n, .int m => if n = m then .int n else .top
  | _, _ => .top

def meet (x y : Integers) : Integers := match x, y with
  | .top, n | n, .top => n
  | .int n, .int m => if n = m then .int n else .bot
  | _, _ => .bot

instance : BoundedLattice Integers where
  bot := .bot
  top := .top
  join := join
  meet := meet
  join_commutative := by
    intro x y
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [join, Max.max]
    grind
  join_associative := by
    intro x y z
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    rcases z with _ | _ | ⟨z⟩ <;>
    dsimp [join, Max.max] <;>
    grind
  join_absorption := by
    intro x y
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [join, meet, Max.max, Min.min] <;>
    grind
  join_bot := by
    intro x
    cases x <;> dsimp [join, Max.max, Min.min]
  join_top := by
    intro x
    cases x <;> dsimp [join, Max.max, Min.min]
  meet_commutative := by
    intro x y
    cases x <;> cases y <;> dsimp [meet, Max.max, Min.min]
    split <;> split
    · next h₁ => rw [h₁]
    · next h₁ h₂ => cases h₂ h₁.symm
    · next h₁ h₂ => cases h₁ h₂.symm
    · constructor
  meet_associative := by
    intro x y z
    cases x <;> cases y <;> cases z <;> dsimp [meet, Max.max, Min.min]
    <;> try (next x y =>
      by_cases h : (x = y) <;> simp [h])
    next x y z =>
      by_cases h1 : (x = y) <;>
      by_cases h2 : (y = z) <;>
      simp [h1] <;>
      simp [h2]
      rw [←h2]
      simp [h1]
  meet_absorption := by
    intro x y
    cases x <;> cases y <;> simp [meet, join, Max.max, Min.min]
    next x y =>
      by_cases h : (x = y) <;>
      simp [h]
  meet_bot := by
    intro x
    cases x <;> dsimp [meet, Max.max, Min.min]
  meet_top := by
    intro x
    cases x <;> dsimp [meet, Max.max, Min.min]

def mapInt (x y : Integers) (f : Int → Int →  Integers) : Integers :=
  match x, y with
  | .bot, _ | _, .bot => .bot
  | .top, _ | _, .top => .top
  | .int n, .int m => f n m

instance : Add Integers where
  add x y := mapInt x y
    fun n m => .int (n + m)

instance : Neg Integers where
  neg x := match x with
  | .bot => .bot
  | .top => .top
  | .int n => .int (-n)

instance : Sub Integers where
  sub x y := mapInt x y
    fun n m => .int (n - m)

instance : Mul Integers where
  mul x y := match x, y with
  | .bot, _ | _, .bot => .bot
  | .int 0, _ | _, .int 0 => .int 0
  | .top, _ | _, .top => .top
  | .int n, .int m => .int (n * m)

instance : Div Integers where
  div x y := match x, y with
  | .bot, _ | _, .bot | _, .int 0 => .bot
  | .int 0, _ => .int 0
  | .int n, .int m => .int (n / m)
  | _, _ => .top

instance : ToString Integers where
  toString x := match x with
  | .bot => "⊥"
  | .top => "⊤"
  | .int n => toString n

instance : DecidableEq Integers := by
  intros x y
  cases x <;> cases y <;> simp <;>
  exact inferInstance

instance : Widen Integers where
  widen x y _ := join x y

instance : WidenLawful Integers where
  covering_left := by
    intros x y n
    dsimp [BoundedLattice.IsSubset, Widen.widen]
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [join, Min.min, Meet.meet, meet, reduceIte]
    by_cases h : (x = y) <;> simp [h]
  covering_right := by
    intros x y n
    dsimp [BoundedLattice.IsSubset, Widen.widen]
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [join, Min.min, Meet.meet, meet, reduceIte]
    by_cases h : (x = y) <;> simp [h]

instance : Narrow Integers where
  narrow x y _ := meet x y

instance : NarrowLawful Integers where
  bounding_low := by
    intros x y n
    dsimp [BoundedLattice.IsSubset, Narrow.narrow]
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [Min.min, Meet.meet, meet, reduceIte]
    grind
  bounding_high := by
    intros x y n
    dsimp [BoundedLattice.IsSubset, Narrow.narrow]
    rcases x with _ | _ | ⟨x⟩ <;>
    rcases y with _ | _ | ⟨y⟩ <;>
    simp only [Min.min, Meet.meet, meet, reduceIte]
    grind

def compareInt (op : CompareOp) (a b : Int) : Integers × Integers :=
  let cond := match op with
  | .eq => decide (a = b)
  | .neq => decide (a ≠ b)
  | .le => decide (a ≤ b)
  | .lt => decide (a < b)
  | .ge => decide (a ≥ b)
  | .gt => decide (a > b)
  if cond then
    (.int a, .int b)
  else
    (bot, bot)

def compare (op : CompareOp) (x y : Integers) : Integers × Integers :=
  match op, x, y with
  | _, .bot, _
  | _, _, .bot => (bot, bot)
  | _, .int a, .int b => compareInt op a b
  | .eq, .top, z
  | .eq, z, .top => (z, z)
  | _, _, _ => (x, y)

instance IntegersValueDomain : ValueDomain Integers where
  nil := .bot
  rand a b := match a, b with
    | .some a, .some b => if a = b then .int a else .top
    | _, _ => .top
  compare := compare

/-theorem widen_termination : ∀ (x : Nat -> Integers),
  IntegersValueDomain.IsIncreasing x -> ∃ (n : Nat),
  IntegersValueDomain.widenSeq x (.succ n) = IntegersValueDomain.widenSeq x n :=
by
  intros x H
  have H₀ := H 0
  have H₁ := H 1
  have H₂ := H 2
  simp [BoundedLattice.IsSubset] at *

  dsimp [BoundedLattice.meet, meet] at H₀ H₁ H₂

  cases h₀ : x 0 <;>
  cases h₁ : x 1 <;>
  cases h₂ : x 2 <;>
  cases h₃ : x 3 <;>
  simp [h₀] at H₀ <;>
  simp [h₁] at H₀ H₁ <;>
  simp [h₂] at H₁ H₂ <;>
  simp [h₃] at H₂ <;>

  (try split at H₀ <;> rename_i H₀') <;>
  (try split at H₁ <;> rename_i H₁') <;>
  (try split at H₂ <;> rename_i H₂') <;>

  (try next => cases H₀) <;>
  (try next => cases H₁) <;>
  (try next => cases H₂) <;>

  solve
  | exists 0; simp [Widen.widenSeq, Widen.widen, join, h₀, h₁, h₂, h₃, H₀, H₁, H₂];
    try simp [H₀']
  | exists 1; simp [Widen.widenSeq, Widen.widen, join, h₀, h₁, h₂, h₃, H₀, H₁, H₂];
    try simp [H₁']
  | exists 2; simp [Widen.widenSeq, Widen.widen, join, h₀, h₁, h₂, h₃, H₀, H₁, H₂];
    try simp [H₂']-/
end Integers
end Lustrean
