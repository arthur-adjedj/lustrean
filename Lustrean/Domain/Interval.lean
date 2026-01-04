import Lustrean.Domain.NonRelational
import Misc.Int

namespace Lustrean
/-- int or -∞ -/
inductive IntLow where
  | int (n : Int)
  | minf
  deriving DecidableEq

namespace IntLow
instance : Repr IntLow where
  reprPrec
    | .int n, _ => s!"{n}"
    | .minf, _ => "-∞"

inductive Le : IntLow → IntLow → Prop where
  | minf m : Le .minf m
  | leq n m : n ≤ m → Le (.int n) (.int m)

instance : LE IntLow where
  le := Le

theorem Le_refl : ∀ (l : IntLow), Le l l :=
by
  intros l
  cases l <;> constructor
  apply Int.le_refl

theorem Le_total : ∀ (l₁ l₂ : IntLow), Le l₁ l₂ ∨ Le l₂ l₁ :=
by
  intros l₁ l₂
  cases l₁ <;> cases l₂ <;>
  try (next => solve | left ; constructor | right ; constructor)
  rename_i n m
  cases (Int.le_total n m) <;>
  try (next => solve | left ; constructor ; assumption | right ; constructor ; assumption)

theorem Le_trans : ∀ {h₁ h₂ h₃ : IntLow},
  Le h₁ h₂ → Le h₂ h₃ → Le h₁ h₃ :=
by
  intros h₁ h₂ h₃ hyp hyp'
  cases hyp <;> (try constructor)
  cases hyp' ; try constructor
  apply Int.le_trans <;> assumption

instance (n m : IntLow) : Decidable (Le n m) := by
  cases n
  · cases m
    · rename_i n m
      by_cases h : n ≤ m
      · apply Decidable.isTrue
        constructor
        assumption
      · apply Decidable.isFalse
        intros h'
        cases h'
        contradiction
    · apply Decidable.isFalse
      intros h
      cases h
  · apply Decidable.isTrue
    constructor

def add (n m : IntLow) : IntLow :=
  match n, m with
  | .minf, _ | _, .minf => .minf
  | .int n, .int m => .int (n + m)

instance : Add IntLow where
  add := add

@[simp]
theorem add_minf_m : ∀ m : IntLow, .minf + m = .minf := by
  intros m
  cases m <;> rfl

@[simp]
theorem add_n_minf : ∀ n : IntLow, n + .minf = .minf := by
  intros n
  cases n <;> rfl

@[simp]
theorem add_n_m : ∀ n m, .int n + .int m = IntLow.int (n + m) := by
  intros
  rfl

def min (n m : IntLow) : IntLow :=
  match n, m with
  | .minf, _ | _, .minf => .minf
  | .int n, .int m => .int (Min.min n m)

instance : Min IntLow where
  min := min

@[simp]
theorem min_minf : ∀ (n : IntLow),
  min n .minf = .minf :=
by
  intro n; cases n <;> simp [min]

@[simp]
theorem minf_min : ∀ (n : IntLow),
  min .minf n = .minf :=
by
  intro n; cases n <;> simp [min]

theorem min_comm : ∀ (n m : IntLow),
  min n m = min m n :=
by
  intro n m
  cases n <;> cases m <;>
  simp [min, Int.min_comm]

theorem min_assoc : ∀ (n m o : IntLow),
  min (min n m) o = min n (min m o) :=
by
  intro n m o
  cases n <;> cases m <;> cases o <;> simp [min]

def max (n m : IntLow) : IntLow :=
  match n, m with
  | .int n, .int m => .int (Max.max n m)
  | .int n, .minf | .minf, .int n => .int n
  | .minf, .minf => .minf

instance : Max IntLow where
  max := max

@[simp]
theorem max_minf : ∀ (n : IntLow),
  max n .minf = n :=
by
  intro n
  cases n <;> simp [max]

@[simp]
theorem minf_max : ∀ (n : IntLow),
  max .minf n = n :=
by
  intro n
  cases n <;> simp [max]

@[simp]
theorem max_refl : ∀ (n : IntLow),
  max n n = n :=
by
  intro n
  cases n <;> simp [max]

theorem max_comm : ∀ (n m : IntLow),
  max n m = max m n :=
by
  intro n m
  cases n <;> cases m <;>
  simp [max, Int.max_comm]

theorem max_assoc : ∀ (n m o : IntLow),
  max (max n m) o = max n (max m o) :=
by
  intro n m o
  cases n <;> cases m <;> cases o <;> simp [max]

theorem min_max_absorb : ∀ (l₁ l₂ : IntLow),
  min l₁ (max l₁ l₂) = l₁ :=
by
  intro l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [min, max]
  apply Int.min_max_absorb

theorem max_min_absorb : ∀ (l₁ l₂ : IntLow),
  max l₁ (min l₁ l₂) = l₁ :=
by
  intro l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [min, max]
  apply Int.max_min_absorb

theorem Le_max_right : ∀ l₁ l₂ : IntLow, l₂ ≤ (max l₁ l₂) :=
by
  intros l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [max] <;> constructor
  · apply Int.le_max_right
  · apply Int.le_refl

theorem max_eq_left : ∀ {l₁ l₂ : IntLow},
  Le l₂ l₁ → l₁.max l₂ = l₁ :=
by
  intros l₁ l₂ hle
  cases hle
  · simp
  · simp [max]
    apply Int.max_eq_left
    assumption

instance : ToString IntLow where
  toString n := match n with
  | .minf => "-∞"
  | .int n => toString n

instance : DecidableEq IntLow := by
  intros x y
  cases x <;> cases y <;> simp <;>
  exact inferInstance
end IntLow

-- int or +∞
inductive IntHigh where
  | int (n : Int)
  | pinf
  deriving DecidableEq

namespace IntHigh
instance : Repr IntHigh where
  reprPrec
    | .int n, _ => s!"{n}"
    | .pinf, _ => "∞"

inductive Le : IntHigh → IntHigh → Prop where
  | pinf_ge n : Le n pinf
  | leq n m : n ≤ m → Le (.int n) (.int m)

instance : LE IntHigh where
  le := Le

@[simp]
theorem Le_refl : ∀ (l : IntHigh), Le l l :=
by
  intros l
  cases l <;> constructor
  apply Int.le_refl

theorem Le_total : ∀ (h₁ h₂ : IntHigh), Le h₁ h₂ ∨ Le h₂ h₁ :=
by
  intros h₁ h₂
  cases h₁ <;> cases h₂ <;>
  try (next => solve | left ; constructor | right ; constructor)
  rename_i n m
  cases (Int.le_total n m) <;>
  try (next => solve | left ; constructor ; assumption | right ; constructor ; assumption)

theorem Le_trans : ∀ {h₁ h₂ h₃ : IntHigh},
  Le h₁ h₂ → Le h₂ h₃ → Le h₁ h₃ :=
by
  intros h₁ h₂ h₃ hyp hyp'
  cases hyp <;> (try constructor) <;>
  cases hyp' <;> try constructor
  apply Int.le_trans <;> assumption

instance (n m : IntHigh) : Decidable (Le n m) := by
  cases m
  · cases n
    · rename_i m n
      by_cases h : n ≤ m
      · apply Decidable.isTrue
        constructor
        assumption
      · apply Decidable.isFalse
        intros h'
        cases h'
        contradiction
    · apply Decidable.isFalse
      intros h
      cases h
  · apply Decidable.isTrue
    constructor

def add (n m : IntHigh) : IntHigh :=
  match n, m with
  | .pinf, _ | _, .pinf => .pinf
  | .int n, .int m => .int (n + m)

instance : Add IntHigh where
  add := add

@[simp]
theorem add_pinf_m : ∀ m, .pinf + m = IntHigh.pinf := by
  intros m
  cases m <;> rfl

@[simp]
theorem add_n_pinf : ∀ n, n + .pinf = IntHigh.pinf := by
  intros n
  cases n <;> rfl

@[simp]
theorem add_n_m : ∀ n m, .int n + .int m = IntHigh.int (n + m) := by
  intros
  rfl

def max (n m : IntHigh) : IntHigh :=
  match n, m with
  | .pinf, _ | _, .pinf => .pinf
  | .int n, .int m => .int (Max.max n m)

instance : Max IntHigh where
  max := max

@[simp]
theorem max_pinf : ∀ (n : IntHigh),
  max n .pinf = .pinf :=
by
  intro n; cases n <;> simp [max]

@[simp]
theorem pinf_max : ∀ (n : IntHigh),
  max .pinf n = .pinf :=
by
  intro n; cases n <;> simp [max]


theorem max_comm : ∀ (n m : IntHigh),
  max n m = max m n :=
by
  intro n m
  cases n <;> cases m <;>
  simp [max, Int.max_comm]

theorem max_assoc : ∀ (n m o : IntHigh),
  max (max n m) o = max n (max m o) :=
by
  intro n m o
  cases n <;> cases m <;> cases o <;> simp [max]

def min (n m : IntHigh) : IntHigh :=
  match n, m with
  | .int n, .int m => .int (Min.min n m)
  | .int n, .pinf | .pinf, .int n => .int n
  | .pinf, .pinf => .pinf

instance : Min IntHigh where
  min := min

@[simp]
theorem min_pinf : ∀ (n : IntHigh),
  min n .pinf = n :=
by
  intro n
  cases n <;> simp [min]

@[simp]
theorem pinf_min : ∀ (n : IntHigh),
  min .pinf n = n :=
by
  intro n
  cases n <;> simp [min]

@[simp]
theorem min_refl : ∀ (n : IntHigh),
  min n n = n :=
by
  intro n
  cases n <;> simp [min]

theorem min_comm : ∀ (n m : IntHigh),
  min n m = min m n :=
by
  intro n m
  cases n <;> cases m <;>
  simp [min, Int.min_comm]

theorem min_assoc : ∀ (n m o : IntHigh),
  min (min n m) o = min n (min m o) :=
by
  intro n m o
  cases n <;> cases m <;> cases o <;> simp [min]

theorem max_min_absorb : ∀ (h₁ h₂ : IntHigh),
  max h₁ (min h₁ h₂) = h₁ :=
by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> simp [min, max]
  apply Int.max_min_absorb

theorem min_max_absorb : ∀ (h₁ h₂ : IntHigh),
  min h₁ (max h₁ h₂) = h₁ :=
by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> simp [min, max]
  apply Int.min_max_absorb

theorem Le_min_right : ∀ (h₁ h₂ : IntHigh), Le (min h₁ h₂) h₂ :=
by
  intros h₁ h₂
  cases h₁ <;> cases h₂ <;> simp [min] <;> constructor
  apply Int.min_le_right

theorem min_eq_left : ∀ {h₁ h₂ : IntHigh},
  Le h₁ h₂ → h₁.min h₂ = h₁ :=
by
  intros h₁ h₂ hle
  cases hle
  · simp
  · simp [min]
    apply Int.min_eq_left
    assumption

instance : ToString IntHigh where
  toString n := match n with
  | .pinf => "+∞"
  | .int n => toString n

instance : DecidableEq IntHigh := by
  intros x y
  cases x <;> cases y <;> simp <;>
  exact inferInstance
end IntHigh

inductive HLe : IntLow → IntHigh → Prop where
  | minf m : HLe .minf m
  | pinf n : HLe n .pinf
  | int_ord n m : n ≤ m → HLe (.int n) (.int m)

namespace HLe
infix:30 " ≤∘ " => HLe

theorem HLe_Le : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
  IntLow.Le l₂ l₁ → IntHigh.Le h₁ h₂ →
  HLe l₁ h₁ → HLe l₂ h₂ :=
by
  intros l₁ l₂ h₁ h₂ lel leh hle
  cases lel <;> try constructor
  cases leh <;> try constructor
  cases hle
  apply Int.le_trans <;> try assumption
  apply Int.le_trans <;> try assumption

@[simp]
theorem hle_int : ∀ n m, .int n ≤∘ .int m ↔ n ≤ m := by
  intros n m
  constructor <;>
  intro leq <;>
  (first | cases leq | constructor) <;>
  assumption

@[simp]
theorem hle_minf : ∀ m, .minf ≤∘ m := by
  intro
  constructor

@[simp]
theorem hle_pinf : ∀ n, n ≤∘ .pinf := by
  intro
  constructor

instance (low : IntLow) (high : IntHigh) : Decidable (low ≤∘ high) := by
  cases low <;>
  cases high <;>
  simp <;>
  apply inferInstance

theorem add_monotone : ∀ n₁ n₂ m₁ m₂, n₁ ≤∘ m₁ → n₂ ≤∘ m₂ → n₁ + n₂ ≤∘ m₁ + m₂ := by
  intros n₁ n₂ m₁ m₂ n₁_leq_m₁ n₂_leq_m₂
  cases n₁
  case minf => simp
  cases n₂
  case minf => simp
  cases m₁
  case pinf => simp
  cases m₂
  case pinf => simp
  cases n₁_leq_m₁
  cases n₂_leq_m₂
  simp
  omega
end HLe

namespace IntLow
def subLH (l : IntLow) (h : IntHigh) : IntLow :=
  match l, h with
  | .minf, _ | _, .pinf => .minf
  | .int n, .int m => .int (n - m)
end IntLow

namespace IntHigh
def subHL (h : IntHigh) (l : IntLow) : IntHigh :=
  match h, l with
  | .pinf, _ | _, .minf => .pinf
  | .int n, .int m => .int (n - m)
end IntHigh

namespace HLe
theorem sub_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
  l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → IntLow.subLH l₁ h₂ ≤∘ IntHigh.subHL h₁ l₂ :=
by
  intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
  cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;> try constructor
  rename_i a b c d
  cases hyp₁ ; cases hyp₂ ;
  apply Int.sub_le_sub <;> assumption

theorem min_max_monotone : ∀ (l₁ l₂ : IntLow) (h₁ h₂ : IntHigh),
  l₁ ≤∘ h₁ → l₂ ≤∘ h₂ → min l₁ l₂ ≤∘ max h₁ h₂ :=
by
  intro l₁ l₂ h₁ h₂ hyp₁ hyp₂
  cases l₁ <;> cases l₂ <;> cases h₁ <;> cases h₂ <;>
  try constructor
  rename_i a b c d
  skip
  apply Int.le_trans
  · apply Int.min_le_left
  · apply Int.le_trans
    · cases hyp₁
      assumption
    · apply Int.le_max_left

theorem min_min_max_max : ∀ (l₁ l₂ l₃ : IntLow) (h₁ h₂ h₃ : IntHigh),
  max (max l₁ l₂) l₃ ≤∘ min (min h₁ h₂) h₃ →
  (max l₁ l₂ ≤∘ min h₁ h₂) ∧ (max l₂ l₃ ≤∘ min h₂ h₃) :=
by
  intro l₁ l₂ l₃ h₁ h₂ h₃ h
  apply And.intro <;>
  cases l₁ <;> cases l₂ <;> cases l₃ <;>
  cases h₁ <;> cases h₂ <;> cases h₃ <;>
  cases h <;> simp [min, max, IntLow.max, IntHigh.min] <;>
  (try assumption) <;> omega
end HLe

namespace IntLow
def neg (l : IntLow) : IntHigh :=
match l with
| .minf => .pinf
| .int n => .int (-n)

def mulLH (l : IntLow) (h : IntHigh) : Option IntLow :=
  match l, h with
  | .minf, .pinf => some .minf
  | .minf, .int n => match compare n 0 with
    | .lt => none
    | .eq => some (.int 0)
    | .gt => some .minf
  | .int n, .pinf => match compare n 0 with
    | .lt => some .minf
    | .eq => some (.int 0)
    | .gt => none
  | .int n, .int m => some (.int (n * m))

def mulLL (l₁ l₂ : IntLow) : Option IntLow :=
  match l₁, l₂ with
  | .minf, .minf => none
  | .int n, .int m => some (.int (n * m))
  | .minf, .int n
  | .int n, .minf => match compare n 0 with
    | .lt => none
    | .eq => some (.int 0)
    | .gt => some .minf

def mulHH (h₁ h₂ : IntHigh) : Option IntLow :=
  match h₁, h₂ with
  | .pinf, .pinf => none
  | .int n, .int m => some (.int (n * m))
  | .pinf, .int n
  | .int n, .pinf => match compare n 0 with
    | .lt => some .minf
    | .eq => some (.int 0)
    | .gt => none
end IntLow

namespace IntHigh
def neg (l : IntHigh) : IntLow :=
match l with
| .pinf => .minf
| .int n => .int (-n)

def mulHL (h : IntHigh) (l : IntLow) : Option IntHigh :=
  match h, l with
  | .pinf, .minf => some .pinf
  | .pinf, .int n => match compare n 0 with
    | .lt => none
    | .eq => some (.int 0)
    | .gt => some .pinf
  | .int n, .minf => match compare n 0 with
    | .lt => some .pinf
    | .eq => some (.int 0)
    | .gt => none
  | .int n, .int m => some (.int (n * m))

def mulHH (h₁ h₂ : IntHigh) : Option IntHigh :=
  match h₁, h₂ with
  | .pinf, .pinf => some .pinf
  | .int n, .int m => some (.int (n * m))
  | .pinf, .int n
  | .int n, .pinf => match compare n 0 with
    | .lt => none
    | .eq => some (.int 0)
    | .gt => some .pinf

def mulLL (l₁ l₂ : IntLow) : Option IntHigh :=
  match l₁, l₂ with
  | .minf, .minf => some .pinf
  | .int n, .int m => some (.int (n * m))
  | .minf, .int n
  | .int n, .minf => match compare n 0 with
    | .lt => some .pinf
    | .eq => some (.int 0)
    | .gt => none
end IntHigh

namespace HLe
@[simp]
theorem neg_rev_hle : ∀ (l : IntLow) (h : IntHigh),
  l ≤∘ h → h.neg ≤∘ l.neg
:= by
  intros l h hyp
  cases hyp <;> try constructor
  apply Int.neg_le_neg
  assumption
end HLe

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
  | empty : Interval constants
  | interval (low : IntLow) (high : IntHigh) : low ≤∘ high → Interval constants
  deriving Repr, Inhabited, DecidableEq

namespace Interval
variable {constants : List Int}
variable (x y z : Interval constants)

def mapEmpty (f : (low₁ low₂ : IntLow) → (high₁ high₂ : IntHigh) →
                   low₁ ≤∘ high₁ → low₂ ≤∘ high₂ →
                   Interval constants)
              : Interval constants :=
  match x, y with
  | .empty, _ | _, .empty => .empty
  | .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ => f l₁ l₂ h₁ h₂ o₁ o₂

def add : Interval constants :=
  mapEmpty x y <| fun l₁ l₂ h₁ h₂ o₁ o₂ =>
    .interval (l₁ + l₂) (h₁ + h₂) <| by apply HLe.add_monotone <;> assumption

instance : Add (Interval constants) where
  add := add

def neg : Interval constants := match x with
| .empty => .empty
| .interval l h o => .interval h.neg l.neg <| by
  apply HLe.neg_rev_hle
  assumption

instance : Neg (Interval constants) where
  neg := neg

def sub : Interval constants :=
  mapEmpty x y <| fun l₁ l₂ h₁ h₂ le₁ le₂ =>
    .interval (IntLow.subLH l₁ h₂) (IntHigh.subHL h₁ l₂)
      <| by apply HLe.sub_monotone <;> assumption

instance : Sub (Interval constants) where
  sub := sub

def bot : Interval constants := .empty

def top : Interval constants := .interval .minf .pinf <| by constructor

def join : Interval constants := match x, y with
| .empty, z | z, .empty => z
| .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ =>
  .interval (min l₁ l₂) (max h₁ h₂) <| by apply HLe.min_max_monotone <;> assumption

def meet : Interval constants := match x, y with
| .empty, _ | _, .empty => .empty
| .interval l₁ h₁ _, .interval l₂ h₂ _ =>
  if h : max l₁ l₂ ≤∘ min h₁ h₂
  then .interval (max l₁ l₂) (min h₁ h₂) h
  else .empty

theorem join_commutative : join x y = join y x :=
by
  cases x <;> cases y <;> simp [join]
  apply And.intro
  · apply IntLow.min_comm
  · apply IntHigh.max_comm

theorem join_associative : join (join x y) z = join x (join y z) :=
by
  cases x <;> cases y <;> cases z <;> dsimp [join]
  simp [min, max, IntLow.min_assoc, IntHigh.max_assoc]

theorem join_absorption : join x (meet x y) = x :=
by
  cases x <;> cases y <;> dsimp [join, meet]
  rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
  by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
  · rw [dif_pos h]
    dsimp
    simp [min, max, IntLow.min_max_absorb, IntHigh.max_min_absorb]
  · rw [dif_neg h]

theorem join_bot : join x bot = x :=
by
  cases x <;> dsimp [bot, join]

theorem join_top : join x top = top :=
by
  cases x <;>
  simp [join, top, min, max, IntLow.min_minf, IntHigh.max_pinf]

theorem meet_commutative : meet x y = meet y x :=
by
  cases x <;> cases y <;> simp [meet]
  split <;> split <;> try dsimp
  · simp [min, max, IntLow.max_comm, IntHigh.min_comm]
  all_goals try next hyp₁ hyp₂ =>
    exfalso
    simp [min, max] at hyp₁
    simp [min, max] at hyp₂
    rw [IntLow.max_comm, IntHigh.min_comm] at hyp₁
    solve | exact (hyp₁ hyp₂) | exact (hyp₂ hyp₁)

theorem meet_associative :
  meet (meet x y) z = meet x (meet y z) :=
by
  cases x <;> cases y <;> cases z <;> simp [meet]
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
    · rw [dif_pos h]
    · rw [dif_neg h]
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂ l₃ h₃ hyp₃
    by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
    · rw [dif_pos h] ; dsimp
      by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
      · rw [dif_pos h'] ; dsimp
        simp [min, max, IntLow.max_assoc, IntHigh.min_assoc]
      · rw [dif_neg h'] ; rw [dif_neg]
        intro H
        apply h'
        apply And.right
        apply HLe.min_min_max_max
        apply H
    · rw [dif_neg h] ; dsimp
      by_cases h' : max l₂ l₃ ≤∘ min h₂ h₃
      · rw [dif_pos h'] ; dsimp; rw [dif_neg]
        intro H
        apply h
        apply And.left
        apply HLe.min_min_max_max
        simp [min, max]
        rw [IntLow.max_assoc, IntHigh.min_assoc]
        apply H
      · rw [dif_neg h']

theorem meet_absorption : meet x (join x y) = x :=
by
  cases x <;> cases y <;> dsimp [join, meet]
  · rename_i l₁ h₁ hyp₁
    rw [dif_pos] <;> simp [max, min, IntLow.max_refl, IntHigh.min_refl]
    assumption
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    simp [min, max, IntLow.max_min_absorb, IntHigh.min_max_absorb]
    rw [dif_pos hyp₁]

theorem meet_bot : meet x bot = bot :=
by
  cases x <;> dsimp [meet, bot]

theorem meet_top : meet x top = x :=
by
  cases x <;> simp [meet, top, max, min]
  rename_i h
  rw [dif_pos h]

theorem non_trivial : (top : Interval constants) ≠ bot := by
  simp [top, bot]

instance BoundedLatticeInterval : BoundedLattice (Interval constants) where
  bot := bot
  top := top
  join := join
  meet := meet
  join_commutative := join_commutative
  join_associative := join_associative
  join_absorption := join_absorption
  join_bot := join_bot
  join_top := join_top
  meet_commutative := meet_commutative
  meet_associative := meet_associative
  meet_absorption := meet_absorption
  meet_bot := meet_bot
  meet_top := meet_top
  -- non_trivial := non_trivial

def splitAtZero : Interval constants × Interval constants :=
  (
    x.meet (.interval .minf (.int 0) <| by constructor),
    x.meet (.interval (.int 0) .pinf <| by constructor),
  )

def mulNegNeg : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match IntLow.mulHH h₁ h₂, IntHigh.mulLL l₁ l₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤∘ h
  then .interval l h hyp
  else .empty

def mulNegPos : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match IntLow.mulLH l₁ h₂, IntHigh.mulHL h₁ l₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤∘ h
  then .interval l h hyp
  else .empty

def mulPosPos : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match IntLow.mulLL l₁ l₂, IntHigh.mulHH h₁ h₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤∘ h
  then .interval l h hyp
  else .empty

def mul : Interval constants :=
  let (x₁, x₂) := splitAtZero x
  let (y₁, y₂) := splitAtZero y
  join
    ((mulNegNeg x₁ y₁).join (mulNegPos x₁ y₂))
    ((mulNegPos y₁ x₂).join (mulPosPos x₂ y₂))

instance : Mul (Interval constants) where
  mul := mul

def divPosPos : Interval constants := mapEmpty x y
fun _ _ h₁ h₂ _ _ =>
match h₁, h₂ with
| _, .int 0 => .bot
| .pinf, _ => .interval (.int 0) .pinf <| by constructor
| .int _, .pinf => .interval (.int 0) (.int 0) <| by constructor ; simp
| .int n, .int m => if hyp : 0 ≤ n / m
  then .interval (.int 0) (.int (n / m)) <| by constructor ; assumption
  else .bot

def divNegPos : Interval constants :=
  neg (divPosPos (neg x) y)

def divPosNeg : Interval constants :=
  neg (divPosPos x (neg y))

def divNegNeg : Interval constants :=
  divPosPos (neg x) (neg y)

def div : Interval constants :=
  let (x₁, x₂) := splitAtZero x
  let (y₁, y₂) := splitAtZero y
  join
    ((divNegNeg x₁ y₁).join (divNegPos x₁ y₂))
    ((divNegPos y₁ x₂).join (divPosPos x₂ y₂))

instance : Div (Interval constants) where
  div := div

def toString := match x with
| .empty => "∅"
| .interval l h _ => s!"[{l}; {h}]"

instance : ToString (Interval constants) where
  toString := toString

instance : DecidableEq (Interval constants) := by
  intros a b
  cases a <;> cases b <;> simp <;>
  exact inferInstance

def extractMaxGt (l : List Int) (h : IntLow) : IntLow :=
  match l with
  | [] => .minf
  | m :: l => if IntLow.Le h (.int m) -- if h <= m
      then extractMaxGt l h
      else max (.int m) (extractMaxGt l h)

def extractMaxGtCorrect : ∀ (l : List Int) (n : IntLow),
  IntLow.Le (extractMaxGt l n) n :=
by
  clear x y z
  intros l h
  induction l
  case nil => constructor
  case cons hd tl IH =>
    dsimp [extractMaxGt]
    split <;> rename_i hle
    · assumption
    · generalize heq : extractMaxGt tl h = x
      rw [heq] at IH
      cases IH
      · simp [max]
        cases h
        · constructor
          rename_i h
          have htot : hd ≤ h ∨ h ≤ hd := by apply Int.le_total
          cases htot <;> try assumption
          exfalso
          apply hle
          constructor
          assumption
        · exfalso
          apply hle
          constructor
      · dsimp [max, IntLow.max]
        constructor
        rw [Int.max_le]
        apply And.intro <;> try assumption
        rename_i n m a
        have htot : hd ≤ m ∨ m ≤ hd := by apply Int.le_total
        cases htot <;> try assumption
        exfalso
        apply hle
        constructor
        assumption

def extractMinGe (l : List Int) (h : IntHigh) : IntHigh :=
  match l with
  | [] => .pinf
  | m :: l => if IntHigh.Le (.int m) h -- if m <= h
      then extractMinGe l h
      else min (.int m) (extractMinGe l h)

def extractMinGeCorrect : ∀ (l : List Int) (h : IntHigh),
  IntHigh.Le h (extractMinGe l h) :=
by
  clear x y z
  intros l h
  induction l
  case nil => constructor
  case cons hd tl IH =>
    dsimp [extractMinGe]
    split <;> rename_i hle
    · assumption
    · generalize heq : extractMinGe tl h = x
      rw [heq] at IH
      cases IH
      · simp [min]
        cases h
        · constructor
          rename_i h
          cases (Int.le_total hd h) <;> try assumption
          exfalso
          apply hle
          constructor
          assumption
        · exfalso
          apply hle
          constructor
      · dsimp [min, IntHigh.min]
        constructor
        rw [Int.le_min]
        apply And.intro <;> try assumption
        rename_i n m a
        cases (Int.le_total hd n) <;> try assumption
        exfalso
        apply hle
        constructor
        assumption

def widen (n : Nat) : Interval constants :=
  if n <= 10
  then x.join y
  else match x, y with
  | .empty, z
  | z, .empty => z
  | .interval l₁ h₁ _, .interval l₂ h₂ o₂ =>
    let l := if IntLow.Le l₁ l₂
      then l₁
      else extractMaxGt constants l₂
    let h := if IntHigh.Le h₂ h₁
      then h₁
      else extractMinGe constants h₂
    .interval l h <| by
      dsimp [l, h]
      apply HLe.HLe_Le
      · by_cases hl : IntLow.Le l₁ l₂ <;> simp [hl]
        · assumption
        · apply extractMaxGtCorrect constants l₂
      · by_cases hr : IntHigh.Le h₂ h₁ <;> simp [hr]
        · assumption
        · apply extractMinGeCorrect constants h₂
      · assumption

theorem covering_left : ∀ (n : Nat),
  BoundedLattice.IsSubset x (x.widen y n) :=
by
  intros n
  cases x <;> simp [BoundedLattice.IsSubset, BoundedLattice.meet, meet, widen]
  by_cases h : n ≤ 10 <;> simp [h, join] <;>
  cases y <;> rename_i hle <;> simp [max, min, hle] <;> clear h
  · simp [IntLow.max_min_absorb, IntHigh.min_max_absorb]
    rename_i hle' _ _
    simp [hle']
  · rename_i l' h' hle' l h
    split <;> split <;> try simp
    · intro
      contradiction
    · have hyph : h'.Le h := by
        cases (IntHigh.Le_total h' h)
        · assumption
        · contradiction
      have hyph' : h'.min (extractMinGe constants h) = h' := by
        apply IntHigh.min_eq_left
        apply IntHigh.Le_trans
        · assumption
        · apply extractMinGeCorrect
      simp [hyph']
      intro; contradiction
    · have hypl : l.Le l' := by
        cases (IntLow.Le_total l l')
        · assumption
        · contradiction
      have hypl' : l'.max (extractMaxGt constants l) = l' := by
        apply IntLow.max_eq_left
        apply IntLow.Le_trans
        · apply extractMaxGtCorrect
        · assumption
      simp [hypl']
      intro
      contradiction
    · have hypl : l.Le l' := by
        cases (IntLow.Le_total l l')
        · assumption
        · contradiction
      have hypl' : l'.max (extractMaxGt constants l) = l' := by
        apply IntLow.max_eq_left
        apply IntLow.Le_trans
        · apply extractMaxGtCorrect
        · assumption
      have hyph : h'.Le h := by
        cases (IntHigh.Le_total h' h)
        · assumption
        · contradiction
      have hyph' : h'.min (extractMinGe constants h) = h' := by
        apply IntHigh.min_eq_left
        apply IntHigh.Le_trans
        · assumption
        · apply extractMinGeCorrect
      simp [hypl', hyph']
      intro
      contradiction

theorem covering_right : ∀ (n : Nat),
  BoundedLattice.IsSubset y (x.widen y n) :=
by
  intros n
  cases x <;> simp [BoundedLattice.IsSubset, BoundedLattice.meet, meet, widen] <;>
  by_cases h : n ≤ 10 <;> cases y <;>
  simp [h, join, bot] <;> clear h <;>
  rename_i l h hle  <;> simp [max, min, hle] <;>
  rename_i l' h' hle'
  · rw [dif_pos] <;> (try simp) <;>
    rw [IntLow.min_comm, IntHigh.max_comm, IntLow.max_min_absorb, IntHigh.min_max_absorb]
    · constructor <;> rfl
    · assumption
  · have hypl : l = l.max (extractMaxGt constants l) := by
        rw [IntLow.max_eq_left]
        apply extractMaxGtCorrect
    have hyph : h = h.min (extractMinGe constants h) := by
        rw [IntHigh.min_eq_left]
        apply extractMinGeCorrect
    split <;> split <;> rename_i hyp' hyp <;>
    rw [dif_pos] <;> (try simp) <;>
    (repeat first
      | rw [IntLow.max_eq_left hyp']
      | rw [IntHigh.min_eq_left hyp]
      | rw [← hypl]
      | rw [← hyph]
    ) <;> solve | simp | assumption

instance : Widen (Interval constants) where
  widen := widen

instance : WidenLawful (Interval constants) where
  covering_left := covering_left
  covering_right := covering_right

def narrow (_ : Nat) : Interval constants :=
  x ⊓ y

theorem bounding_low :
  ∀ (x y : Interval constants) (n : Nat),
  (x ⊓ y) ⊑ (narrow x y n) :=
by
  intros x y n
  have hx : x.meet x = x := BoundedLattice.meet_idempotent x
  have hy : y.meet y = y := BoundedLattice.meet_idempotent y
  simp [BoundedLattice.IsSubset, narrow]
  conv =>
    rhs
    arg 2
    rw [meet_commutative]
  rw [meet_associative]
  conv =>
    rhs
    arg 2
    rw [←meet_associative, hy, meet_commutative]
  rw [←meet_associative, hx]

theorem bounding_high :
  ∀ (x y : Interval constants) (n : Nat),
  (narrow x y n) ⊑ x :=
by
  intros x y n
  simp [narrow]
  rw [BoundedLattice.IsSubset]
  unfold BoundedLattice.meet
  unfold BoundedLatticeInterval
  simp
  rw [meet_associative]
  conv =>
    rhs
    arg 2
    rw [meet_commutative]
  rw [
    ← meet_associative,
    show x.meet x = x by apply BoundedLattice.meet_idempotent
  ]

instance : Narrow (Interval constants) where
  narrow := narrow

instance : NarrowLawful (Interval constants) where
  bounding_low := bounding_low
  bounding_high := bounding_high

def measure : CompareOp → Nat
  | .eq => 0
  | .neq => 3
  | .le => 0
  | .lt => 1
  | .ge => 2
  | .gt => 2

def compare (op : CompareOp) (x y : Interval constants) :
  Interval constants × Interval constants
:=
  match x, y with
  | .empty, _
  | _, .empty => (.empty, .empty)
  | .interval l₁ h₁ _, .interval l₂ h₂ _ =>
    match op with
    | .eq => (x.meet y, x.meet y)
    | .neq =>
      let (x', y') := compare .lt x y
      let (x'', y'') := compare .gt x y
      (x'.join x'', y'.join y'')
    | .le =>
      let l := l₁.max l₂
      let h := h₁.min h₂
      (
        if hyp₁ : l₁ ≤∘ h
        then .interval l₁ h hyp₁
        else .empty,
        if hyp₂ : l ≤∘ h₂
        then .interval l h₂ hyp₂
        else .empty
      )
    | .lt =>
      let one := .interval (.int 1) (.int 1) <| by simp
      let (x', y') := compare .le (x + one) y
      (x' - one, y')
    | .ge =>
      let (y', x') := compare .le y x
      (x', y')
    | .gt =>
      let (y', x') := compare .lt y x
      (x', y')
  termination_by measure op
  decreasing_by all_goals simp [measure]

instance : ValueDomain (Interval constants) where
  nil := ⊤                    -- we have no better approximation for nil in this domain than ⊤
  rand
    | .some x, .some y => if h : x ≤ y
      then .interval (.int x) (.int y) <| by constructor; assumption
      else .empty
    | .none, .some y => .interval .minf (.int y) <| by constructor
    | .some x, .none => .interval (.int x) .pinf <| by constructor
    | .none, .none => .interval .minf .pinf <| by constructor
  compare := compare

  -- TODO: pourquoi ça n'infère pas ??
  covering_left := WidenLawful.covering_left
  covering_right := WidenLawful.covering_right

  bounding_low := NarrowLawful.bounding_low
  bounding_high := NarrowLawful.bounding_high
end Interval
end Lustrean
