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

@[simp, local grind .]
theorem Le.leq_iff n m : (int n).Le (int m) ↔ n ≤ m := by
  constructor
  · intros h; cases h; assumption;
  · apply Le.leq

@[simp, local grind .]
theorem Le.le_iff n m: int n ≤ int m ↔ n ≤ m := by simp only [LE.le, Le.leq_iff]

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

instance (n m : IntLow) : Decidable (n ≤ m) := by
  simp only [LE.le]
  infer_instance

instance: Std.IsLinearOrder IntLow where
  le_refl := Le_refl
  le_trans := @Le_trans
  le_antisymm := by
    rintro x y xy yx
    rcases xy <;> rcases yx <;> simp only [int.injEq]
    apply Int.le_antisymm <;> simp [*]
  le_total := by
    rintro (_ | ⟨x⟩) (_ | ⟨y⟩) <;>
    dsimp only [LE.le] <;> grind [Le]

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

theorem min_def (n m : IntLow): n ⊓ m = if n ≤ m then n else m := by
  dsimp [Min.min]
  fun_cases (n.min m) with
  | case3 n m => grind
  | case1 =>
    have: minf ≤ m := by simp [LE.le, Le.minf m]
    simp [*]
  | case2 => simp; rintro (_ | _); rfl

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

theorem max_def (n m: IntLow): n ⊔ m = if n ≤ m then m else n := by
  dsimp [Max.max]
  fun_cases (n.max m) with
  | case1 n m => grind [max]
  | case2 =>
    simp; rintro (_| _)
  | case3 => simp; constructor
  | case4 => simp

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

theorem max_min_absorb : ∀ (l₁ l₂ : IntLow),
  max l₁ (min l₁ l₂) = l₁ :=
by
  intro l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [min, max]

theorem Le_max_right : ∀ l₁ l₂ : IntLow, l₂ ≤ (max l₁ l₂) :=
by
  intros l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [max]; constructor

theorem max_eq_left : ∀ {l₁ l₂ : IntLow},
  Le l₂ l₁ → l₁.max l₂ = l₁ :=
by
  intros l₁ l₂ hle
  cases hle
  · simp
  · simp [max, *]

instance : ToString IntLow where
  toString n := match n with
  | .minf => "-∞"
  | .int n => toString n

instance : DecidableEq IntLow := by
  intros x y
  cases x <;> cases y <;> simp <;>
  exact inferInstance

theorem join_is_lub
: ∀ (x y z: IntLow), x = x ⊓ z → y = y ⊓ z → x ⊔ y = x ⊔ y ⊓ z
:= by grind only

theorem meet_is_glb
: ∀ (x y z: IntLow), z = z ⊓ x → z = z ⊓ y → z = z ⊓ x ⊓ y
:= by grind only

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

@[simp, local grind .]
theorem Le.leq_iff n m : (int n).Le (int m) ↔ n ≤ m := by
  constructor
  · intros h; cases h; assumption;
  · apply Le.leq

@[simp, local grind .]
theorem Le.le_iff n m: int n ≤ int m ↔ n ≤ m := by simp only [LE.le, Le.leq_iff]

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
  cases hyp <;>
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

instance (n m : IntHigh) : Decidable (n ≤ m) := by
  simp only [LE.le]; infer_instance

instance: Std.IsLinearOrder IntHigh where
  le_refl := Le_refl
  le_trans := @Le_trans
  le_antisymm := by
    rintro x y xy yx
    rcases xy <;> rcases yx <;> simp only [int.injEq]
    apply Int.le_antisymm <;> simp [*]
  le_total := by
    rintro (_ | ⟨x⟩) (_ | ⟨y⟩) <;>
    dsimp only [LE.le] <;> grind [Le]

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

theorem max_def (n m:IntHigh): n ⊔ m = if n ≤ m then m else n := by
  dsimp [Max.max]
  match n, m with
  | .pinf, e  => simp only [max, right_eq_ite_iff]; rintro (_ | _); rfl
  | .int e, .pinf => simp [max]; constructor
  | .int n', .int m' => grind [max]

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

theorem min_def (n m : IntHigh): n ⊓ m = if n ≤ m then n else m := by
  dsimp [Min.min]
  fun_cases (n.min m) with
  | case1 n m => grind
  | case2 => simp; constructor
  | case3 => simp; rintro (_ | _)
  | case4 => simp

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

theorem min_max_absorb : ∀ (h₁ h₂ : IntHigh),
  min h₁ (max h₁ h₂) = h₁ :=
by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> simp [min, max]

theorem Le_min_right : ∀ (h₁ h₂ : IntHigh), Le (min h₁ h₂) h₂ :=
by
  intros h₁ h₂
  cases h₁ <;> cases h₂ <;> simp [min]; constructor

theorem min_eq_left : ∀ {h₁ h₂ : IntHigh},
  Le h₁ h₂ → h₁.min h₂ = h₁ :=
by
  intros h₁ h₂ hle
  cases hle
  · simp
  · simp [min, *]

instance : ToString IntHigh where
  toString n := match n with
  | .pinf => "+∞"
  | .int n => toString n

instance : DecidableEq IntHigh := by
  intros x y
  cases x <;> cases y <;> simp <;>
  exact inferInstance

theorem join_is_lub
: ∀ (x y z: IntHigh), x = x ⊓ z → y = y ⊓ z → x ⊔ y = x ⊔ y ⊓ z
:= by grind only

theorem meet_is_glb
: ∀ (x y z: IntHigh), z = z ⊓ x → z = z ⊓ y → z = z ⊓ x ⊓ y
:= by grind only

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
  apply Int.le_trans
  · apply Int.min_le_left
  · apply Int.le_trans
    · cases hyp₁
      assumption
    · apply Int.le_max_left

set_option maxHeartbeats 1000000 in
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

theorem hle_le_trans {nₗ mₗ: IntLow} {nₕ mₕ: IntHigh}
: nₗ ≤ mₗ → mₗ ≤∘ mₕ → mₕ ≤ nₕ → nₗ ≤∘ nₕ
:= by
  rcases nₗ with nₗ | _; case minf => intros; constructor
  rcases nₕ with nₕ | _; case pinf => intros; constructor
  match mₗ, mₕ with
  | .int mₗ, .int mₕ => grind only [IntLow.Le.le_iff, hle_int, IntHigh.Le.le_iff]
  | .minf,   .int mₕ => rintro (_ | _)
  | .int mₗ, .pinf   => rintro _ _ (_ | _)
  | .minf,   .pinf   => rintro (_ | _)
end HLe

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
  | empty : Interval constants
  | interval (low : IntLow) (high : IntHigh) : low ≤∘ high → Interval constants
  deriving Repr, Inhabited, DecidableEq

@[grind]
instance(cts: List Int): Bot (Interval cts) where bot := .empty
instance(cts: List Int): EmptyCollection (Interval cts) where emptyCollection := .empty
instance(cts: List Int): Top (Interval cts) where top := .interval .minf .pinf (by constructor)

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

instance: Max (Interval constants) where
  max := join

def meet : Interval constants := match x, y with
| .empty, _ | _, .empty => .empty
| .interval l₁ h₁ _, .interval l₂ h₂ _ =>
  if h : max l₁ l₂ ≤∘ min h₁ h₂
  then .interval (max l₁ l₂) (min h₁ h₂) h
  else .empty

instance: Min (Interval constants) where
  min := meet

theorem join_commutative : x ⊔ y = y ⊔ x :=
by
  dsimp [Max.max]
  cases x <;> cases y <;> simp [join]
  apply And.intro
  · apply IntLow.min_comm
  · apply IntHigh.max_comm

theorem join_associative : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  dsimp [Max.max]
  cases x <;> cases y <;> cases z <;> dsimp [join]
  simp [min, max, IntLow.min_assoc, IntHigh.max_assoc]

theorem join_absorption : x ⊔ (x ⊓ y) = x :=
by
  dsimp [Max.max, Min.min]
  cases x <;> cases y <;> dsimp [join, meet]
  rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
  by_cases h : max l₁ l₂ ≤∘ min h₁ h₂
  · rw [dif_pos h]
    dsimp
    simp [min, max, IntLow.min_max_absorb, IntHigh.max_min_absorb]
  · rw [dif_neg h]

theorem join_bot : x ⊔ ⊥ = x :=
by
  dsimp [Max.max, Bot.bot]
  cases x <;> dsimp [bot, join]

theorem join_top : x ⊔ ⊤ = ⊤ :=
by
  dsimp [Max.max, Top.top]
  cases x <;> dsimp [join]
  simp [min, max, IntLow.min_minf, IntHigh.max_pinf]

theorem meet_commutative : x ⊓ y = y ⊓ x :=
by
  dsimp [Min.min]
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
  (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  dsimp [Min.min]
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

theorem meet_absorption : x ⊓ (x ⊔ y) = x :=
by
  dsimp [Min.min, Max.max]
  cases x <;> cases y <;> dsimp [join, meet]
  · rename_i l₁ h₁ hyp₁
    rw [dif_pos] <;> simp [max, min, IntLow.max_refl, IntHigh.min_refl]
    assumption
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    simp [min, max, IntLow.max_min_absorb, IntHigh.min_max_absorb]
    rw [dif_pos hyp₁]

theorem meet_bot : x ⊓ ⊥ = ⊥ :=
by
  dsimp [Min.min, Bot.bot]
  cases x <;> dsimp [meet, bot]

theorem meet_top : x ⊓ ⊤ = x :=
by
  dsimp [Min.min]
  cases x <;> simp [meet, max, min]
  rename_i h
  rw [dif_pos h]

theorem non_trivial : (⊤ : Interval constants) ≠ ⊥ := by
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

@[grind =]
theorem empty_is_bot : Interval.empty (constants := constants) = ⊥ := rfl

theorem join_is_lub
: ∀ (x y z : Interval constants), x = x ⊓ z → y = y ⊓ z → x ⊔ y = (x ⊔ y) ⊓ z
:= by
  rintro (_ | ⟨xₗ,xₕ,hx⟩)
  case empty => grind [meet_commutative, meet_bot, join_commutative, join_bot]
  rintro (_ | ⟨yₗ,yₕ,hy⟩)
  case empty => grind [meet_commutative, meet_bot, join_commutative, join_bot]
  rintro (_ | ⟨zₗ,zₕ,zy⟩)
  case empty => grind [meet_commutative, meet_bot, join_commutative, join_bot]
  dsimp [Min.min, Max.max]
  dsimp only [meet, join]
  intro xz
  split at xz; case isFalse => simp only [reduceCtorEq] at xz
  rename_i hx
  intros yz
  split at yz; case isFalse => simp only [reduceCtorEq] at yz
  rename_i hy
  simp only [interval.injEq] at xz yz
  grind [IntLow.max_def, IntHigh.min_def, IntLow.min_def, IntHigh.max_def]


theorem meet_is_glb
: ∀ (x y z : Interval constants), z = z ⊓ x → z = z ⊓ y → z = z ⊓ (x ⊓ y)
:= by
  rintro (_ | ⟨xₗ,xₕ,hx⟩)
  case empty => grind [meet_commutative, meet_bot]
  rintro (_ | ⟨yₗ,yₕ,hy⟩)
  case empty => grind [meet_commutative, meet_bot]
  rintro (_ | ⟨zₗ,zₕ,zy⟩)
  case empty => grind [meet_commutative, meet_bot]
  dsimp [Min.min]
  dsimp only [meet]
  intro xz
  split at xz; case isFalse => simp only [reduceCtorEq] at xz
  rename_i hx
  intros yz
  split at yz; case isFalse => simp only [reduceCtorEq] at yz
  rename_i hy
  simp only [interval.injEq] at xz yz
  have cond: xₗ ⊔ yₗ ≤∘ xₕ ⊓ yₕ  := by
    -- Basically, we prove this by putting `zₗ` and `zₕ` in between
    have lhs: xₗ ⊔ yₗ ≤ zₗ := by grind [IntLow.max_def]
    have rhs: zₕ ≤ xₕ ⊓ yₕ := by grind [IntHigh.min_def]
    apply HLe.hle_le_trans lhs zy rhs
  grind [IntHigh.min_def, IntLow.min_def, IntLow.max_def, IntHigh.max_def]


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
  join_is_lub := join_is_lub
  meet_is_glb := meet_is_glb

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

attribute [-simp] BoundedLattice.min_bot_is_bot

theorem covering_left : ∀ (n : Nat),
  BoundedLattice.IsSubset x (x.widen y n) :=
by
  intros n
  rcases x with _ | ⟨l', h', hle'⟩ <;>
  simp only [BoundedLattice.IsSubset, Min.min, meet, widen]
  -- case minf =>
  --   by_cases h : n ≤ 10 <;> simp [h, join] <;>
  --   simp
  --   sorry
  by_cases this: n ≤ 10 <;> simp [this, join] <;>
  rcases y with _ | ⟨l, h, hle⟩ <;> simp [max, min, *]
  · simp [IntLow.max_min_absorb, IntHigh.min_max_absorb, *]
  · split <;> split <;> try simp
    · assumption
    · have hyph : h'.Le h := by
        cases (IntHigh.Le_total h' h)
        · assumption
        · contradiction
      have hyph' : h'.min (extractMinGe constants h) = h' := by
        apply IntHigh.min_eq_left
        apply IntHigh.Le_trans
        · assumption
        · apply extractMinGeCorrect
      simpa [hyph']
    · have hypl : l.Le l' := by
        cases (IntLow.Le_total l l')
        · assumption
        · contradiction
      have hypl' : l'.max (extractMaxGt constants l) = l' := by
        apply IntLow.max_eq_left
        apply IntLow.Le_trans
        · apply extractMaxGtCorrect
        · assumption
      simpa [hypl']
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
      simpa [hypl', hyph']

theorem covering_right : ∀ (n : Nat),
  BoundedLattice.IsSubset y (x.widen y n) :=
by
  intros n
  rcases x with _ | ⟨l,h,hle⟩ <;> simp [BoundedLattice.IsSubset, Min.min, meet, widen] <;>
  by_cases hc : n ≤ 10 <;>
  rcases y with _ | ⟨l', h', hle'⟩ <;>
  simp [hc, join]
  · simp [Max.max, *]
  · simp [Max.max, *]
  · simp [Max.max, Min.min,
      IntLow.max_min_absorb, IntLow.min_comm l,
      IntHigh.min_max_absorb, IntHigh.max_comm h,
      hle']
  · have hypl : l' = l'.max (extractMaxGt constants l') := by
        rw [IntLow.max_eq_left]
        apply extractMaxGtCorrect
    have hyph : h' = h'.min (extractMinGe constants h') := by
        rw [IntHigh.min_eq_left]
        apply extractMinGeCorrect
    split <;> split <;> rename_i hyp' hyp <;>
    simp only [Max.max, IntLow.max_eq_left, hyp',
                        IntHigh.min_eq_left, hyp,
                        hle', ↓reduceDIte,
                        ←hyph, ←hypl]

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

theorem bounding_high :
  ∀ (x y : Interval constants) (n : Nat),
  (narrow x y n) ⊑ x :=
by
  intros x y n
  simp [narrow]

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
