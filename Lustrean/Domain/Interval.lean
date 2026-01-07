import Lustrean.Domain.NonRelational
import Misc.Int
import Mathlib.Order.WithBot

namespace Lustrean

abbrev ClosedInt := WithTop (WithBot Int)

#synth Std.IsLinearOrder ClosedInt
instance: SMul ℕ Int where smul s n := s * n

@[to_dual] instance {α: Type}[ι: Add α]: Add (WithBot α) where
  add x y := show Option α from do ι.add (←x) (←y)

@[to_dual] instance{α β: Type*}[ι:SMul α β]: SMul α (WithBot β) where
  smul s n := show Option _ from do ι.smul s (←n)

instance {α: Type}[ι: Mul α]: Mul (WithTop (WithBot α)) where
  mul
  | ⊤, ⊥ | ⊥, ⊤ => ⊥
  | ⊥, ⊥ | ⊤, ⊤ => ⊤
  | ⊤, _ | _, ⊤ => ⊤
  | ⊥, _ | _, ⊥ => ⊤
  | .some (.some x), .some (.some y) => ι.mul x y

instance {α: Type}[ι: Neg α]: Neg (WithTop (WithBot α)) where
  neg
  | ⊤ => ⊥
  | ⊥ => ⊤
  | .some (.some e) => ι.neg e

instance: Sub ClosedInt where sub x y := x + (-y)

instance: Zero ClosedInt where zero := .some (.some 0)

@[to_dual] instance{α: Type*}[ι:One α]: One (WithBot α) where
  one := ι.one

instance: Lean.Grind.IntModule ClosedInt where
  add_zero := by
    rintro (_ | (_ | _)) <;> simp [HAdd.hAdd, Add.add, Zero.zero]
    sorry

instance: SMul ℕ ClosedInt where
  smul s
  | ⊥ => ⊥
  | ⊤ => ⊤
  | .some (.some n) => .some (.some)

#synth Lean.Grind.IntModule (ClosedInt)

Neg M, Sub M

-- Parameterized by the list of constants
-- in the source program, in order to do
-- a better widening
inductive Interval (constants : List Int) where
  | empty : Interval constants
  | interval (low : ClosedInt) (high : ClosedInt) : low ≤ high → Interval constants
  deriving Repr, Inhabited, DecidableEq

@[grind]
instance(cts: List Int): Bot (Interval cts) where bot := .empty
instance(cts: List Int): EmptyCollection (Interval cts) where emptyCollection := .empty
instance(cts: List Int): Top (Interval cts) where top := .interval ⊥ ⊤ (by simp)

namespace Interval
variable {constants : List Int}
variable (x y z : Interval constants)

def mapEmpty (f : (low₁ low₂ : ClosedInt) → (high₁ high₂ : ClosedInt) →
                   low₁ ≤ high₁ → low₂ ≤ high₂ →
                   Interval constants)
              : Interval constants :=
  match x, y with
  | .empty, _ | _, .empty => .empty
  | .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ => f l₁ l₂ h₁ h₂ o₁ o₂

def add : Interval constants :=
  mapEmpty x y <| fun l₁ l₂ h₁ h₂ o₁ o₂ =>
    .interval (l₁ + l₂) (h₁ + h₂) <| by grind
    -- apply HLe.add_monotone <;> assumption

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
    .interval (ClosedInt.subLH l₁ h₂) (ClosedInt.subHL h₁ l₂)
      <| by apply HLe.sub_monotone <;> assumption

instance : Sub (Interval constants) where
  sub := sub

def bot : Interval constants := .empty

def top : Interval constants := .interval ⊥ ⊤ <| by constructor

def join : Interval constants := match x, y with
| .empty, z | z, .empty => z
| .interval l₁ h₁ o₁, .interval l₂ h₂ o₂ =>
  .interval (min l₁ l₂) (max h₁ h₂) <| by apply HLe.min_max_monotone <;> assumption

instance: Max (Interval constants) where
  max := join

def meet : Interval constants := match x, y with
| .empty, _ | _, .empty => .empty
| .interval l₁ h₁ _, .interval l₂ h₂ _ =>
  if h : max l₁ l₂ ≤ min h₁ h₂
  then .interval (max l₁ l₂) (min h₁ h₂) h
  else .empty

instance: Min (Interval constants) where
  min := meet

theorem join_commutative : x ⊔ y = y ⊔ x :=
by
  dsimp [Max.max]
  cases x <;> cases y <;> simp [join]
  apply And.intro
  · apply ClosedInt.min_comm
  · apply ClosedInt.max_comm

theorem join_associative : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
by
  dsimp [Max.max]
  cases x <;> cases y <;> cases z <;> dsimp [join]
  simp [min, max, ClosedInt.min_assoc, ClosedInt.max_assoc]

theorem join_absorption : x ⊔ (x ⊓ y) = x :=
by
  dsimp [Max.max, Min.min]
  cases x <;> cases y <;> dsimp [join, meet]
  rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
  by_cases h : max l₁ l₂ ≤ min h₁ h₂
  · rw [dif_pos h]
    dsimp
    simp [min, max, ClosedInt.min_max_absorb, ClosedInt.max_min_absorb]
  · rw [dif_neg h]

theorem join_bot : x ⊔ ⊥ = x :=
by
  dsimp [Max.max, Bot.bot]
  cases x <;> dsimp [bot, join]

theorem join_top : x ⊔ ⊤ = ⊤ :=
by
  dsimp [Max.max, Top.top]
  cases x <;> dsimp [join]
  simp [min, max, ClosedInt.min⊥, ClosedInt.max⊤]

theorem meet_commutative : x ⊓ y = y ⊓ x :=
by
  dsimp [Min.min]
  cases x <;> cases y <;> simp [meet]
  split <;> split <;> try dsimp
  · simp [min, max, ClosedInt.max_comm, ClosedInt.min_comm]
  all_goals try next hyp₁ hyp₂ =>
    exfalso
    simp [min, max] at hyp₁
    simp [min, max] at hyp₂
    rw [ClosedInt.max_comm, ClosedInt.min_comm] at hyp₁
    solve | exact (hyp₁ hyp₂) | exact (hyp₂ hyp₁)

theorem meet_associative :
  (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by
  dsimp [Min.min]
  cases x <;> cases y <;> cases z <;> simp [meet]
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    by_cases h : max l₁ l₂ ≤ min h₁ h₂
    · rw [dif_pos h]
    · rw [dif_neg h]
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂ l₃ h₃ hyp₃
    by_cases h : max l₁ l₂ ≤ min h₁ h₂
    · rw [dif_pos h] ; dsimp
      by_cases h' : max l₂ l₃ ≤ min h₂ h₃
      · rw [dif_pos h'] ; dsimp
        simp [min, max, ClosedInt.max_assoc, ClosedInt.min_assoc]
      · rw [dif_neg h'] ; rw [dif_neg]
        intro H
        apply h'
        apply And.right
        apply HLe.min_min_max_max
        apply H
    · rw [dif_neg h] ; dsimp
      by_cases h' : max l₂ l₃ ≤ min h₂ h₃
      · rw [dif_pos h'] ; dsimp; rw [dif_neg]
        intro H
        apply h
        apply And.left
        apply HLe.min_min_max_max
        simp [min, max]
        rw [ClosedInt.max_assoc, ClosedInt.min_assoc]
        apply H
      · rw [dif_neg h']

theorem meet_absorption : x ⊓ (x ⊔ y) = x :=
by
  dsimp [Min.min, Max.max]
  cases x <;> cases y <;> dsimp [join, meet]
  · rename_i l₁ h₁ hyp₁
    rw [dif_pos] <;> simp [max, min, ClosedInt.max_refl, ClosedInt.min_refl]
    assumption
  · rename_i l₁ h₁ hyp₁ l₂ h₂ hyp₂
    simp [min, max, ClosedInt.max_min_absorb, ClosedInt.min_max_absorb]
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
  grind [ClosedInt.max_def, ClosedInt.min_def, IntLow.min_def, ClosedInt.max_def]


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
  have cond: xₗ ⊔ yₗ ≤ xₕ ⊓ yₕ  := by
    -- Basically, we prove this by putting `zₗ` and `zₕ` in between
    have lhs: xₗ ⊔ yₗ ≤ zₗ := by grind [ClosedInt.max_def]
    have rhs: zₕ ≤ xₕ ⊓ yₕ := by grind [ClosedInt.min_def]
    apply HLe.hle_le_trans lhs zy rhs
  grind [ClosedInt.min_def, ClosedInt.min_def, IntLow.max_def, ClosedInt.max_def]


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
    x.meet (.interval ⊥ (0) <| by constructor),
    x.meet (.interval (0) ⊤ <| by constructor),
  )

def mulNegNeg : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match ClosedInt.mulHH h₁ h₂, ClosedInt.mulLL l₁ l₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤ h
  then .interval l h hyp
  else .empty

def mulNegPos : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match ClosedInt.mulLH l₁ h₂, ClosedInt.mulHL h₁ l₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤ h
  then .interval l h hyp
  else .empty

def mulPosPos : Interval constants := mapEmpty x y
fun l₁ l₂ h₁ h₂ _ _ =>
match ClosedInt.mulLL l₁ l₂, ClosedInt.mulHH h₁ h₂ with
| .none, _
| _, .none => .empty
| .some l, .some h => if hyp : l ≤ h
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
| _, 0 => .bot
| ⊤, _ => .interval (0) ⊤ <| by constructor
| _, ⊤ => .interval (0) (0) <| by constructor ; simp
| n, m => if hyp : 0 ≤ n / m
  then .interval (0) ((n / m)) <| by constructor ; assumption
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

def extractMaxGt (l : List Int) (h : ClosedInt) : IntLow :=
  match l with
  | [] => ⊥
  | m :: l => if ClosedInt.Le h (m) -- if h <= m
      then extractMaxGt l h
      else max (m) (extractMaxGt l h)

def extractMaxGtCorrect : ∀ (l : List Int) (n : ClosedInt),
  ClosedInt.Le (extractMaxGt l n) n :=
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
      · dsimp [max, ClosedInt.max]
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

def extractMinGe (l : List Int) (h : ClosedInt) : Close:=
  match l with
  | [] => ⊤
  | m :: l => if ClosedInt.Le (m) h -- if m <= h
      then extractMinGe l h
      else min (m) (extractMinGe l h)

def extractMinGeCorrect : ∀ (l : List Int) (h : ClosedInt),
  ClosedInt.Le h (extractMinGe l h) :=
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
      · dsimp [min, ClosedInt.min]
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
    let l := if ClosedInt.Le l₁ l₂
      then l₁
      else extractMaxGt constants l₂
    let h := if ClosedInt.Le h₂ h₁
      then h₁
      else extractMinGe constants h₂
    .interval l h <| by
      dsimp [l, h]
      apply HLe.HLe_Le
      · by_cases hl : ClosedInt.Le l₁ l₂ <;> simp [hl]
        · assumption
        · apply extractMaxGtCorrect constants l₂
      · by_cases hr : ClosedInt.Le h₂ h₁ <;> simp [hr]
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
  -- case⊥ =>
  --   by_cases h : n ≤ 10 <;> simp [h, join] <;>
  --   simp
  --   sorry
  by_cases this: n ≤ 10 <;> simp [this, join] <;>
  rcases y with _ | ⟨l, h, hle⟩ <;> simp [max, min, *]
  · simp [ClosedInt.max_min_absorb, ClosedInt.min_max_absorb, *]
  · split <;> split <;> try simp
    · assumption
    · have hyph : h'.Le h := by
        cases (ClosedInt.Le_total h' h)
        · assumption
        · contradiction
      have hyph' : h'.min (extractMinGe constants h) = h' := by
        apply ClosedInt.min_eq_left
        apply ClosedInt.Le_trans
        · assumption
        · apply extractMinGeCorrect
      simpa [hyph']
    · have hypl : l.Le l' := by
        cases (ClosedInt.Le_total l l')
        · assumption
        · contradiction
      have hypl' : l'.max (extractMaxGt constants l) = l' := by
        apply ClosedInt.max_eq_left
        apply ClosedInt.Le_trans
        · apply extractMaxGtCorrect
        · assumption
      simpa [hypl']
    · have hypl : l.Le l' := by
        cases (ClosedInt.Le_total l l')
        · assumption
        · contradiction
      have hypl' : l'.max (extractMaxGt constants l) = l' := by
        apply ClosedInt.max_eq_left
        apply ClosedInt.Le_trans
        · apply extractMaxGtCorrect
        · assumption
      have hyph : h'.Le h := by
        cases (ClosedInt.Le_total h' h)
        · assumption
        · contradiction
      have hyph' : h'.min (extractMinGe constants h) = h' := by
        apply ClosedInt.min_eq_left
        apply ClosedInt.Le_trans
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
      ClosedInt.max_min_absorb, IntLow.min_comm l,
      ClosedInt.min_max_absorb, ClosedInt.max_comm h,
      hle']
  · have hypl : l' = l'.max (extractMaxGt constants l') := by
        rw [ClosedInt.max_eq_left]
        apply extractMaxGtCorrect
    have hyph : h' = h'.min (extractMinGe constants h') := by
        rw [ClosedInt.min_eq_left]
        apply extractMinGeCorrect
    split <;> split <;> rename_i hyp' hyp <;>
    simp only [Max.max, ClosedInt.max_eq_left, hyp',
                        ClosedInt.min_eq_left, hyp,
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
        if hyp₁ : l₁ ≤ h
        then .interval l₁ h hyp₁
        else .empty,
        if hyp₂ : l ≤ h₂
        then .interval l h₂ hyp₂
        else .empty
      )
    | .lt =>
      let one := .interval (1) (1) <| by simp
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
      then .interval (x) (y) <| by constructor; assumption
      else .empty
    | .none, .some y => .interval ⊥ (y) <| by constructor
    | .some x, .none => .interval (x) ⊤ <| by constructor
    | .none, .none => .interval ⊥ ⊤ <| by constructor
  compare := compare

  -- TODO: pourquoi ça n'infère pas ??
  covering_left := WidenLawful.covering_left
  covering_right := WidenLawful.covering_right

  bounding_low := NarrowLawful.bounding_low
  bounding_high := NarrowLawful.bounding_high
end Interval
end Lustrean
