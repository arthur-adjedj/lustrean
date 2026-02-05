import Lustrean.Domain.Interval.Defs
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Int.SuccPred
import Mathlib.Order.SuccPred.Archimedean

/- Extra operations on Set needed to define the abstraction
   function of sets as intervals. In particular, we need to
   be able to pick the minimum and maximum elements in a
   set, if they exist, and otherwise return ⊥ or ⊤
   respectively. These functions are implemented as Set.min?
   and Set.max?

   We require Classical, both functions are noncomputable.
-/
namespace Set

/- Couldn't find a better definition for this.
   See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/The.20minimum.20of.20a.20.60Set.60.20if.20it.20exists.20else.20.60bot.60/with/570279925-/
open Classical in
noncomputable
def min?{α: Type}[PartialOrder α](s: Set α)(_nonempty: s ≠ ∅ ): WithBot α :=
  if h : ∃ (x: α), IsLeast s x then
    (Classical.choose h: α)
  else
    ⊥

-- TODO: Maybe this can be done through SupSet and InfSet notations?
-- I think I can exploit that Int is a CompleteLattice to derive
-- instances of CompleteSemilatticeSup for WithTop (resp. Inf for Bot),
-- and redefine
--     max? as ⨆ (WithTop.some '' s)
--     min? as ⨅ (WithBot.some '' s)
-- May be worth looking into once the proofs are done, or if they become
-- more complicated than expected.

notation "⨅₂" s:max => Set.min? s (by grind)

open Classical in
noncomputable
def max?{α: Type}[PartialOrder α](s: Set α)(_nonempty: s ≠ ∅): WithTop α :=
  if h : ∃ (x: α), IsGreatest s x then
    (Classical.choose h: α)
  else
    ⊤

notation "⨆₂" s:max => Set.max? s (by grind)

theorem min?_hle_max?(s: Set Int)(h: s ≠ ∅): ⨅₂ s ≤∘ ⨆₂ s
:= by
  dsimp only [Set.min?, Set.max?]
  split
  case isTrue hasMin =>
    have ⟨min_in_s, min_lb⟩ := Classical.choose_spec hasMin
    split
    case isTrue hasMax =>
      have ⟨max_in_s, max_ub⟩ := Classical.choose_spec hasMax
      apply min_lb; assumption
    case isFalse =>
      apply WithBot.hle_top
  case isFalse =>
    apply WithBot.bot_hle

theorem min?_le_of_mem{s: Set Int}(h: s ≠ ∅): ∀ x ∈ s, ⨅₂ s ≤ x
:= by
  intros x x_S
  dsimp only [Set.min?]
  split
  case isTrue h =>
    have ⟨inS, bound⟩ := Classical.choose_spec h
    simp only [WithBot.coe_le_coe]
    apply bound x_S
  case isFalse => apply bot_le

theorem le_max?_of_mem(s: Set Int)(h: s ≠ ∅): ∀ x ∈ s, x ≤ ⨆₂ s
:= by
  intros x x_S
  dsimp only [Set.max?]
  split
  case isTrue h =>
    have ⟨inS, bound⟩ := Classical.choose_spec h
    simp only [WithTop.coe_le_coe]
    apply bound x_S
  case isFalse => apply le_top

theorem le_min?(s: Set Int)(nonempty: s ≠ ∅)
: ∀ (x: Int), x ≤ ⨅₂ s ↔ (∀ z ∈ s, x ≤ z)
:= by
  intros x
  constructor <;> intros hyp
  · intros z z_s
    apply WithBot.coe_le_coe.mp
    calc x ≤ ⨅₂ s := by assumption
         _ ≤ z := by apply s.min?_le_of_mem <;> assumption
  · have bd: BddBelow s := by
      simp only [BddBelow,lowerBounds,Set.Nonempty,Set.mem_setOf_eq]
      exists x
    have h := bd.exists_isLeast_of_nonempty (by grind only [Set.nonempty_iff_empty_ne])
    unfold Set.min?
    simp only [h, reduceDIte, WithBot.coe_le_coe]
    apply hyp
    have ⟨_, _⟩ := Classical.choose_spec h
    assumption

theorem max?_le(s: Set Int)(nonempty: s ≠ ∅)
: ∀ (x: Int), ⨆₂ s ≤ x ↔ (∀ z ∈ s, z ≤ x)
:= by
  intros x
  constructor <;> intros hyp
  · intros z z_s
    apply WithTop.coe_le_coe.mp
    calc z ≤ ⨆₂ s := by apply s.le_max?_of_mem <;> assumption
         _ ≤ x := by assumption
  · have bd: BddAbove s := by
      simp only [BddAbove,upperBounds,Set.Nonempty,Set.mem_setOf_eq]
      exists x
    have h := bd.exists_isGreatest_of_nonempty (by grind only [Set.nonempty_iff_empty_ne])
    unfold Set.max?
    simp only [h, reduceDIte, WithTop.coe_le_coe]
    apply hyp
    have ⟨_, _⟩ := Classical.choose_spec h
    assumption

theorem le_min?_of_mem(s: Set Int)(h: s ≠ ∅): ∀ x ∈ s, x = ⨅₂ s ↔ x ≤ ⨅₂ s
:= by
  intros x x_S
  dsimp only [Set.min?]
  split <;> simp only [WithBot.coe_le_coe, WithBot.coe_inj, le_bot_iff, WithBot.coe_ne_bot]
  rename_i hasMin
  have ⟨min_in_s, min_lb⟩ := Classical.choose_spec hasMin
  specialize min_lb x_S
  grind only

theorem max?_le_of_mem(s: Set Int)(h: s ≠ ∅): ∀ x ∈ s, x = ⨆₂ s ↔ ⨆₂ s ≤ x
:= by
  intros x x_S
  dsimp only [Set.max?]
  split <;> simp only [WithTop.coe_le_coe, WithTop.coe_inj, top_le_iff]
  rename_i hasMin
  have ⟨min_in_s, min_lb⟩ := Classical.choose_spec hasMin
  specialize min_lb x_S
  grind only

theorem bdd_of_le_min?(s: Set Int)(h: s ≠ ∅)(e: Int)
: e ≤ (⨅₂ s) → BddBelow s
:= by
  intros hyp
  simp only [BddBelow,lowerBounds,Set.Nonempty,Set.mem_setOf_eq]
  exists e
  intros x x_s
  apply WithBot.coe_le_coe.mp
  calc e ≤ ⨅₂ s := by assumption
       _ ≤ x    := by apply Set.min?_le_of_mem <;> assumption

theorem bdd_of_max?_le(s: Set Int)(h: s ≠ ∅)(e: Int)
: (⨆₂ s) ≤ e → BddAbove s
:= by
  intros hyp
  simp only [BddAbove,upperBounds,Set.Nonempty,Set.mem_setOf_eq]
  exists e
  intros x x_s
  apply WithTop.coe_le_coe.mp
  calc x ≤ ⨆₂ s := by apply Set.le_max?_of_mem <;> assumption
       _ ≤ e    := by assumption

end Set

namespace Lustrean

namespace Interval

def concrete: Interval → Set Int
| ⊥ => ∅
| .mk l h .. => {x : Int | l ≤ x ∧ x ≤ h}

open Classical in
noncomputable
def abstract(s: Set Int): Interval :=
  if cond: s = ∅ then
    ⊥
  else
    mk (⨅₂ s) (⨆₂ s) (s.min?_hle_max? cond)

attribute [simp] WithBot.coe_le_coe WithTop.coe_le_coe

def gc: GaloisConnection abstract concrete := by
  intros s x
  if nonempty: s = ∅ then
    subst s
    simp only [concrete, abstract, reduceDIte, bot_le, Set.le_eq_subset, Set.empty_subset]
  else
  match x with
  | ⊥ =>
    simp only [abstract, nonempty, ne_eq, ↓reduceDIte, mk, le_bot_iff, concrete,
      Set.le_eq_subset, Set.subset_empty_iff, iff_false]
    intros h
    simp only [WithBot.some, Bot.bot, reduceCtorEq] at h
  | .mk xl xh xinv =>
    simp only [abstract, nonempty, mk, concrete,
      Set.le_eq_subset, ↓reduceDIte, ]
    constructor <;> intros hyp
    · have ⟨xl_minS, maxS_xh⟩ := WithBot.coe_le_coe.mp hyp
      intros e e_S
      constructor
      · calc xl ≤ ⨅₂ s := by assumption
              _ ≤ e   := by apply Set.min?_le_of_mem <;> assumption
      · calc e ≤  ⨆₂ s := by apply Set.le_max?_of_mem <;> assumption
              _ ≤ xh  := by assumption
    · apply WithBot.coe_le_coe.mpr
      simp only [NonEmpty.mk_le_mk]
      constructor
      · match xl with
        | ⊥ => apply bot_le
        | (xl: Int) =>
          have ⟨l, l_S, l_eq⟩ : ∃ l ∈ s, l = ⨅₂ s := by
            fun_cases (⨅₂ s) <;> rename_i h
            · have ⟨e, h⟩ := Classical.choose_spec h
              simp only [WithBot.coe_inj, exists_eq_right, e]
            · exfalso
              rename_i h
              have : xl ≤ ⨅₂ s := by
                apply Set.le_min? s nonempty xl |>.mpr
                intros z z_s
                have ⟨xl_z, z_xh⟩ := hyp z_s
                apply WithBot.coe_le_coe.mp xl_z
              have := s.bdd_of_le_min? nonempty xl this
              have := this.exists_isLeast_of_nonempty (Set.nonempty_iff_ne_empty.mpr nonempty)
              grind
          have ⟨_,_⟩ := hyp l_S
          grind only
      · match xh with
        | ⊤ => apply le_top
        | (xh: Int) =>
          have ⟨l, l_S, l_eq⟩ : ∃ l ∈ s, l = ⨆₂ s := by
            fun_cases (⨆₂ s) <;> rename_i h
            · have ⟨e, h⟩ := Classical.choose_spec h
              simp only [WithTop.coe_inj, exists_eq_right, e]
            · exfalso
              rename_i h
              have : ⨆₂ s ≤ xh := by
                apply Set.max?_le s nonempty xh |>.mpr
                intros z z_s
                have ⟨xl_z, z_xh⟩ := hyp z_s
                apply WithTop.coe_le_coe.mp z_xh
              have := s.bdd_of_max?_le nonempty xh this
              have := this.exists_isGreatest_of_nonempty (Set.nonempty_iff_ne_empty.mpr nonempty)
              grind
          have ⟨_,_⟩ := hyp l_S
          -- TODO: Why grind doesn't close on its own? It should work by congruence
          -- Look into it
          rw [←l_eq]
          grind only

end Interval
