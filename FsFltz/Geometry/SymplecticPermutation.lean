import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Option

/-!
# Signs of permutations of symplectic pairs

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–160,
and `sec:lean`, lines 783–814. In the signed permutation formula for a top
power of a standard alternating two-form, every nonzero summand permutes
matched pairs. The sign of such a permutation is the product of its
within-pair orientation signs.
-/

noncomputable section
open scoped BigOperators

namespace FsFltz.Geometry.SymplecticAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem pair_fst_eq (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) (i : α) (k : Fin 2) :
    (σ (i, k)).1 = (σ (i, 0)).1 := by
  fin_cases k
  · rfl
  · exact (hσ i).symm

/-- The permutation induced on the two slots of one matched pair. -/
def pairSlotPerm (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) (i : α) : Equiv.Perm (Fin 2) := by
  let s : Fin 2 → Fin 2 := fun k => (σ (i, k)).2
  have hs : Function.Injective s := by
    intro k l h
    have he : σ (i, k) = σ (i, l) :=
      Prod.ext ((pair_fst_eq σ hσ i k).trans (pair_fst_eq σ hσ i l).symm) h
    exact congrArg Prod.snd (σ.injective he)
  exact Equiv.ofBijective s ⟨hs, Finite.surjective_of_injective hs⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem pairSlotPerm_apply (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) (i : α) (k : Fin 2) :
    pairSlotPerm σ hσ i k = (σ (i, k)).2 := rfl

/-- The permutation induced on the matched-pair indices. -/
def pairIndexPerm (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) : Equiv.Perm α := by
  let p : α → α := fun i => (σ (i, 0)).1
  have hp : Function.Injective p := by
    intro i j hij
    let k := (pairSlotPerm σ hσ i).symm 0
    let l := (pairSlotPerm σ hσ j).symm 0
    have hk : (σ (i, k)).2 = 0 := (pairSlotPerm σ hσ i).apply_symm_apply 0
    have hl : (σ (j, l)).2 = 0 := (pairSlotPerm σ hσ j).apply_symm_apply 0
    have he : σ (i, k) = σ (j, l) := by
      apply Prod.ext
      · exact (pair_fst_eq σ hσ i k).trans (hij.trans (pair_fst_eq σ hσ j l).symm)
      · exact hk.trans hl.symm
    exact congrArg Prod.fst (σ.injective he)
  exact Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩

omit [DecidableEq α] in
@[simp] theorem pairIndexPerm_apply (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) (i : α) :
    pairIndexPerm σ hσ i = (σ (i, 0)).1 := rfl

omit [DecidableEq α] in
theorem pairedPerm_decomposition (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) :
    σ = (Equiv.prodCongrRight (pairSlotPerm σ hσ)).trans
      (Equiv.prodCongrLeft (fun _ : Fin 2 => pairIndexPerm σ hσ)) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · exact pair_fst_eq σ hσ p.1 p.2
  · rfl

/-- Permuting whole pairs is even; only the within-pair swaps contribute. -/
theorem sign_pairedPerm (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) :
    Equiv.Perm.sign σ = ∏ i, Equiv.Perm.sign (pairSlotPerm σ hσ i) := by
  conv_lhs => rw [pairedPerm_decomposition σ hσ]
  rw [Equiv.Perm.sign_trans,
    Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight,
    Fin.prod_univ_two, Int.units_mul_self, one_mul]

/-- The matrix coefficient of the standard alternating form on matched pairs. -/
def standardPairEntry (p q : α × Fin 2) : ℝ :=
  if p.1 = q.1 ∧ p.2 ≠ q.2 then (if p.2 = 0 then 1 else -1) else 0

theorem sign_finTwo (s : Equiv.Perm (Fin 2)) :
    (((Equiv.Perm.sign s : ℤˣ) : ℤ) : ℝ) = if s 0 = 0 then 1 else -1 := by
  have hn : s 0 ≠ s 1 := s.injective.ne (by decide)
  generalize hs0 : s 0 = a
  generalize hs1 : s 1 = b
  fin_cases a <;> fin_cases b
  · exact False.elim (hn (hs0.trans hs1.symm))
  · have he : s = Equiv.refl (Fin 2) := by
      ext k
      fin_cases k <;> simp [hs0, hs1]
    simp [he]
  · have he : s = Equiv.swap 0 1 := by
      ext k
      fin_cases k <;> simp [hs0, hs1]
    simp [he, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  · exact False.elim (hn (hs0.trans hs1.symm))

omit [Fintype α] in
theorem standardPairEntry_pairedPerm (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) (i : α) :
    standardPairEntry (σ (i, 0)) (σ (i, 1)) =
      (((Equiv.Perm.sign (pairSlotPerm σ hσ i) : ℤˣ) : ℤ) : ℝ) := by
  have hn : (σ (i, 0)).2 ≠ (σ (i, 1)).2 := by
    intro h
    have he := congrArg Prod.snd (σ.injective (Prod.ext (hσ i) h))
    exact (by decide : (0 : Fin 2) ≠ 1) he
  rw [standardPairEntry, ite_eq_left ⟨hσ i, hn⟩, sign_finTwo, pairSlotPerm_apply]

theorem prod_standardPairEntry_pairedPerm (σ : Equiv.Perm (α × Fin 2))
    (hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1) :
    (∏ i, standardPairEntry (σ (i, 0)) (σ (i, 1))) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) := by
  conv_rhs => rw [sign_pairedPerm σ hσ]
  simp [standardPairEntry_pairedPerm σ hσ]

/-- Every summand of the raw standard symplectic permutation volume is either
zero or one; the sign and the alternating pair orientations cancel exactly. -/
theorem standardPairTerm_eq_zero_or_one (σ : Equiv.Perm (α × Fin 2)) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) *
        (∏ i, standardPairEntry (σ (i, 0)) (σ (i, 1))) = 0 ∨
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) *
        (∏ i, standardPairEntry (σ (i, 0)) (σ (i, 1))) = 1 := by
  by_cases hσ : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1
  · right
    rw [prod_standardPairEntry_pairedPerm σ hσ, ← Int.cast_mul,
      Int.units_coe_mul_self, Int.cast_one]
  · left
    obtain ⟨i, hi⟩ := not_forall.mp hσ
    have he : standardPairEntry (σ (i, 0)) (σ (i, 1)) = 0 := by
      simp [standardPairEntry, hi]
    have hp : (∏ j, standardPairEntry (σ (j, 0)) (σ (j, 1))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) he
    rw [hp, mul_zero]

/-- The raw signed permutation sum for the standard symplectic top volume
is positive in every rank, including rank zero. No counting formula is needed. -/
theorem standardPairVolume_pos :
    0 < ∑ σ : Equiv.Perm (α × Fin 2),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) *
        ∏ i, standardPairEntry (σ (i, 0)) (σ (i, 1)) := by
  apply Finset.sum_pos'
  · intro σ _
    rcases standardPairTerm_eq_zero_or_one σ with h | h <;> rw [h]
    exact zero_le_one
  · refine ⟨Equiv.refl _, Finset.mem_univ _, ?_⟩
    simp [standardPairEntry]

/-- The distinguished contact covector in standard contact coordinates. -/
def standardContactCovector : Option (α × Fin 2) → ℝ
  | none => 1
  | some _ => 0

/-- Extend the standard symplectic coefficients by zero on the distinguished
contact direction. Only its values on pairs of kernel vectors will matter. -/
def standardContactEntry : Option (α × Fin 2) → Option (α × Fin 2) → ℝ
  | some p, some q => standardPairEntry p q
  | _, _ => 0

theorem standardContactTerm_eq_zero_or_one (σ : Equiv.Perm (Option (α × Fin 2))) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * standardContactCovector (σ none) *
        (∏ i, standardContactEntry (σ (some (i, 0))) (σ (some (i, 1)))) = 0 ∨
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * standardContactCovector (σ none) *
        (∏ i, standardContactEntry (σ (some (i, 0))) (σ (some (i, 1)))) = 1 := by
  by_cases hσ : σ none = none
  · have he : (Equiv.removeNone σ).optionCongr = σ := by
      simpa only [hσ, Equiv.swap_self, ← Equiv.Perm.one_def, one_mul] using
        map_equiv_removeNone σ
    rw [← he, Equiv.optionCongr_sign]
    simpa only [Equiv.optionCongr_apply, Option.map_none, Option.map_some,
      standardContactCovector, standardContactEntry, mul_one] using
      standardPairTerm_eq_zero_or_one (Equiv.removeNone σ)
  · left
    have hcov : standardContactCovector (σ none) = 0 := by
      cases hs : σ none with
      | none => exact False.elim (hσ hs)
      | some p => rfl
    rw [hcov, mul_zero, zero_mul]

/-- Positivity of the full standard raw contact permutation sum. -/
theorem standardContactVolume_pos :
    0 < ∑ σ : Equiv.Perm (Option (α × Fin 2)),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * standardContactCovector (σ none) *
        ∏ i, standardContactEntry (σ (some (i, 0))) (σ (some (i, 1))) := by
  apply Finset.sum_pos'
  · intro σ _
    rcases standardContactTerm_eq_zero_or_one σ with h | h <;> rw [h]
    exact zero_le_one
  · refine ⟨Equiv.refl _, Finset.mem_univ _, ?_⟩
    simp [standardContactCovector, standardContactEntry, standardPairEntry]

/-- A normalized contact covector and standard symplectic kernel coefficients
force positivity of the raw contact sum. Coefficients involving the contact
direction are unrestricted: their terms have zero covector factor. -/
theorem contactPermutationVolume_pos
    (a : Option (α × Fin 2) → ℝ)
    (b : Option (α × Fin 2) → Option (α × Fin 2) → ℝ)
    (ha : a none = 1) (ha' : ∀ p, a (some p) = 0)
    (hb : ∀ p q, b (some p) (some q) = standardPairEntry p q) :
    0 < ∑ σ : Equiv.Perm (Option (α × Fin 2)),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * a (σ none) *
        ∏ i, b (σ (some (i, 0))) (σ (some (i, 1))) := by
  have hterm (σ : Equiv.Perm (Option (α × Fin 2))) :
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * a (σ none) *
          (∏ i, b (σ (some (i, 0))) (σ (some (i, 1)))) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * standardContactCovector (σ none) *
          ∏ i, standardContactEntry (σ (some (i, 0))) (σ (some (i, 1))) := by
    by_cases hσ : σ none = none
    · have he : (Equiv.removeNone σ).optionCongr = σ := by
        simpa only [hσ, Equiv.swap_self, ← Equiv.Perm.one_def, one_mul] using
          map_equiv_removeNone σ
      rw [← he]
      simp only [Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        ha, hb, standardContactCovector, standardContactEntry]
    · have hcov : a (σ none) = 0 ∧ standardContactCovector (σ none) = 0 := by
        cases hs : σ none with
        | none => exact False.elim (hσ hs)
        | some p => exact ⟨ha' p, rfl⟩
      simp only [hcov.1, hcov.2, mul_zero, zero_mul]
  simpa only [hterm] using (standardContactVolume_pos (α := α))

end FsFltz.Geometry.SymplecticAlgebra
