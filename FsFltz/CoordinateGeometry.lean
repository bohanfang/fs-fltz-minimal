import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Pointwise linear algebra for the ambient primitive

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 74–86. Complex vectors
represent real tangent coordinates `δu + i δθ`. This file proves the rank-one
positivity calculation. Identification with differential forms on the quotient
manifold, and smoothness of that identification, remain separate bridges.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace FsFltz.CoordinateGeometry

variable {n : ℕ}

/-- The complex-linear covector with coefficients `G`. -/
def evaluation (G q : Fin n → ℂ) : ℂ := ∑ j, G j * q j

/-- The usual complex structure in real logarithmic coordinates. -/
def complexStructure (q : Fin n → ℂ) : Fin n → ℂ := fun j => Complex.I * q j

/-- The pointwise expression for `dλ₀ + K W*(dx ∧ dy)`. -/
def omega (G : Fin n → ℂ) (K : ℝ) (q r : Fin n → ℂ) : ℝ :=
  (∑ j, conj (q j) * r j).im + K * (conj (evaluation G q) * evaluation G r).im

theorem evaluation_complexStructure (G q : Fin n → ℂ) :
    evaluation G (complexStructure q) = Complex.I * evaluation G q := by
  simp only [evaluation, complexStructure, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The two summands are respectively the Euclidean norm squared and the
nonnegative holomorphic pullback contribution in source lines 83–85. -/
theorem omega_complexStructure (G q : Fin n → ℂ) (K : ℝ) :
    omega G K q (complexStructure q) =
      (∑ j, Complex.normSq (q j)) + K * Complex.normSq (evaluation G q) := by
  have hi (z : ℂ) : (conj z * (Complex.I * z)).im = Complex.normSq z := by
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
  rw [omega, evaluation_complexStructure, hi]
  congr 1
  change Complex.imAddGroupHom (∑ j, conj (q j) * (Complex.I * q j)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => hi (q j))

theorem omega_complexStructure_pos (G q : Fin n → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hq : q ≠ 0) : 0 < omega G K q (complexStructure q) := by
  rw [omega_complexStructure]
  have he : ∃ j, q j ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  obtain ⟨j, hj⟩ := he
  have hs : 0 < ∑ k, Complex.normSq (q k) :=
    Finset.sum_pos' (fun k _ => Complex.normSq_nonneg (q k))
      ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩
  exact add_pos_of_pos_of_nonneg hs (mul_nonneg hK (Complex.normSq_nonneg _))

/-- Pointwise nondegeneracy, without a nonzero-dimension assumption. -/
theorem omega_nondegenerate (G q : Fin n → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hq : ∀ r, omega G K q r = 0) : q = 0 := by
  by_contra h
  have hp := omega_complexStructure_pos G q hK h
  rw [hq] at hp
  exact (lt_irrefl 0) hp

/-- The squared norm of the logarithmic derivative. -/
def derivativeNormSq (G : Fin n → ℂ) : ℝ := ∑ j, Complex.normSq (G j)

/-- The complex coordinate solution of the Liouville equation. -/
def liouville (G u : Fin n → ℂ) (W : ℂ) (K : ℝ) : Fin n → ℂ :=
  fun j => u j + (K / (1 + K * derivativeNormSq G) : ℝ) *
    conj (G j) * (W / 2 - evaluation G u)

theorem liouville_denominator_pos (G : Fin n → ℂ) {K : ℝ} (hK : 0 ≤ K) :
    0 < 1 + K * derivativeNormSq G := by
  have ha : 0 ≤ derivativeNormSq G :=
    Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (G j))
  positivity

theorem evaluation_liouville (G u : Fin n → ℂ) (W : ℂ) (K : ℝ) :
    evaluation G (liouville G u W K) = evaluation G u +
      (K / (1 + K * derivativeNormSq G) : ℝ) *
        (derivativeNormSq G : ℂ) * (W / 2 - evaluation G u) := by
  simp only [evaluation, liouville, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [derivativeNormSq, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.mul_conj]
  ring

/-- This identity is the rank-one linear system equivalent to contraction with
the pointwise form. Positivity ensures that its prescribed denominator is nonzero. -/
theorem liouville_linear_system (G u : Fin n → ℂ) (W : ℂ) {K : ℝ}
    (hK : 0 ≤ K) (j : Fin n) :
    liouville G u W K j + (K : ℂ) * conj (G j) *
      evaluation G (liouville G u W K) = u j + (K : ℂ) / 2 * W * conj (G j) := by
  rw [evaluation_liouville, liouville]
  have hd : (1 : ℂ) + (K : ℂ) * derivativeNormSq G ≠ 0 := by
    exact_mod_cast (ne_of_gt (liouville_denominator_pos G hK))
  push_cast
  field_simp
  ring

/-- The pointwise primitive; the intended vector `u` has real coordinates. -/
def primitive (G u : Fin n → ℂ) (W : ℂ) (K : ℝ) (r : Fin n → ℂ) : ℝ :=
  (∑ j, conj (u j) * r j).im + K / 2 * (conj W * evaluation G r).im

theorem omega_eq_linear_system (G q r : Fin n → ℂ) (K : ℝ) :
    omega G K q r =
      (∑ j, conj (q j + (K : ℂ) * conj (G j) * evaluation G q) * r j).im := by
  have he : (∑ j, conj (q j + (K : ℂ) * conj (G j) * evaluation G q) * r j) =
      (∑ j, conj (q j) * r j) + (K : ℂ) * conj (evaluation G q) * evaluation G r := by
    simp only [map_add, map_mul, Complex.conj_ofReal, starRingEnd_self_apply,
      add_mul, Finset.sum_add_distrib]
    congr 1
    simp only [evaluation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp [omega, Complex.mul_im, Complex.mul_re]
  ring

/-- The explicit vector satisfies the actual pointwise contraction equation. -/
theorem omega_liouville (G u : Fin n → ℂ) (W : ℂ) {K : ℝ} (hK : 0 ≤ K)
    (r : Fin n → ℂ) : omega G K (liouville G u W K) r = primitive G u W K r := by
  rw [omega_eq_linear_system]
  simp_rw [liouville_linear_system G u W hK]
  have he : (∑ j, conj (u j + (K : ℂ) / 2 * W * conj (G j)) * r j) =
      (∑ j, conj (u j) * r j) + ((K : ℂ) / 2) * conj W * evaluation G r := by
    simp only [map_add, map_mul, map_div₀, map_ofNat, Complex.conj_ofReal,
      starRingEnd_self_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    simp only [evaluation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp [primitive, Complex.mul_im, Complex.mul_re, div_eq_mul_inv]
  ring

end FsFltz.CoordinateGeometry
