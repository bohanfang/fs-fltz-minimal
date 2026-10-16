import FsFltz.Analysis.TailoringPoissonPositivity
import FsFltz.Analysis.PotentialPathMargin

/-!
# The quantitative margin after scalar normalization

Source: `geometric-part-fsf-proof.tex`, `lem:margin`, lines 746–768,
and `subsec:finite`, lines 1182–1197. The constants and exceptional radius
are chosen before the normalization parameter. This is the holomorphic
margin used to absorb the tailored exhaustion error on a finite band.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

theorem W_tailoringNormalizedInput_scale (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    W (tailoringNormalizedInput I β) y =
      (Real.exp (-β) : ℂ) * W (I.alongCoefficientPath 1) y := by
  simp only [W, tailoringNormalizedInput, ToricInput.alongCoefficientPath_one_coeff,
    Finset.mul_sum, monomial, one_mul, mul_assoc]
  rfl

theorem b0_tailoringNormalizedInput (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    b0 (tailoringNormalizedInput I β) y =
      (Real.exp (-β) : ℂ) * b0 (I.alongCoefficientPath 1) y := by
  simp only [b0, G_tailoringNormalizedInput, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every term in the actual margin scales by the square of the positive
normalization scalar. -/
theorem potentialMetricMargin_tailoringNormalizedInput
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    potentialMetricMargin H (tailoringNormalizedInput I β) y =
      Real.exp (-β) ^ 2 * potentialMetricMargin H (I.alongCoefficientPath 1) y := by
  simp only [potentialMetricMargin, toricInverseMetricSq_tailoringNormalizedInput,
    b0_tailoringNormalizedInput, W_tailoringNormalizedInput_scale,
    Complex.normSq_ofReal, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

/-- The normalized endpoint polynomial has the same positive quantitative
margin outside one fixed cylinder, for every real normalization parameter. -/
theorem tailoringNormalizedInput_uniform_metric_margin
    (I : ToricInput n) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ q : ℝ, 0 < q ∧ ∃ L : ℝ, 0 < L ∧ ∀ β : ℝ, ∀ y : LGSpace n,
      L ≤ Real.sqrt (realSquaredNorm y.1) →
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        (∀ v, inner ℝ (H v) v ≤ C * ‖v‖ ^ 2) →
        0 < toricInverseMetricSq H (tailoringNormalizedInput I β) y ∧
          q * Real.sqrt (metricRadialSq H y.1) *
            Real.exp (supportHeight I y.1 - β) ^ 2 ≤
              potentialMetricMargin H (tailoringNormalizedInput I β) y := by
  obtain ⟨q, hq, L, hL, hm⟩ := I.coefficientPath_metric_quantitative_ambient_margin hc hC
  refine ⟨q, hq, L, hL, ?_⟩
  intro β y hy H hsymm hlower hupper
  obtain ⟨ha, hmargin⟩ := hm 1 (by simp) y hy H hsymm hlower hupper
  rw [toricInverseMetricSq_tailoringNormalizedInput, potentialMetricMargin_tailoringNormalizedInput]
  refine ⟨mul_pos (sq_pos_of_pos (Real.exp_pos _)) ha, ?_⟩
  rw [maxMonomialMagnitude_coefficientOne] at hmargin
  have he : Real.exp (supportHeight I y.1 - β) =
      Real.exp (-β) * Real.exp (supportHeight I y.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  convert mul_le_mul_of_nonneg_left hmargin (sq_nonneg (Real.exp (-β))) using 1
  ring

end FsFltz
