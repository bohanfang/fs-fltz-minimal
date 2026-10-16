import FsFltz.Analysis.PotentialMetricEstimates

/-!
# Operator bounds for the actual inverse Hessian

Source: `geometric-part-fsf-proof.tex`, `eq:rankerror`, lines 1137–1140.
The positive lower Hessian bound controls its actual inverse uniformly.
The immediate consumer is the Poisson-pairing perturbation estimate for the
literal tailoring family.
-/

noncomputable section

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coercivity controls the actual inverse on each vector. -/
theorem norm_inverse_apply_le_of_lowerBound (H : E ≃L[ℝ] E)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ v : E, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) (v : E) :
    ‖H.symm v‖ ≤ c⁻¹ * ‖v‖ := by
  have h := hlower (H.symm v)
  rw [H.apply_symm_apply] at h
  have hu := real_inner_le_norm v (H.symm v)
  by_cases hz : H.symm v = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg v)
  have hp := norm_pos_iff.mpr hz
  have hh : c * ‖H.symm v‖ ≤ ‖v‖ := by
    nlinarith
  calc
    ‖H.symm v‖ ≤ ‖v‖ / c := (le_div_iff₀ hc).mpr (by linarith)
    _ = c⁻¹ * ‖v‖ := by ring

/-- The positive lower quadratic bound bounds the inverse operator norm. -/
theorem norm_inverse_le_of_lowerBound (H : E ≃L[ℝ] E)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ v : E, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) :
    ‖H.symm.toContinuousLinearMap‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  exact norm_inverse_apply_le_of_lowerBound H hc hlower

/-- Instantiation for the constructed inverse of the actual potential Hessian. -/
theorem norm_potentialHessianEquiv_symm_le
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {φ : E → ℝ} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x v : E,
      c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) (x : E) :
    ‖(potentialHessianEquiv hc hlower x).symm.toContinuousLinearMap‖ ≤ c⁻¹ :=
  norm_inverse_le_of_lowerBound _ hc (hlower x)

end FsFltz
