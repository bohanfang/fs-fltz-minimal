import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Regularity of a squared Lipschitz gauge at the origin

A Lipschitz function vanishing at zero has a differentiable square at zero,
with zero derivative. If it is smooth away from zero, its square is globally
`C¹`. This is the origin-regularity step of `lem:potential` in
`geometric-part-fsf-proof.tex`, lines 636–639.
-/

noncomputable section

open Filter
open scoped Topology ContDiff NNReal

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quadratic vanishing gives a zero derivative, even when the unsquared
function itself is not differentiable at the origin. -/
theorem hasFDerivAt_sq_zero_of_lipschitz {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hf0 : f 0 = 0) :
    HasFDerivAt (fun x => f x ^ 2) (0 : E →L[ℝ] ℝ) (0 : E) := by
  have hbig : (fun x => f x ^ 2) =O[𝓝 (0 : E)] (fun x => ‖x - 0‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound ((C : ℝ) ^ 2)
    filter_upwards [] with x
    have hb : |f x| ≤ C * ‖x‖ := by simpa [hf0, Real.norm_eq_abs] using hf.norm_sub_le x 0
    have hc : 0 ≤ (C : ℝ) * ‖x‖ := mul_nonneg C.coe_nonneg (norm_nonneg x)
    simpa [Real.norm_eq_abs, abs_sq, sub_zero, pow_two, mul_assoc, mul_left_comm, mul_comm]
      using (sq_le_sq₀ (abs_nonneg (f x)) hc).mpr hb
  exact hbig.hasFDerivAt (by norm_num)

/-- Away from zero, the derivative of the square decays linearly in the
distance to zero; the estimate extends to zero by its zero derivative. -/
theorem norm_fderiv_sq_le_of_lipschitz {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hf0 : f 0 = 0)
    (hfd : ∀ x ≠ 0, DifferentiableAt ℝ f x) (x : E) :
    ‖fderiv ℝ (fun x => f x ^ 2) x‖ ≤ 2 * (C : ℝ) ^ 2 * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [(hasFDerivAt_sq_zero_of_lipschitz hf hf0).fderiv]
  have hdx := (hfd x hx).hasFDerivAt
  have hd : HasFDerivAt (fun x => f x ^ 2)
      (f x • fderiv ℝ f x + f x • fderiv ℝ f x) x := by
    simpa only [pow_two] using hdx.fun_mul hdx
  rw [hd.fderiv]
  have hb : |f x| ≤ C * ‖x‖ := by simpa [hf0, Real.norm_eq_abs] using hf.norm_sub_le x 0
  have hD := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
  calc
    ‖f x • fderiv ℝ f x + f x • fderiv ℝ f x‖ ≤
        ‖f x • fderiv ℝ f x‖ + ‖f x • fderiv ℝ f x‖ := norm_add_le _ _
    _ = 2 * |f x| * ‖fderiv ℝ f x‖ := by simp [norm_smul, Real.norm_eq_abs]; ring
    _ ≤ 2 * ((C : ℝ) * ‖x‖) * C := by gcongr
    _ = 2 * (C : ℝ) ^ 2 * ‖x‖ := by ring

/-- The square of a Lipschitz function vanishing at zero and smooth elsewhere
is globally `C¹`, including its actual origin derivative. -/
theorem contDiff_one_sq_of_lipschitz {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hf0 : f 0 = 0)
    (hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x) : ContDiff ℝ 1 (fun x => f x ^ 2) := by
  have hfd : ∀ x ≠ 0, DifferentiableAt ℝ f x := fun x hx =>
    (hfs x hx).differentiableAt (by simp)
  apply contDiff_one_iff_fderiv.mpr
  constructor
  · intro x
    by_cases hx : x = 0
    · subst x
      exact (hasFDerivAt_sq_zero_of_lipschitz hf hf0).differentiableAt
    · exact ((hfs x hx).pow 2).differentiableAt (by simp)
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      change Tendsto (fderiv ℝ (fun x => f x ^ 2)) (𝓝 0)
        (𝓝 (fderiv ℝ (fun x => f x ^ 2) 0))
      rw [(hasFDerivAt_sq_zero_of_lipschitz hf hf0).fderiv]
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [sub_zero]
      apply squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
        (Eventually.of_forall (norm_fderiv_sq_le_of_lipschitz hf hf0 hfd))
      simpa using ((continuous_norm : Continuous (norm : E → ℝ)).const_mul
        (2 * (C : ℝ) ^ 2)).tendsto (0 : E)
    · exact ((hfs x hx).pow 2).continuousAt_fderiv (by simp)

end FsFltz
