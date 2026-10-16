import FsFltz.Analysis.TailoringCriticalToriImplicit

/-!
# The radial scale of the reduced critical branch

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1526–1527.
Differentiability of the reduced solution gives the quantitative bounded
displacement at the original large-radius scale. Application to a toric
face uses the actual constrained-minimum map, constructed separately.
-/

noncomputable section

namespace FsFltz

open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rescaling a differentiable curve at zero yields a bounded displacement
from its leading linear radial term. -/
theorem eventually_bounded_radial_displacement_of_differentiableAt
    {f : ℝ → E} (hf : DifferentiableAt ℝ f 0) :
    ∃ C > 0, ∀ᶠ β : ℝ in atTop, ‖β • f β⁻¹ - β • f 0‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hf.isBigO_sub.exists_pos
  refine ⟨C, hC, ?_⟩
  have hb := tendsto_inv_atTop_zero.eventually hbound.bound
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with β hβ hpos
  simp only [sub_zero] at hβ
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  calc
    β * ‖f β⁻¹ - f 0‖ ≤ β * (C * ‖β⁻¹‖) :=
      mul_le_mul_of_nonneg_left hβ hpos.le
    _ = C := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      field_simp

variable {ι : Type*} [Fintype ι]

/-- The logarithmic parameter in the actual reduced equations remains
differentiable at the positive base solution. -/
theorem differentiableAt_critical_logarithmic_parameter
    {q : ℝ → (ι → ℝ)} (hq : DifferentiableAt ℝ q 0)
    (hpositive : ∀ i, 0 < q 0 i) :
    DifferentiableAt ℝ (fun ε : ℝ => ε • (fun i => Real.log (q ε i))) 0 := by
  apply differentiableAt_id.fun_smul
  apply differentiableAt_pi.mpr
  intro i
  exact (differentiableAt_pi.mp hq i).log (hpositive i).ne'

/-- The source's `u = β x_F + O(1)` conclusion, once the actual smooth
affine minimizer and positive reduced weights have been constructed. -/
theorem critical_radial_displacement
    {x : (ι → ℝ) → E} (hx : DifferentiableAt ℝ x 0)
    {q : ℝ → (ι → ℝ)} (hq : DifferentiableAt ℝ q 0)
    (hpositive : ∀ i, 0 < q 0 i) :
    (∃ C > 0, ∀ᶠ β : ℝ in atTop,
      ‖β • x (β⁻¹ • (fun i => Real.log (q β⁻¹ i))) - β • x 0‖ ≤ C) ∧
    Tendsto (fun β : ℝ => x (β⁻¹ • (fun i => Real.log (q β⁻¹ i))))
      atTop (𝓝 (x 0)) := by
  have hg := differentiableAt_critical_logarithmic_parameter hq hpositive
  have hf : DifferentiableAt ℝ
      (fun ε : ℝ => x (ε • (fun i => Real.log (q ε i)))) 0 := by
    apply DifferentiableAt.comp 0 _ hg
    simpa using hx
  constructor
  · simpa using eventually_bounded_radial_displacement_of_differentiableAt hf
  · simpa only [Function.comp_def, zero_smul] using
      hf.continuousAt.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))

end FsFltz
