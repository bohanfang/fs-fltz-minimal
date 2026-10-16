import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linearization of a local metric gradient at a zero

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott` and `lem:stable`,
lines 1538–1570 and 1709–1724. Differentiation of the actual gradient
identity removes the variable-metric term at a zero of the field.
-/

noncomputable section
open Filter
open scoped Topology
namespace FsFltz.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local gradient identity at a field zero gives the exact Hessian;
the derivative of the variable metric contributes zero. -/
theorem metric_gradient_linearization {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Z : E → E} {f : E → ℝ} {c : E}
    (hG : DifferentiableAt ℝ G c) (hZ : DifferentiableAt ℝ Z c)
    (hzero : Z c = 0)
    (hgrad : (fun z => G z (Z z)) =ᶠ[𝓝 c] fderiv ℝ f) (v w : E) :
    G c (fderiv ℝ Z c v) w = fderiv ℝ (fderiv ℝ f) c v w := by
  have he := hgrad.fderiv_eq (𝕜 := ℝ)
  rw [(hG.hasFDerivAt.clm_apply hZ.hasFDerivAt).fderiv] at he
  have hv := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) he
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hzero, map_zero, zero_add, add_zero] using hv

/-- Hessian symmetry implies metric selfadjointness of the actual field
derivative, without assuming a constant metric on a neighborhood. -/
theorem metric_gradient_linearization_selfadjoint
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Z : E → E} {f : E → ℝ} {c : E}
    (hG : DifferentiableAt ℝ G c) (hZ : DifferentiableAt ℝ Z c)
    (hzero : Z c = 0)
    (hgrad : (fun z => G z (Z z)) =ᶠ[𝓝 c] fderiv ℝ f)
    (hf : ContDiffAt ℝ 2 f c) (hmetric : ∀ v w, G c v w = G c w v)
    (v w : E) :
    G c (fderiv ℝ Z c v) w = G c v (fderiv ℝ Z c w) := by
  rw [metric_gradient_linearization hG hZ hzero hgrad,
    hmetric v (fderiv ℝ Z c w), metric_gradient_linearization hG hZ hzero hgrad]
  exact hf.isSymmSndFDerivAt (by simp) v w

end FsFltz.Geometry
