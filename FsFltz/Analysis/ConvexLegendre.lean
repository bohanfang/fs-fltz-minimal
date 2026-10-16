import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniformly positive Hessians and the global Legendre map

The analytic global-inverse argument used in `lem:potential` of
`geometric-part-fsf-proof.tex`, lines 631–642. The geometric construction
of the compatible potential is a separate producer.
-/

noncomputable section

open Function Set
open scoped Topology ContDiff

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrating a uniform lower bound for the symmetric part of the derivative
along a segment gives strong monotonicity. -/
theorem mul_norm_sq_le_inner_sub_of_uniform_derivative {g : E → E} {c : ℝ}
    (hg : Differentiable ℝ g)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v)
    (x y : E) :
    c * ‖y - x‖ ^ 2 ≤ inner ℝ (g y - g x) (y - x) := by
  let v := y - x
  let f : ℝ → ℝ := fun t => inner ℝ (g (x + t • v)) v
  have hd (t : ℝ) : HasDerivAt f (inner ℝ ((fderiv ℝ g (x + t • v)) v) v) t := by
    have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v |>.const_add x
    have hgp := (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t hp
    simpa [f] using hgp.inner ℝ (hasDerivAt_const t v)
  have hle := mul_sub_le_image_sub_of_le_deriv (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; exact hbound _ _) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa [f, v, inner_sub_left] using hle

/-- The inverse of a uniformly strongly monotone map has Lipschitz constant
at most the reciprocal of the derivative lower bound. -/
theorem norm_sub_le_of_uniform_derivative {g : E → E} {c : ℝ}
    (hg : Differentiable ℝ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v)
    (x y : E) : ‖y - x‖ ≤ c⁻¹ * ‖g y - g x‖ := by
  have hle := mul_norm_sq_le_inner_sub_of_uniform_derivative hg hbound x y
  have hi : inner ℝ (g y - g x) (y - x) ≤ ‖g y - g x‖ * ‖y - x‖ :=
    (le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (g y - g x) (y - x)))
  by_cases hzero : y - x = 0
  · simp [sub_eq_zero.mp hzero]
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr hzero
  have hmul : c * ‖y - x‖ ≤ ‖g y - g x‖ := by nlinarith
  exact (le_inv_mul_iff₀ hc).mpr hmul

/-- A uniform positive derivative bound gives a global quantitative embedding. -/
theorem antilipschitz_of_uniform_derivative {g : E → E} {c : ℝ}
    (hg : Differentiable ℝ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) :
    AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ g := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist x y ≤ c⁻¹ * dist (g x) (g y)
  simpa [dist_eq_norm] using norm_sub_le_of_uniform_derivative hg hc hbound y x

/-- The same bound makes every derivative injective. -/
theorem fderiv_injective_of_uniform_derivative {g : E → E} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) (x : E) :
    Injective (fderiv ℝ g x) := by
  intro v w hvw
  have hv : (fderiv ℝ g x) (v - w) = 0 := by simp [map_sub, hvw]
  have hb := hbound x (v - w)
  rw [hv, inner_zero_left] at hb
  have hn : ‖v - w‖ = 0 := by
    by_contra h
    have := mul_pos hc (sq_pos_of_ne_zero h)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [FiniteDimensional ℝ E]

/-- In finite dimension the positive derivative is a continuous linear equivalence. -/
def derivativeEquivOfUniformPositive {g : E → E} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) (x : E) :
    E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (fderiv ℝ g x).toLinearMap
    ⟨fderiv_injective_of_uniform_derivative hc hbound x,
      (fderiv ℝ g x).toLinearMap.surjective_of_injective
        (fderiv_injective_of_uniform_derivative hc hbound x)⟩).toContinuousLinearEquiv

@[simp]
theorem derivativeEquivOfUniformPositive_coe {g : E → E} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) (x : E) :
    (derivativeEquivOfUniformPositive hc hbound x : E →L[ℝ] E) = fderiv ℝ g x := by
  ext v
  rfl

/-- The inverse function theorem makes a smooth map with uniformly positive
derivative an open map. -/
theorem isOpenMap_of_uniform_derivative {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) : IsOpenMap g := by
  apply isOpenMap_of_hasStrictFDerivAt_equiv
    (f' := derivativeEquivOfUniformPositive hc hbound)
  intro x
  rw [derivativeEquivOfUniformPositive_coe]
  exact hg.contDiffAt.hasStrictFDerivAt' ((hg.differentiable (by simp)) x).hasFDerivAt
    (by simp)

/-- A smooth uniformly strongly monotone map on a finite-dimensional real
inner-product space is bijective. No global inverse is assumed. -/
theorem bijective_of_uniform_derivative {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) : Bijective g := by
  have ha := antilipschitz_of_uniform_derivative (hg.differentiable (by simp)) hc hbound
  have hp : IsProperMap g := isProperMap_iff_tendsto_cocompact.mpr
    ⟨hg.continuous, by simpa only [Metric.cobounded_eq_cocompact] using ha.tendsto_cobounded⟩
  have ho := isOpenMap_of_uniform_derivative hg hc hbound
  have hr : range g = univ :=
    IsClopen.eq_univ ⟨hp.isClosed_range, ho.isOpen_range⟩ (range_nonempty g)
  exact ⟨ha.injective, range_eq_univ.mp hr⟩

/-- The global homeomorphism of a smooth map with uniformly positive derivative. -/
def homeomorphOfUniformPositiveDerivative {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) : E ≃ₜ E :=
  (Equiv.ofBijective g (bijective_of_uniform_derivative hg hc hbound)).toHomeomorphOfContinuousOpen
    hg.continuous (isOpenMap_of_uniform_derivative hg hc hbound)

@[simp]
theorem homeomorphOfUniformPositiveDerivative_apply {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) (x : E) :
    homeomorphOfUniformPositiveDerivative hg hc hbound x = g x := rfl

@[simp]
theorem homeomorphOfUniformPositiveDerivative_coe {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) :
    (homeomorphOfUniformPositiveDerivative hg hc hbound : E → E) = g := rfl

/-- The global inverse is smooth, by the inverse function theorem. -/
theorem contDiff_symm_homeomorphOfUniformPositiveDerivative {g : E → E} {c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ g x) v) v) :
    ContDiff ℝ ∞ (homeomorphOfUniformPositiveDerivative hg hc hbound).symm := by
  apply Homeomorph.contDiff_symm (f₀' := derivativeEquivOfUniformPositive hc hbound)
  · intro x
    simpa using ((hg.differentiable (by simp)) x).hasFDerivAt
  · exact hg

variable [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- The actual Riesz gradient of a smooth real-valued function is smooth. -/
theorem contDiff_gradient {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_infty_iff_fderiv.mp hφ).2

/-- A smooth function with a uniform positive Hessian has a bijective gradient. -/
theorem bijective_gradient_of_uniform_hessian {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) :
    Bijective (gradient φ) :=
  bijective_of_uniform_derivative (contDiff_gradient hφ) hc hbound

/-- The global Legendre map, with forward map literally equal to `gradient φ`. -/
def gradientHomeomorph {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) : E ≃ₜ E :=
  homeomorphOfUniformPositiveDerivative (contDiff_gradient hφ) hc hbound

@[simp]
theorem gradientHomeomorph_apply {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) (x : E) :
    gradientHomeomorph hφ hc hbound x = gradient φ x := rfl

/-- Smoothness of the inverse Legendre map. -/
theorem contDiff_symm_gradientHomeomorph {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) :
    ContDiff ℝ ∞ (gradientHomeomorph hφ hc hbound).symm :=
  contDiff_symm_homeomorphOfUniformPositiveDerivative (contDiff_gradient hφ) hc hbound

end FsFltz
