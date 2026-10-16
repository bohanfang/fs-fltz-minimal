import FsFltz.Analysis.PotentialExtension
import FsFltz.Analysis.ConvexLegendre

/-!
# Hessian lower bounds retained by potential extension

The common quadratic convexity correction in `PotentialExtension` implies
the actual Hessian bound used by the global Legendre theorem. This supplies
the positivity step in `geometric-part-fsf-proof.tex`, `lem:potential`,
lines 626–635, by restriction to affine lines.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Convexity after subtracting a quadratic gives the corresponding pointwise
lower bound on the actual derivative of the Riesz gradient. -/
theorem hessian_lowerBound_of_differentiable_convex_sub_quadratic {f : E → ℝ} {c : ℝ}
    (hf : Differentiable ℝ f)
    (hconv : ConvexOn ℝ univ (fun x => f x - c * ‖x‖ ^ 2)) (x v : E)
    (hgrad : DifferentiableAt ℝ (gradient f) x) :
    (2 * c) * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient f) x) v) v := by
  let p : ℝ → E := fun t => x + t • v
  let l : ℝ → ℝ := fun t => f (p t) - c * ‖p t‖ ^ 2
  let dl : ℝ → ℝ := fun t => inner ℝ (gradient f (p t)) v -
    c * (2 * inner ℝ (p t) v)
  have hp (t : ℝ) : HasDerivAt p v t := by
    simpa [p] using ((hasDerivAt_id t).smul_const v).const_add x
  have hd (t : ℝ) : HasDerivAt l (dl t) t := by
    have hfg := (hf (p t)).hasGradientAt.hasFDerivAt
    convert (hfg.comp_hasDerivAt t (hp t)).sub ((hp t).norm_sq.const_mul c) using 1
    · rfl
    · simp [dl]
  have hlconv : ConvexOn ℝ univ l := by
    refine ⟨convex_univ, ?_⟩
    intro t _ s _ a b ha hb hab
    have hpab : p (a • t + b • s) = a • p t + b • p s := by
      dsimp [p]
      calc
        x + (a * t + b * s) • v = (a + b) • x + (a * t + b * s) • v := by
          rw [hab, one_smul]
        _ = a • (x + t • v) + b • (x + s • v) := by module
    change f (p (a • t + b • s)) - c * ‖p (a • t + b • s)‖ ^ 2 ≤ _
    rw [hpab]
    exact hconv.2 (mem_univ (p t)) (mem_univ (p s)) ha hb hab
  have hmon : Monotone dl := by
    have h := monotoneOn_univ.mp (hlconv.monotoneOn_deriv (fun t _ => (hd t).differentiableAt))
    have he : deriv l = dl := funext fun t => (hd t).deriv
    rwa [he] at h
  have hg0 : DifferentiableAt ℝ (gradient f) (p 0) := by simpa [p] using hgrad
  have hdg := hg0.hasFDerivAt.comp_hasDerivAt 0 (hp 0)
  have hddl : HasDerivAt dl
      (inner ℝ ((fderiv ℝ (gradient f) x) v) v - (2 * c) * ‖v‖ ^ 2) 0 := by
    have h := (hdg.inner ℝ (hasDerivAt_const 0 v)).sub
      (((hp 0).inner ℝ (hasDerivAt_const 0 v)).const_mul 2 |>.const_mul c)
    convert h using 1
    · rfl
    · simp [p, mul_assoc, mul_left_comm]
  exact sub_nonneg.mp (hddl.nonneg_of_monotone hmon)

/-- Global smoothness supplies the pointwise derivative hypotheses of the
preceding lower-bound theorem. -/
theorem hessian_lowerBound_of_convex_sub_quadratic {f : E → ℝ} {c : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hconv : ConvexOn ℝ univ (fun x => f x - c * ‖x‖ ^ 2)) (x v : E) :
    (2 * c) * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient f) x) v) v :=
  hessian_lowerBound_of_differentiable_convex_sub_quadratic
    (hf.differentiable (by simp)) hconv x v
    ((contDiff_gradient hf).differentiable (by simp) x)

/-- The smooth-max extension has a uniformly positive actual Hessian and a
global smooth Legendre inverse when the retained correction is positive. -/
theorem exists_smooth_extension_with_legendre [FiniteDimensional ℝ E]
    {f : E → ℝ} {a c d : ℝ} (hc : 0 < c) (hca : c ≤ a) (had : a < d)
    (hf : Continuous f) (hf0 : f 0 = 0)
    (hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x)
    (hconv : ConvexOn ℝ univ (fun x => f x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, d * ‖x‖ ^ 2 ≤ f x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x v, (2 * c) * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient g) x) v) v) ∧
      (∀ᶠ x in 𝓝 (0 : E), g x = a * ‖x‖ ^ 2 + 1) ∧
      (∃ R > 0, ∀ x, R ≤ ‖x‖ → g x = f x) ∧
      ∃ e : E ≃ₜ E, (∀ x, e x = gradient g x) ∧ ContDiff ℝ ∞ e.symm := by
  obtain ⟨g, hgs, hgconv, hg0, hgend⟩ :=
    PotentialExtension.exists_smooth_extension hca had hf hf0 hfs hconv hlower
  have hbound := hessian_lowerBound_of_convex_sub_quadratic hgs hgconv
  refine ⟨g, hgs, hbound, hg0, hgend, gradientHomeomorph hgs (by positivity) hbound,
    fun _ => rfl, ?_⟩
  exact contDiff_symm_gradientHomeomorph hgs (by positivity) hbound

end FsFltz
