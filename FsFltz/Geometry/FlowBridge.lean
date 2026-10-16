import FsFltz.Geometry.LiouvilleNaturality
import FsFltz.Geometry.VectorFieldBridge
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Native integral curves of the completed Liouville flow

The coordinate flow equation is connected to Mathlib's actual manifold ODE.
This is the flow foundation requested in `geoemtric-part-fsf.tex`,
`def:chain`, lines 183–189, and `sec:lean`, lines 805–814.
-/

noncomputable section
open scoped Manifold ContDiff
open Topology

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate ODE in every chart is equivalent to the native manifold
integral-curve equation for a differentiable curve. -/
theorem isMIntegralCurve_iff_chart_solves {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (γ : ℝ → M.Point)
    (hγ : MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ) :
    IsMIntegralCurve γ Z ↔ ∀ (t : ℝ) (a : M.Point),
      γ t ∈ (chartAt (Model d) a).source →
      HasDerivAt (fun s => chartAt (Model d) a (γ s))
        (M.chartTangentMap a (γ t) (Z (γ t))) t := by
  constructor
  · intro h t a ha
    have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt ha
    have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
      (hc.hasMFDerivAt.comp t (h t))).hasDerivAt
    apply hd.congr_deriv
    change M.chartTangentMap a (γ t) ((1 : ℝ) • Z (γ t)) = _
    rw [one_smul]
  · intro h t
    let a := γ t
    have ha : γ t ∈ (chartAt (Model d) a).source := mem_chart_source _ _
    have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt ha
    have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
      (hc.hasMFDerivAt.comp t (hγ t).hasMFDerivAt)).hasDerivAt
    have he : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t (1 : ℝ) = Z (γ t) := by
      apply (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mfderiv_bijective ha |>.injective
      exact hd.unique (h t a ha)
    apply (hγ t).hasMFDerivAt.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    rw [show r = r • (1 : ℝ) by simp, map_smul, he]
    change r • Z (γ t) = (r * 1) • Z (γ t)
    rw [mul_one]

theorem CompleteLiouvilleFlow.contMDiff_orbit {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z) (x : M.Point) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) ∞ (fun t => F.flow t x) :=
  F.smooth_action.comp (contMDiff_id.prodMk contMDiff_const)

/-- Every all-real-time orbit in a bundled completed flow is a native integral
curve of its specified vector field. -/
theorem CompleteLiouvilleFlow.isMIntegralCurve {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z) (x : M.Point) :
    IsMIntegralCurve (fun t => F.flow t x) Z :=
  (isMIntegralCurve_iff_chart_solves M Z _
    ((F.contMDiff_orbit x).mdifferentiable (by simp))).mpr (F.solves x)

set_option backward.isDefEq.respectTransparency false in
/-- Primitive preservation forces equivariance of the actual complete flows.
Native integral-curve uniqueness applies to the transported source orbit
and target orbit, with field smoothness already bundled in the target. -/
theorem CompleteLiouvilleManifold.map_flow {d e : ℕ}
    (X : CompleteLiouvilleManifold d) (Y : CompleteLiouvilleManifold e)
    (f : X.manifold.SmoothEquiv Y.manifold)
    (hprimitive : X.manifold.pullback Y.manifold f Y.primitive = X.primitive)
    (x : X.manifold.Point) (t : ℝ) :
    f (X.completeFlow.flow t x) = Y.completeFlow.flow t (f x) := by
  have hleft : IsMIntegralCurve (fun s => f (X.completeFlow.flow s x)) Y.field := by
    intro s
    have h := ((f.contMDiff.mdifferentiable (by simp))
      (X.completeFlow.flow s x)).hasMFDerivAt.comp s (X.completeFlow.isMIntegralCurve x s)
    apply h.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (X.completeFlow.flow s x)
      (r • X.field (X.completeFlow.flow s x)) = r • Y.field (f (X.completeFlow.flow s x))
    rw [map_smul, X.map_field Y f hprimitive]
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (Y.smooth_field.contMDiff_section.of_le (by simp)) hleft
    (Y.completeFlow.isMIntegralCurve (f x)) (by simp only [Flow.map_zero_apply])
  exact congrFun heq t

/-- The strict ambient map of a permitted completion identification
intertwines the same all-real-time flows that define its completions. -/
theorem CompletionIdentification.map_flow {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (x : P.ambientCompletion.ambient.manifold.Point)
    (t : ℝ) :
    h.ambientEquiv (P.ambientCompletion.ambient.completeFlow.flow t x) =
      Q.ambientCompletion.ambient.completeFlow.flow t (h.ambientEquiv x) :=
  P.ambientCompletion.ambient.map_flow Q.ambientCompletion.ambient
    h.ambientEquiv h.primitive x t

end FsFltz.Geometry
