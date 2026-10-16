import FsFltz.Geometry.Smooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Form pullbacks and chart calculus

The primitive-preserving maps in `def:pair` and `def:chain` of
`geoemtric-part-fsf.tex`, lines 144–145 and 175–189, use actual differentials.
This file proves their pullback calculus. It is foundation work for the bridges
in `sec:lean`, lines 805–814, and asserts no comparison-chain existence.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.SmoothManifold

/-- Pullback composition is the manifold chain rule, including the derivative
at every tangent fiber. -/
theorem pullback_comp {d e f k : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (P : SmoothManifold f) {u : M.Point → N.Point} {v : N.Point → P.Point}
    (hu : MDifferentiable (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) u)
    (hv : MDifferentiable (𝓘(ℝ, Model e)) (𝓘(ℝ, Model f)) v) (eta : P.Form k) :
    M.pullback P (v ∘ u) eta = M.pullback N u (N.pullback P v eta) := by
  funext x
  unfold pullback
  rw [mfderiv_comp x (hv (u x)) (hu x)]
  ext vs
  rfl

@[simp] theorem pullback_id {d k : ℕ} (M : SmoothManifold d) (eta : M.Form k) :
    M.pullback M id eta = eta := by
  funext x
  unfold pullback
  rw [mfderiv_id]
  ext vs
  rfl

/-- The differential of a chart and its inverse cancel on its source, so
chart coefficients recover the actual intrinsic form. -/
theorem formInChart_comp_chartTangentMap {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (a x : M.Point) (hx : x ∈ (chartAt (Model d) a).source) :
    (M.formInChart a eta (chartAt (Model d) a x)).compContinuousLinearMap
      (M.chartTangentMap a x) = eta x := by
  unfold formInChart chartTangentMap
  rw [(chartAt (Model d) a).left_inv hx]
  have h := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  apply ContinuousAlternatingMap.ext
  intro vs
  change eta x (fun i =>
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a).symm
      (chartAt (Model d) a x))
        ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a) x) (vs i))) =
    eta x vs
  apply congrArg (eta x)
  funext i
  exact congrArg (fun L => L (vs i)) h

/-- In overlapping source and target charts, the coefficients of an intrinsic
pullback are the Euclidean pullback by the coordinate expression of the map.
This supplies the representation needed to apply `extDeriv_pullback`. -/
theorem formInChart_pullback {d e k : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    {f : M.Point → N.Point} (eta : N.Form k) (a : M.Point) (b : N.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target)
    (hb : f ((chartAt (Model d) a).symm y) ∈ (chartAt (Model e) b).source)
    (hf : MDifferentiableAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f
      ((chartAt (Model d) a).symm y)) :
    M.formInChart a (M.pullback N f eta) y =
      (N.formInChart b eta
        (chartAt (Model e) b (f ((chartAt (Model d) a).symm y)))).compContinuousLinearMap
        (fderiv ℝ (chartAt (Model e) b ∘ f ∘ (chartAt (Model d) a).symm) y) := by
  rw [← mfderiv_eq_fderiv]
  have hca := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy
  have hcb := (mdifferentiable_chart (I := 𝓘(ℝ, Model e)) b).mdifferentiableAt hb
  have hchain := mfderiv_comp y hcb (hf.comp y hca)
  rw [hchain, mfderiv_comp y hf hca]
  unfold formInChart pullback
  rw [(chartAt (Model e) b).left_inv hb]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model e)) b).symm_comp_deriv hb
  apply ContinuousAlternatingMap.ext
  intro vs
  change eta (f ((chartAt (Model d) a).symm y))
    (fun i => (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f ((chartAt (Model d) a).symm y))
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a).symm y) (vs i))) = _
  apply congrArg (eta (f ((chartAt (Model d) a).symm y)))
  funext i
  exact (congrArg (fun L => L
    ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f ((chartAt (Model d) a).symm y))
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) a).symm y) (vs i))))
    hinv).symm

@[simp] theorem pullback_symm_pullback {d e k : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (u : M.SmoothEquiv N) (eta : N.Form k) :
    N.pullback M u.symm (M.pullback N u eta) = eta := by
  rw [← pullback_comp N M N
    (u.symm.contMDiff.mdifferentiable (by simp))
    (u.contMDiff.mdifferentiable (by simp))]
  have hu : (u ∘ u.symm : N.Point → N.Point) = id := by
    funext x
    exact u.apply_symm_apply x
  rw [hu, pullback_id]

end FsFltz.Geometry.SmoothManifold
