import FsFltz.Geometry.IntrinsicShrinkingPairMotion

/-!
# Actual variable-time Liouville pullback

Source: `geometric-part-fsf-proof.tex`, `eq:hittingprimitive`, lines 1847–1852.
The differential of a variable-time map includes the time derivative. The
Liouville contraction equation makes its primitive evaluation vanish.
No immersion, hitting-time identity, or supplied pullback identity is assumed.
This generic complete-flow result does not identify a separate regional action
with an actual completed ambient flow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
namespace CompleteLiouvilleManifold

/-- The variable-time derivative has a spatial-flow term and a Liouville
vector term. The primitive kills the latter, yielding exact exponential
scaling for every source tangent. Only differentiability at this point is used. -/
theorem evalOne_pullback_variableTime_at {d e : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold e) (j : N.Point → X.manifold.Point) (τ : N.Point → ℝ)
    (x : N.Point) (hj : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j x)
    (hτ : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x) (v : N.Tangent x) :
    evalOne (N.pullback X.manifold (fun y => X.completeFlow.flow (τ y) (j y)) X.primitive) x v =
      Real.exp (τ x) * evalOne (N.pullback X.manifold j X.primitive) x v := by
  let F : ℝ × X.manifold.Point → X.manifold.Point := fun p => X.completeFlow.flow p.1 p.2
  have hF : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d)
      F (τ x, j x) := X.completeFlow.smooth_action.mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply (f := fun y => (τ y, j y)) (g := F) x hF (hτ.prodMk hj) v
  rw [mfderiv_prodMk hτ hj] at hc
  change mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d)
      (fun y => X.completeFlow.flow (τ y) (j y)) x v =
    mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d)
      F (τ x, j x)
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x v,
        mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j x v) at hc
  rw [mfderiv_prod_eq_add_apply hF,
    (X.completeFlow.isMIntegralCurve (j x) (τ x)).mfderiv] at hc
  change mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d)
      (fun y => X.completeFlow.flow (τ y) (j y)) x v =
    (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x v) • X.field (X.completeFlow.flow (τ x) (j x)) +
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (fun z => X.completeFlow.flow (τ x) z) (j x)
        (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j x v) at hc
  have hzero : evalOne X.primitive (X.completeFlow.flow (τ x) (j x))
      (X.field (X.completeFlow.flow (τ x) (j x))) = 0 :=
    X.manifold.evalOne_eq_zero_of_liouvilleEquation X.primitive _ _ (X.contraction _)
  change evalOne X.primitive (X.completeFlow.flow (τ x) (j x))
    (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d)
      (fun y => X.completeFlow.flow (τ y) (j y)) x v) = _
  rw [hc, evalOne_add, evalOne_smul, hzero, mul_zero, zero_add]
  have hp := congrFun (X.pullback_timeDiffeomorph (τ x)) (j x)
  have hv := congrArg (fun α => α (fun _ : Fin 1 =>
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j x v)) hp
  exact hv

/-- The actual one-form identity for a variable-time map, locally at any
point where its source map and time function are differentiable. -/
theorem pullback_variableTime_at {d e : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold e) (j : N.Point → X.manifold.Point) (τ : N.Point → ℝ)
    (x : N.Point) (hj : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j x)
    (hτ : MDifferentiableAt 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) τ x) :
    N.pullback X.manifold (fun y => X.completeFlow.flow (τ y) (j y)) X.primitive x =
      Real.exp (τ x) • N.pullback X.manifold j X.primitive x := by
  ext vs
  have hv : vs = fun _ : Fin 1 => vs 0 := by
    funext i
    exact congrArg vs (Subsingleton.elim i 0)
  rw [hv]
  exact X.evalOne_pullback_variableTime_at N j τ x hj hτ (vs 0)

/-- Global smooth source and time maps give the same exact primitive law
everywhere, with no immersion or regular-level hypothesis. -/
theorem pullback_variableTime {d e : ℕ} (X : CompleteLiouvilleManifold d)
    (N : SmoothManifold e) (j : N.Point → X.manifold.Point) (τ : N.Point → ℝ)
    (hj : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) ∞ j)
    (hτ : ContMDiff 𝓘(ℝ, Model e) 𝓘(ℝ, ℝ) ∞ τ) :
    N.pullback X.manifold (fun y => X.completeFlow.flow (τ y) (j y)) X.primitive =
      fun x => Real.exp (τ x) • N.pullback X.manifold j X.primitive x := by
  funext x
  exact X.pullback_variableTime_at N j τ x
    (hj.mdifferentiableAt (by simp)) (hτ.mdifferentiableAt (by simp))

end CompleteLiouvilleManifold
end FsFltz.Geometry
