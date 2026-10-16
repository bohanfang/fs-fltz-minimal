import FsFltz.Geometry.LocalCovers
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# Actual integral curves in logarithmic covering coordinates

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1625–1658.
The local lift is constructed from the smooth covering inverse. The field
identity is the one supplied for the actual intrinsic projected field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- Lift an actual native integral curve, retaining its prescribed initial
logarithmic representative and the equation with the original quotient curve. -/
theorem exists_logarithmic_integralCurve_lift {n d : ℕ}
    (N : SmoothManifold d) (j : N.SmoothMap (lgManifold n))
    (Z : (a : N.Point) → N.Tangent a) (V : TangentCoordinates n → TangentCoordinates n)
    (hpush : ∀ (a : N.Point) (x : TangentCoordinates n), j a = lgCover x →
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j a (Z a) = lgCoverTangent x (V x))
    {γ : ℝ → N.Point} {t₀ : ℝ} (hγ : IsMIntegralCurveAt γ Z t₀)
    (x : TangentCoordinates n) (hx : j (γ t₀) = lgCover x) :
    ∃ ξ : ℝ → TangentCoordinates n, ξ t₀ = x ∧
      IsMIntegralCurveAt (I := 𝓘(ℝ, TangentCoordinates n)) ξ (fun z => V z) t₀ ∧
      ∀ᶠ t in 𝓝 t₀, lgCover (ξ t) = j (γ t) := by
  let l := isLocalDiffeomorph_lgCover n x
  let ξ : ℝ → TangentCoordinates n := fun t => l.localInverse (j (γ t))
  have hsource : ∀ᶠ t in 𝓝 t₀, j (γ t) ∈ l.localInverse.source :=
    (j.contMDiff.continuous.continuousAt.comp hγ.continuousAt).tendsto.eventually
      (l.localInverse.open_source.mem_nhds (by
        change j (γ t₀) ∈ l.localInverse.source
        rw [hx]
        exact l.localInverse_mem_source))
  have hξpoint : ξ t₀ = x := by
    dsimp [ξ]
    rw [hx]
    exact l.localInverse_left_inv l.localInverse_mem_target
  refine ⟨ξ, hξpoint, ?_, ?_⟩
  · filter_upwards [hγ, hsource] with t ht hs
    have hl := l.localInverse.contMDiffOn.contMDiffAt
      (l.localInverse.open_source.mem_nhds hs)
    have hj := j.contMDiff.mdifferentiableAt (by simp) (x := γ t)
    have hξder := (hl.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hj.hasMFDerivAt.comp t ht)
    apply hξder.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, TangentCoordinates n)
      l.localInverse (j (γ t))
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j (γ t) (r • Z (γ t))) =
      r • V (ξ t)
    rw [map_smul, map_smul, hpush (γ t) (ξ t) (l.localInverse_right_inv hs).symm]
    congr 1
    have htarget : ξ t ∈ l.localInverse.target := l.localInverse.map_source hs
    have he : l.localInverse ∘ lgCover =ᶠ[𝓝 (ξ t)] id :=
      Filter.eventuallyEq_of_mem (l.localInverse.open_target.mem_nhds htarget)
        l.localInverse_eqOn_left
    have hd := mfderiv_comp (ξ t)
      (show MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, TangentCoordinates n)
        l.localInverse (lgCover (ξ t)) from
        (l.localInverse_right_inv hs).symm ▸ hl.mdifferentiableAt (by simp))
      ((contMDiff_lgCover n).mdifferentiableAt (by simp))
    rw [he.mfderiv_eq, mfderiv_id] at hd
    have hv := congrArg (fun L => L (V (ξ t))) hd
    change V (ξ t) = mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, TangentCoordinates n)
      l.localInverse (lgCover (ξ t)) (lgCoverTangent (ξ t) (V (ξ t))) at hv
    rw [l.localInverse_right_inv hs] at hv
    exact hv.symm
  · filter_upwards [hsource] with t ht
    exact l.localInverse_right_inv ht

end FsFltz.Geometry
