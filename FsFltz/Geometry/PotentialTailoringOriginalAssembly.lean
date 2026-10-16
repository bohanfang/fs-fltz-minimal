import FsFltz.Geometry.PotentialTailoringOriginalChain
import FsFltz.Analysis.OriginalRounding
import FsFltz.Analysis.PotentialPathFiberBounds
import FsFltz.Analysis.PotentialPathThreshold

/-!
# Finite-input original-K, holomorphic and tailoring marked prefix

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 770–795,
`lem:markedfamily`, lines 975–1049, and assembly, lines 2148–2158.
The original fiber bound at the literal logarithmic level is obtained by
specializing the same retained potential path at its quadratic endpoint.
The common rounding width is then proved for both actual original and
holomorphic-tailoring constructions, rather than assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The quadratic endpoint of the actual potential interpolation supplies
the original strict fiber end bound at its literal logarithmic level. -/
theorem ToricInput.exists_original_logarithmic_fiberEndBound
    (I : ToricInput n) {φ φEnd : EuclideanSpace ℝ (Fin n) → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient φ) x v) v)
    (hupper : ∀ x v, inner ℝ (fderiv ℝ (gradient φ) x v) v ≤ U * ‖v‖ ^ 2)
    {L : ℝ} (hL : 0 < L) (hend : ∀ x, L ≤ ‖x‖ → φ x = φEnd x) (Aamb : ℝ) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      FiberEndBound I Aamb (Real.exp β) (F ^ 2 * β ^ 2 / 2) := by
  obtain ⟨F, hF, β₀, hβ₀, hbound⟩ :=
    I.coefficientPath_potentialPath_logarithmic_potential_level
      hφ hEnd1 hEnd hhom hc hlower hupper hL hend Aamb
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨hlevel, hb⟩ := hbound β hβ
  refine ⟨hlevel, ?_⟩
  intro y hy hW
  have hn : ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ ^ 2 = realSquaredNorm y.1 := by
    simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hq : (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2) (WithLp.toLp 2 y.1) = phi0 y := by
    simp only [hn, phi0]
  have hy' : F ^ 2 * β ^ 2 / 2 ≤
      potentialPath (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2) φ 0 (WithLp.toLp 2 y.1) := by
    simpa only [potentialPath_zero, hq] using hy
  obtain ⟨_hend, ha, hdef⟩ := hb 0 (by simp) 0 (by simp) y hy'
    (by simpa only [I.alongCoefficientPath_zero] using hW)
  simp only [potentialPathHessianEquiv_zero, I.alongCoefficientPath_zero,
    toricInverseMetricSq_refl] at ha hdef
  have hdef' : phi0 y ≤ realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y := by
    simpa only [potentialPath_zero, hq, phi0, potentialMetricFiberDefect, metricRadialSq,
      ContinuousLinearEquiv.refl_apply, real_inner_self_eq_norm_sq, hn,
      toricInverseMetricSq_refl] using hdef
  have hpos : 0 < F ^ 2 * β ^ 2 / 2 :=
    div_pos (mul_pos (sq_pos_of_pos hF) (sq_pos_of_pos (hβ₀.trans_le hβ))) (by norm_num)
  exact ⟨ha, (hpos.trans_le hy).trans_le hdef'⟩

end FsFltz
