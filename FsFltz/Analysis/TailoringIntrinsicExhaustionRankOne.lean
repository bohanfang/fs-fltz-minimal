import FsFltz.Analysis.TailoringIntrinsicExhaustion
import FsFltz.Analysis.PotentialPathRankOne

/-!
# The entire bounded-value tailored end is empty in rank one

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1221–1227.
The normalized holomorphic metric defect vanishes identically in rank one,
contradicting the positive defect supplied by the actual bounded-value
tailoring end estimate. This covers every value of modulus at most two.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set
open scoped ContDiff Manifold

/-- In rank one the whole actual bounded-value tailored end is empty,
uniformly in the homotopy parameter, without assuming any fiber nonempty. -/
theorem tailoringFamily_exists_uniform_whole_end_empty_rankOne
    (I : ToricInput 1) {φ φEnd : RealSpace 1 → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin 1), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin 1) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin 1),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin 1) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(EuclideanSpace.equiv (Fin 1) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        {y : LGSpace 1 |
          F * β ≤ Real.sqrt (metricRadialSq
            (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1)) y.1) ∧
          ‖tailoringFamily I β s y‖ ≤ 2} = ∅ := by
  obtain ⟨F, hF, _C, _hC, β₀, hβ₀, hdata⟩ :=
    tailoringFamily_exists_uniform_whole_end_exhaustion_data
      I hφ hc hU hlower hupper hEnd hhom hREnd heq
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ s hs
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := lgCover_surjective 1 y
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  obtain ⟨ha, hdefect, _hπ, _hout, _hnorm⟩ :=
    hdata β hβ s hs x hy.1 hy.2 hnd
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  have hrad : 0 < metricRadialSq H x.1 := Real.sqrt_pos.mp
    ((mul_pos hF (hβ₀.trans_le hβ)).trans_le hy.1)
  have hzero := potentialMetricFiberDefect_eq_zero_rankOne H
    (tailoringNormalizedInput I β) (lgCover x) ha.ne'
  change 3 / 4 * metricRadialSq H x.1 ≤
    potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x) at hdefect
  rw [hzero] at hdefect
  linarith only [hrad, hdefect]

end FsFltz
