import FsFltz.Geometry.TailoringStrictJunctionGradingCompact
import FsFltz.Geometry.TailoringCompletedGradingFamily

/-!
# Literal native section agreement at the strict incoming parameter

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2025–2045,
and `subsec:junction`, lines 1891–1919. The last tailoring slice and the
first coefficient-removal slice use the same function, potential,
Hamiltonian vector and rank-two shear coefficient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The actual native tensor at tailoring parameter one is the actual
native tensor at the decreasing-coefficient family's parameter zero.
Both use the same retained potential and the same selected base coefficient. -/
theorem tailoringNativeMaslovFamily_tensor_one_eq_decreasing_zero {n : ℕ}
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK).tensor 1 =
      ((potentialMaslovRepresentative hφ hc hlower).decreasingRankTwoPrimitiveFamily
        (isSmoothForm_lambdaPotentialForm hφ)
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
        (tailoringFamily I β 1) (contMDiff_tailoringFamily_lgManifold I β 1)
        (hπ 1 ⟨zero_le_one, le_rfl⟩) K hK).tensor 0 := by
  funext y
  change rankTwoShearTensor _ _ K _ = rankTwoShearTensor _ _ (K * (1 - 0)) _
  simp only [sub_zero, mul_one]

end FsFltz
