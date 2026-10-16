import FsFltz.Analysis.TailoringLyapunovGood
import FsFltz.Analysis.TailoringLyapunovCoordinates
import FsFltz.Geometry.GradientLinearization

/-!
# The metric-gradient identity for every actual good-locus tangent

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1491–1493,
and `lem:stable`, lines 1709–1724. The projected native Liouville field
pairs with every tangent vector by the differential of the restricted
potential. The identity retains the actual potential symplectic form.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FsFltz
open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold
variable {n : ℕ}

/-- At a good endpoint point, the true projected Liouville vector is the
metric gradient against every tangent, not just against itself. -/
theorem tailoring_good_projectedLiouville_gradient
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (q : TangentCoordinates n)
    (hq : lgCoverTangent x q =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)))
    (v : TangentCoordinates n)
    (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x (coordinateComplexStructure n v)) =
      (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x v) := by
  have hlead := fderiv_tailoringFamily_one_eq_leading_of_good I β x hx hgood
  have hrotate : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
      (coordinateComplexStructure n v) = 0 := by
    rw [hlead] at hv ⊢
    rw [tailoringLeadingDifferential_complexStructure, hv, mul_zero]
  have hcon := tailoring_projectedLiouville_contraction I β x hnd q hq
    (coordinateComplexStructure n v) hrotate
  rw [scalarDerivative_potential_lgCover hφ, fderiv_eq_coordinateGradient_pairing]
  simpa only [coordinateComplexStructure_apply] using hcon

end FsFltz
