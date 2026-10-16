import FsFltz.Analytic
import FsFltz.Geometry.ToricForms

/-!
# Actual geometric admissibility of a rounding

This is `def:rounding`, lines 309–326 in `geoemtric-part-fsf.tex`, with the
actual manifold derivatives and the intrinsic vector determined by
`lambdaKForm`. The equivalence with `CoordinateAdmissibleRounding` requires
the explicit coordinate/differential/form bridges of `sec:lean`, 805–814.
No completion marking, chain, or full-core conclusion is assumed here.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

def GeometricCornerCovectorsIndependent {n : ℕ} (I : ToricInput n)
    (y : (lgManifold n).Point) : Prop :=
  ∀ s t : ℝ, (∀ v : (lgManifold n).Tangent y,
    s * differentialCovector (lgManifold n) phi0 y v +
      t * differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y v = 0) →
    s = 0 ∧ t = 0

def GeometricAdmissibleRounding {n : ℕ} (I : ToricInput n)
    (R K Aminus A : ℝ) (m : RoundingChoice) : Prop :=
  0 < m.eps ∧ m.eps < A - Aminus ∧
    ∀ y : (lgManifold n).Point, y ∈ CornerBand I R A m.eps →
      0 < differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y) ∧
      GeometricCornerCovectorsIndependent I y

end FsFltz.Geometry
