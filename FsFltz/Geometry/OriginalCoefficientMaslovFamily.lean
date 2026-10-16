import FsFltz.Geometry.GradingRepresentatives
import FsFltz.Geometry.MaslovHomotopy

/-!
# The prescribed logarithmic datum along the original coefficient path

Source: `geometric-part-fsf-proof.tex`, `sec:assembly`, lines 2148–2153;
`geoemtric-part-fsf.tex`, `def:maslov`, lines 225–240.
The ambient complex field and squared volume tensor are literally constant.
Their transport to a completed pair family requires its actual completion
map germs and is not asserted by this construction.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- The fixed logarithmic complex field and squared volume tensor form the
prescribed actual Maslov family along every nonnegative affine coefficient
path, with smooth extensions across both parameter endpoints. -/
def logarithmicAffineMaslovFamily {n : ℕ} (I : ToricInput n)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    MaslovFamily (lgManifold n) (fun t =>
      (lgManifold n).exteriorDerivative (lambdaKForm I ((1 - t) * K + t * L))) where
  J := fun _ => logarithmicAlmostComplexField n
  tensor := fun _ => logarithmicSquaredVolumeTensor n
  compatible := fun _ ht => isCompatibleAlmostComplex_logarithmicAlmostComplexField I
    (add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hK) (mul_nonneg ht.1 hL))
  canonical := fun _ _ => logarithmicSquaredVolumeTensor_canonical
  nowhereZero := fun _ _ => logarithmicSquaredVolumeTensor_ne_zero
  smoothJ := fun a => SmoothNearInterval.constant
    (chartAt (Model (2 * n)) a).open_target
    (isSmoothAlmostComplexField_logarithmicAlmostComplexField n a)
  smoothSection := fun a => SmoothNearInterval.constant
    (chartAt (Model (2 * n)) a).open_target
    (isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n a)

@[simp]
theorem logarithmicAffineMaslovFamily_J {n : ℕ} (I : ToricInput n)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (t : ℝ) :
    (logarithmicAffineMaslovFamily I K L hK hL).J t =
      logarithmicAlmostComplexField n := rfl

@[simp]
theorem logarithmicAffineMaslovFamily_tensor {n : ℕ} (I : ToricInput n)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (t : ℝ) :
    (logarithmicAffineMaslovFamily I K L hK hL).tensor t =
      logarithmicSquaredVolumeTensor n := rfl

end FsFltz.Geometry
