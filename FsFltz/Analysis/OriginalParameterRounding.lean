import FsFltz.Analysis.OriginalRoundedBoundary

/-!
# Retaining the supplied rounding while increasing the base coefficient

Source: `geometric-part-fsf-proof.tex`, finite comparison assembly,
lines 2148–2153. The actual admissibility predicate and the outward derivative
persist on the same rounded domain. Constructing a marked pair deformation
from this path remains a separate geometric obligation.
-/

noncomputable section

namespace FsFltz

variable {n : ℕ}

/-- Positivity persists because the numerator is affine with nonnegative slope;
no monotonicity of the quotient itself is asserted. -/
theorem dAbsWSq_liouvilleCoordinates_pos_of_le (I : ToricInput n)
    {K L : ℝ} (hK : 0 ≤ K) (hKL : K ≤ L) (y : LGSpace n)
    (hpos : 0 < dAbsWSq I y (liouvilleCoordinates I K y)) :
    0 < dAbsWSq I y (liouvilleCoordinates I L y) := by
  rw [dAbsWSq_liouvilleCoordinates I hK] at hpos
  rw [dAbsWSq_liouvilleCoordinates I (hK.trans hKL)]
  apply div_pos _ (originalLiouville_denominator_pos I (hK.trans hKL) y)
  have hnum := (div_pos_iff_of_pos_right
    (originalLiouville_denominator_pos I hK y)).mp hpos
  have hslope := mul_nonneg (a_nonneg I y) (Complex.normSq_nonneg (W I y))
  nlinarith [mul_le_mul_of_nonneg_right hKL hslope]

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

/-- Every supplied admissible profile is retained for all larger nonnegative
base coefficients, including the empty corner in rank one. -/
theorem GeometricAdmissibleRounding.mono_parameter (I : ToricInput n)
    {R K L Aminus A : ℝ} {m : RoundingChoice} (hK : 0 ≤ K) (hKL : K ≤ L)
    (hm : GeometricAdmissibleRounding I R K Aminus A m) :
    GeometricAdmissibleRounding I R L Aminus A m := by
  rw [geometricAdmissibleRounding_iff I R hK Aminus A m] at hm
  rw [geometricAdmissibleRounding_iff I R (hK.trans hKL) Aminus A m]
  refine ⟨hm.1, hm.2.1, fun y hy => ?_⟩
  exact ⟨dAbsWSq_liouvilleCoordinates_pos_of_le I hK hKL y (hm.2.2 y hy).1,
    (hm.2.2 y hy).2⟩

/-- The fixed rounded domain stays outward along the entire increasing affine
coefficient path. This consumes the original, arbitrary supplied rounding. -/
theorem roundedDefiningFunction_increasing_parameter_path_outward
    (I : ToricInput n) {Aamb R Afib K L Aminus A : ℝ}
    (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K) (hKL : K ≤ L)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hm : GeometricAdmissibleRounding I R K Aminus A m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (y : (lgManifold n).Point) (hy : roundedDefiningFunction I R A m y = 0) :
    0 < differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y
      ((lgManifold n).liouvilleVector (lambdaKForm I ((1 - s) * K + s * L)) y) := by
  have hKnonneg : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hpath : K ≤ (1 - s) * K + s * L := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hKL)]
  exact differentialCovector_roundedDefiningFunction_originalLiouville_pos I
    hamb hR hset (hK.trans hpath) hfib hlevels m
    (GeometricAdmissibleRounding.mono_parameter I hKnonneg hpath hm) y hy

end FsFltz.Geometry
