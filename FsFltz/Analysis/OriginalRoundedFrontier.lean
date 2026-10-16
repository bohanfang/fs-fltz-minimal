import FsFltz.Analysis.OriginalRoundedBoundary
import FsFltz.Geometry.RegularSublevelFrontier

/-!
# Literal frontier of every original rounded domain

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 909–930,
especially the regular boundary conclusion at lines 915–919;
`geoemtric-part-fsf.tex`, `thm:target`, G2, lines 363–382.
A regular zero of a smooth real function cannot be interior to its closed
sublevel: otherwise Fermat's theorem would make the native differential
zero. This identifies the literal rounded frontier with the zero level,
before any separate native boundary-atlas construction.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold


private theorem roundedDefiningFunction_zeroLevel_nonzero {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (y : (lgManifold n).Point) (hy : roundedDefiningFunction I R A m y = 0) :
    differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y ≠ 0 := by
  have hsurj := roundedDefiningFunction_zeroLevel_regular I hamb hR hset hK
    hfib hlevels m hadmiss y hy
  intro hz
  obtain ⟨v, hv⟩ := hsurj 1
  rw [hz, zero_apply] at hv
  exact zero_ne_one hv

set_option backward.isDefEq.respectTransparency false in
/-- The topological frontier of the literal original rounded domain is
exactly its entire defining zero level for every admissible rounding.
Source: `prop:allinitial`, lines 915–919. -/
theorem frontier_roundedDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    frontier (RoundedDomain I R A m) =
      {y : LGSpace n | roundedDefiningFunction I R A m y = 0} := by
  exact SmoothManifold.frontier_scalar_sublevel_of_regular_zero (M := lgManifold n)
    (roundedDefiningFunction I R A m) (contMDiff_roundedDefiningFunction I R A m)
    (roundedDefiningFunction_zeroLevel_nonzero I hamb hR hset hK hfib hlevels m hadmiss)

set_option backward.isDefEq.respectTransparency false in
/-- The interior of the literal rounded domain is exactly the strict
defining sublevel for every admissible rounding profile. -/
theorem interior_roundedDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    interior (RoundedDomain I R A m) =
      {y : LGSpace n | roundedDefiningFunction I R A m y < 0} := by
  exact SmoothManifold.interior_scalar_sublevel_of_regular_zero (M := lgManifold n)
    (roundedDefiningFunction I R A m) (contMDiff_roundedDefiningFunction I R A m)
    (roundedDefiningFunction_zeroLevel_nonzero I hamb hR hset hK hfib hlevels m hadmiss)

end FsFltz.Geometry
