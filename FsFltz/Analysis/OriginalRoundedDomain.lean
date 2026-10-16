import FsFltz.Analysis.OriginalRoundedBoundary
import FsFltz.Analysis.OriginalRoundedFrontier
import FsFltz.Geometry.RegularSublevelDomain

/-!
# Actual original rounded Liouville domains

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 909–920;
`geoemtric-part-fsf.tex`, `thm:target`, G2, lines 363–382.
Every admissible profile defines a native compact Liouville domain with
literal carrier `RoundedDomain` in the fixed quotient ambient and actual
primitive `lambdaKForm`. Its boundary and smooth embedding are constructed
from the proved scalar regularity. Initial-pair data and completion
markings are separate consumers.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Every admissible original rounding profile defines the actual native
compact Liouville domain, with the prescribed original primitive.
Source: `prop:allinitial`, lines 909–920. -/
def originalRoundedLiouvilleDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    LiouvilleDomain (2 * n) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  exact regularSublevelLiouvilleDomain (lgManifold n) (roundedDefiningFunction I R A m)
    (contMDiff_roundedDefiningFunction I R A m) (isCompact_roundedDomain I R A m)
    (lambdaKForm I K) (isSmoothForm_lambdaKForm I K)
    (isSymplecticOn_exteriorDerivative_lambdaKForm I hKnonneg)
    (differentialCovector_roundedDefiningFunction_originalLiouville_pos I
      hamb hR hset hK hfib hlevels m hadmiss)

/-- The compact domain underlying the actual original rounded Liouville
domain; no second boundary presentation is chosen. -/
abbrev originalRoundedCompactDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    CompactDomain (2 * n) :=
  (originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss).domain

/-- The actual rounded compact domain has the entire literal defining zero
level as its native frontier. -/
theorem originalRoundedCompactDomain_frontier {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    frontier (originalRoundedCompactDomain I hamb hR hset hK hfib hlevels m hadmiss).carrier =
      {y : (lgManifold n).Point | roundedDefiningFunction I R A m y = 0} :=
  frontier_roundedDomain I hamb hR hset hK hfib hlevels m hadmiss

/-- The constructed native smooth boundary embedding covers exactly the
whole rounded zero level, including the flat junctions. -/
theorem originalRoundedCompactDomain_boundary_range {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    range (originalRoundedCompactDomain I hamb hR hset hK hfib hlevels m hadmiss).boundaryInclusion.map =
      {y : (lgManifold n).Point | roundedDefiningFunction I R A m y = 0} :=
  (originalRoundedCompactDomain I hamb hR hset hK hfib hlevels m hadmiss).boundary_range.trans
    (originalRoundedCompactDomain_frontier I hamb hR hset hK hfib hlevels m hadmiss)

end FsFltz.Geometry
