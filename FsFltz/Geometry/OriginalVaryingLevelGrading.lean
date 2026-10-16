import FsFltz.Geometry.OriginalVaryingLevelMarkedFamily
import FsFltz.Geometry.MaslovHomotopy

/-!
# Grading on the same varying full-ribbon family

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 437–474, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973.
The ambient completion and its presentation are constant in the actual
constructed deformation. Thus every actual ambient datum extends by the
constant smooth family, while the entire ribbon moves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ} (E : LiouvilleDomain (2 * n)) (CE : Completion E)
  (D : CompactDomain (2 * n - 2)) (Λ : Parameter → LiouvilleStructure D)
  (j : Parameter → D.extension.SmoothEmbedding E.domain.boundary)
  (hj : D.extension.IsSmoothIntervalMapFamily E.domain.boundary (fun t => (j t).map))
  (ribbon : LocalizedCompletionFamily D Λ)
  (hp : ∀ t, D.extension.pullback E.domain.boundary (j t).map
    (E.domain.boundaryForm E.liouville.primitive) = (Λ t).primitive)

/-- A datum on the unchanged completed ambient extends on the very same
constructed deformation, with exact endpoint representatives. -/
def fixedAmbientLocalizedPairDeformationGrading
    (s : MaslovRepresentative CE.ambient.manifold
      (CE.ambient.manifold.exteriorDerivative CE.ambient.primitive)) :
    GradedPairDeformation
      (fixedAmbientLocalizedPairDeformation E CE D Λ j hj ribbon hp) s s where
  etaExtension := fun _ => CE.ambient.manifold.exteriorDerivative CE.ambient.primitive
  eta_agrees := fun _ => by
    change _ = CE.ambient.manifold.exteriorDerivative
      (CE.ambient.manifold.pullback CE.ambient.manifold id CE.ambient.primitive)
    rw [CE.ambient.manifold.pullback_id]
  family := (MaslovHomotopy.refl s).family
  sourceJ := (pullbackAlmostComplex_refl _ _).symm
  targetJ := (pullbackAlmostComplex_refl _ _).symm
  sourceTensor := (pullbackSquaredTensor_refl _ _).symm
  targetTensor := (pullbackSquaredTensor_refl _ _).symm

namespace OriginalVaryingLevelBoundaryData

variable {I : ToricInput n} {Aamb R Afib K A B Lbound Elevel : ℝ}
  {hamb : AmbientEndBound I Aamb}
  {hR : max 1 (sublevelMagnitudeSup I Aamb) < R}
  {hset : RatioSetWellDefined I R} {hK : K0 I R ≤ K}
  {hfib : FiberEndBound I Aamb R Afib} {hA : Afib < A} (hB : Afib < B)
  {hL : max A B < Lbound} {m : RoundingChoice}
  {hm : GeometricAdmissibleRounding I R K Lbound Elevel m}
  (V : OriginalVaryingLevelBoundaryData I hamb hR hset hK hfib hA hL m hm)

local notation "CE" => originalRoundedCompletion I hamb hR hset hK hfib
  (lt_trans hA (lt_of_le_of_lt (le_max_left A B) hL)) m hm

/-- The constant ambient datum grades this same actual full-ribbon motion. -/
def graded (s : MaslovRepresentative (CE).ambient.manifold
    ((CE).ambient.manifold.exteriorDerivative (CE).ambient.primitive)) :
    GradedPairDeformation V.deformation s s :=
  fixedAmbientLocalizedPairDeformationGrading _ _ V.domain V.liouville
    V.boundaryEmbedding V.boundary_smooth V.ribbonFamily V.boundary_primitive s

end OriginalVaryingLevelBoundaryData

end FsFltz.Geometry
