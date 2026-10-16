import FsFltz.Target
import FsFltz.Geometry.MaslovPullback

/-!
# Prescribed representatives on the target's marked endpoints

The markings in `geoemtric-part-fsf.tex`, `g:initial`, lines 373–385, and
`g:chain`, lines 399–413, pull the explicit endpoint representatives back
to the completed pairs. These constructors consume the actual conclusion
data of the target. They do not construct initial pairs, terminal ribbons,
comparison chains, or grading extensions along a chain.
-/

noncomputable section

namespace FsFltz
open Geometry

namespace InitialPairData

/-- The prescribed source representative on the completed initial pair,
obtained through its specified primitive-preserving ambient marking. -/
def sourceMaslov {n : ℕ} {I : ToricInput n} {R K Aminus A : ℝ}
    {m : RoundingChoice} (initial : InitialPairData I R K Aminus A m)
    (hK : 0 ≤ K) : initial.pair.Maslov :=
  pullbackLogarithmicMaslovRepresentative initial.pair.ambientManifold
    initial.pair.ambientCompletion.ambient.primitive initial.ambientMarking.equiv
    I K hK initial.ambientMarking.primitive

/-- The constructed datum satisfies the exact source-marking prescription
used by `EndpointComparison.source_prescribed`. -/
theorem sourceMaslov_prescribed {n : ℕ} {I : ToricInput n} {R K Aminus A : ℝ}
    {m : RoundingChoice} (initial : InitialPairData I R K Aminus A m)
    (hK : 0 ≤ K) :
    IsLogarithmicGrading initial.ambientMarking.equiv (initial.sourceMaslov hK) :=
  isLogarithmicGrading_pullbackLogarithmicMaslovRepresentative initial.pair.ambientManifold
    initial.pair.ambientCompletion.ambient.primitive initial.ambientMarking.equiv
    I K hK initial.ambientMarking.primitive

end InitialPairData

namespace CotangentPairData

/-- The prescribed vertical-phase-zero representative on the completed
terminal pair, obtained through its standard cotangent marking. -/
def verticalMaslov {n : ℕ} (endpoint : CotangentPairData n) : endpoint.pair.Maslov :=
  pullbackCotangentMaslovRepresentative endpoint.pair.ambientManifold
    endpoint.pair.ambientCompletion.ambient.primitive endpoint.marking endpoint.primitive

/-- The constructed datum satisfies the exact endpoint-marking prescription
used by `EndpointComparison.vertical_prescribed`. -/
theorem verticalMaslov_prescribed {n : ℕ} (endpoint : CotangentPairData n) :
    IsVerticalGrading endpoint.marking endpoint.verticalMaslov :=
  isVerticalGrading_pullbackCotangentMaslovRepresentative endpoint.pair.ambientManifold
    endpoint.pair.ambientCompletion.ambient.primitive endpoint.marking endpoint.primitive

end CotangentPairData

end FsFltz
