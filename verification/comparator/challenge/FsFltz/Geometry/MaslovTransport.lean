import FsFltz.Geometry.Maslov
import FsFltz.Geometry.Deformation
import FsFltz.Geometry.Identification

/-!
# Grading lifts on the specified geometric comparison steps

`def:maslov`, source lines 225–232, requires data over the same completed
family or completion map as the geometric step. These definitions attach
the concrete tensor representatives to those actual objects. In particular
the endpoints use the family's specified presentations, even when its
initial presentation is not the identity. The fixed-J bundle correspondence
is proved in `CanonicalSquareBundle`; correspondence for these prescribed
varying completed families remains a separate foundation obligation.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

namespace WitnessedPair

abbrev ambientManifold {n : ℕ} (P : WitnessedPair n) :=
  P.ambientCompletion.ambient.manifold

def ambientSymplecticForm {n : ℕ} (P : WitnessedPair n) : P.ambientManifold.Form 2 :=
  P.ambientManifold.exteriorDerivative P.ambientCompletion.ambient.primitive

abbrev Maslov {n : ℕ} (P : WitnessedPair n) :=
  MaslovRepresentative P.ambientManifold P.ambientSymplecticForm

end WitnessedPair

/-- An extension of the grading over the completed ambient of this very
deformation, with endpoint representatives read in its specified charts. -/
structure GradedPairDeformation {n : ℕ} (D : PairDeformation n)
    (source : D.source.Maslov) (target : D.target.Maslov) where
  etaExtension : ℝ → D.source.ambientManifold.Form 2
  eta_agrees : ∀ t : Parameter, etaExtension t.val =
    D.source.ambientManifold.exteriorDerivative (D.completedPrimitive t)
  family : MaslovFamily D.source.ambientManifold etaExtension
  sourceJ : family.J 0 = pullbackAlmostComplex D.source.ambientManifold
    D.source.ambientManifold (D.ambientCompletionPresentation parameterZero).equiv source.J
  targetJ : family.J 1 = pullbackAlmostComplex D.source.ambientManifold
    D.target.ambientManifold (D.ambientCompletionPresentation parameterOne).equiv target.J
  sourceTensor : family.tensor 0 = pullbackSquaredTensor D.source.ambientManifold
    D.source.ambientManifold (D.ambientCompletionPresentation parameterZero).equiv source.tensor
  targetTensor : family.tensor 1 = pullbackSquaredTensor D.source.ambientManifold
    D.target.ambientManifold (D.ambientCompletionPresentation parameterOne).equiv target.tensor

/-- The graded completion lift is indexed by the actual strict geometric
identification; an unrelated ambient map cannot be substituted. -/
abbrev GradedCompletionIdentification {n : ℕ} {P Q : WitnessedPair n}
    (identification : CompletionIdentification P Q) (source : P.Maslov) (target : Q.Maslov) :=
  MaslovCompletionLift P.ambientManifold Q.ambientManifold
    P.ambientSymplecticForm Q.ambientSymplecticForm identification.ambientEquiv source target

end FsFltz.Geometry
