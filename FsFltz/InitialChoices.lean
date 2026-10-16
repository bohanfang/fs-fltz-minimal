import FsFltz.Target

/-!
# Conditional comparison of admissible initial choices

The original `geoemtric-part-fsf.tex`, `lem:choices`, lines 437–474, asserts
this consequence of G1–G2. This file defines its proposition, with the
chosen ambient bound/radius and both possibly different fiber bounds
displayed. `Geometry.OriginalVaryingLevelChoice` proves it as
`initialChoicesStatement` using the actual three-step marked and graded chain.

Every intermediate tuple is mapped into the same literal `(Y, lambdaK)`.
Deformation markings vary jointly smoothly on completed spaces. A strict
identification commutes with these markings on the entire completed ambient,
so it is literally the identity on marked Y. This is the geometric data
needed to pull back any fixed ambient background class. No cohomology theory
or class-transport theorem is asserted: its pullback/functoriality bridge
remains separate, as do the general categorical foundations (lines 476–486).
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- An actual inclusion presentation of a pair inside the fixed source
ambient, with both the completed primitive and compact restriction specified. -/
structure FixedAmbientPairMarking {n : ℕ} (I : ToricInput n) (K : ℝ)
    (P : WitnessedPair n) where
  domainEmbedding : P.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)
  equiv : P.ambientManifold.SmoothEquiv (lgManifold n)
  primitive : P.ambientManifold.pullback (lgManifold n) equiv (lambdaKForm I K) =
    P.ambientCompletion.ambient.primitive
  compact_square : ∀ x ∈ P.ambientDomain.domain.carrier,
    equiv (P.ambientCompletion.inclusion.map x) = domainEmbedding.map x
  domain_primitive : ∀ x ∈ P.ambientDomain.domain.carrier,
    P.ambientDomain.domain.extension.pullback (lgManifold n) domainEmbedding.map
      (lambdaKForm I K) x = P.ambientDomain.liouville.primitive x

/-- Markings throughout this very deformation, jointly smooth in its
specified fixed compact and completed presentations, including endpoints. -/
structure FixedAmbientPairDeformation {n : ℕ} {I : ToricInput n} {K : ℝ}
    (D : PairDeformation n) (source : FixedAmbientPairMarking I K D.source)
    (target : FixedAmbientPairMarking I K D.target) where
  marking : ∀ t, FixedAmbientPairMarking I K (D.pair t)
  source_eq : marking parameterZero = source
  target_eq : marking parameterOne = target
  completed_smooth : D.source.ambientManifold.IsSmoothIntervalMapFamily (lgManifold n)
    (fun t x => (marking t).equiv ((D.ambientCompletionPresentation t).equiv x))
  compact_smooth : D.source.ambientDomain.domain.extension.IsSmoothIntervalMapFamily (lgManifold n)
    (fun t x => (marking t).domainEmbedding.map ((D.ambientPresentation t).extensionEquiv x))

/-- Decoration of an actual permitted step. Primitive preservation and
identity on marked Y are exact map equations, rather than opaque predicates. -/
inductive FixedAmbientComparisonStep {n : ℕ} {I : ToricInput n} {K : ℝ} :
    {P Q : WitnessedPair n} → ComparisonStep n P Q →
      FixedAmbientPairMarking I K P → FixedAmbientPairMarking I K Q → Type 1
  | deformation {D : PairDeformation n}
      {source : FixedAmbientPairMarking I K D.source}
      {target : FixedAmbientPairMarking I K D.target}
      (family : FixedAmbientPairDeformation D source target) :
      FixedAmbientComparisonStep (.deformation D) source target
  | identification {P Q : WitnessedPair n} {h : CompletionIdentification P Q}
      {source : FixedAmbientPairMarking I K P} {target : FixedAmbientPairMarking I K Q}
      (identity_on_marked_ambient : ∀ x : P.ambientManifold.Point,
        target.equiv (h.ambientEquiv x) = source.equiv x) :
      FixedAmbientComparisonStep (.identification h) source target
  | reverse {P Q : WitnessedPair n} {step : ComparisonStep n P Q}
      {source : FixedAmbientPairMarking I K P} {target : FixedAmbientPairMarking I K Q}
      (decoration : FixedAmbientComparisonStep step source target) :
      FixedAmbientComparisonStep (.reverse step) target source

/-- The decoration follows the same finite path, sharing each intermediate
marking literally. Reverses retain the actual specified maps. -/
inductive FixedAmbientComparisonChain {n : ℕ} {I : ToricInput n} {K : ℝ}
    (P : WitnessedPair n) : {Q : WitnessedPair n} → ComparisonChain P Q →
      FixedAmbientPairMarking I K P → FixedAmbientPairMarking I K Q → Type 1
  | nil (marking : FixedAmbientPairMarking I K P) :
      FixedAmbientComparisonChain P Quiver.Path.nil marking marking
  | cons {Q R : WitnessedPair n} {path : ComparisonChain P Q}
      {step : ComparisonStep n Q R}
      {source : FixedAmbientPairMarking I K P} {junction : FixedAmbientPairMarking I K Q}
      {target : FixedAmbientPairMarking I K R}
      (initial : FixedAmbientComparisonChain P path source junction)
      (last : FixedAmbientComparisonStep step junction target) :
      FixedAmbientComparisonChain P (path.cons step) source target

/-- One comparison of the two supplied initial choices. The endpoint markings
are the supplied inclusion markings, and grading is carried by the same path. -/
structure InitialChoiceComparison {n : ℕ} {I : ToricInput n} {R K : ℝ}
    {Aminus0 A0 Aminus1 A1 : ℝ} {m0 m1 : RoundingChoice}
    (initial0 : InitialPairData I R K Aminus0 A0 m0)
    (initial1 : InitialPairData I R K Aminus1 A1 m1) where
  sourceMarking : FixedAmbientPairMarking I K initial0.pair
  targetMarking : FixedAmbientPairMarking I K initial1.pair
  source_embedding : sourceMarking.domainEmbedding = initial0.domainEmbedding
  target_embedding : targetMarking.domainEmbedding = initial1.domainEmbedding
  source_marking : sourceMarking.equiv = initial0.ambientMarking.equiv
  target_marking : targetMarking.equiv = initial1.ambientMarking.equiv
  chain : ComparisonChain initial0.pair initial1.pair
  fixedAmbient : FixedAmbientComparisonChain initial0.pair chain sourceMarking targetMarking
  sourceDatum : initial0.pair.Maslov
  targetDatum : initial1.pair.Maslov
  source_prescribed : IsLogarithmicGrading initial0.ambientMarking.equiv sourceDatum
  target_prescribed : IsLogarithmicGrading initial1.ambientMarking.equiv targetDatum
  graded : GradedComparisonChain initial0.pair chain sourceDatum targetDatum

/-- The separate conditional proposition of `lem:choices`, proved by
`initialChoicesStatement` in `Geometry.OriginalVaryingLevelChoice`.
The two valid fiber bounds may differ, while I, Aamb, R0, R and K are shared.
Both actual InitialPairData packages are universally quantified. -/
def InitialChoicesStatement : Prop :=
  ∀ n : ℕ, ∀ I : ToricInput n, ∀ Aamb R0 : ℝ,
    AllNonnegativeComplete I → InitialRangeAssertions I Aamb R0 →
      ∀ R : ℝ, R0 ≤ R → ∀ K : ℝ, K0 I R ≤ K →
        ∀ Afib0 Afib1 : ℝ,
          FiberEndBound I Aamb R Afib0 → FiberEndBound I Aamb R Afib1 →
            ∀ Aminus0 A0 Aminus1 A1 : ℝ,
              Afib0 < Aminus0 → Aminus0 < A0 → Afib1 < Aminus1 → Aminus1 < A1 →
                ∀ m0 m1 : RoundingChoice,
                  GeometricAdmissibleRounding I R K Aminus0 A0 m0 →
                  GeometricAdmissibleRounding I R K Aminus1 A1 m1 →
                    ∀ initial0 : InitialPairData I R K Aminus0 A0 m0,
                    ∀ initial1 : InitialPairData I R K Aminus1 A1 m1,
                      Nonempty (InitialChoiceComparison initial0 initial1)

end FsFltz
