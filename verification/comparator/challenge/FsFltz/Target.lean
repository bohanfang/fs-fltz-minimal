import FsFltz.Geometry.Admissibility
import FsFltz.Geometry.FixedAmbient
import FsFltz.Geometry.MaslovChain
import FsFltz.Geometry.PrescribedGrading
import FsFltz.Compactness

/-!
# The geometric FS–FLTZ target proposition

Authoritative source: `geoemtric-part-fsf.tex`, `thm:target`, lines 352–435,
and `sec:lean`, lines 766–836. This file defines the proposition and its
conclusion data. It does not assert a theorem, an axiom, or a placeholder proof.

Every marking is an actual smooth primitive-preserving diffeomorphism.
The initial domains and whole fiber are tied to the literal source subsets;
the terminal full core is tied to the literal positive-cone FLTZ subset.
The same finite geometric path carries the prescribed grading.

The remaining boundary, completion and varying-family representation bridges
are required Phase 1 proofs, listed in `fidelity-audit.md`. Type checking does
not establish equivalence with every intrinsic source formulation or prove the
geometric existence theorem. Categorical deductions are out of scope and supply
no assumptions to this proposition.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The whole regular fiber with the restriction of the actual `lambda0`.
It is a conclusion witness, never an extra condition on the toric input. -/
structure FullFiberModel {n : ℕ} (I : ToricInput n) (R : ℝ) where
  ambient : CompleteLiouvilleManifold (2 * n - 2)
  embedding : ambient.manifold.SmoothEmbedding (lgManifold n)
  image : Set.range embedding.map = FullFiber I R
  primitive : ambient.manifold.pullback (lgManifold n) embedding.map
    (lambda0Form n) = ambient.primitive
  regularValue : ∀ y : (lgManifold n).Point, W I y = (R : ℂ) →
    Function.Surjective (complexDifferential (lgManifold n) (W I) y)

/-- The specified initial pair, including its two inclusion/flow markings.
Image equations and the ribbon square express the literal inclusions from
`eq:initialpair`; an unrelated abstract copy of the fiber is insufficient. -/
structure InitialPairData {n : ℕ} (I : ToricInput n)
    (R K Aminus A : ℝ) (m : RoundingChoice) where
  pair : WitnessedPair n
  ambient : CompletePrimitive (lgManifold n) (lambdaKForm I K)
  domainEmbedding : pair.ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)
  domain_image : domainEmbedding.map '' pair.ambientDomain.domain.carrier = RoundedDomain I R A m
  ambientMarking : InclusionMarking pair.ambientCompletion ambient.toCompleteLiouvilleManifold
    (fun x => domainEmbedding.map x.val)
  witness_one : ∀ x, pair.witness x = 1
  fiber : FullFiberModel I R
  ribbonInFiber : pair.ribbonDomain.domain.extension.SmoothEmbedding fiber.ambient.manifold
  ribbon_image : (fun x => fiber.embedding.map (ribbonInFiber.map x)) ''
    pair.ribbonDomain.domain.carrier = InitialRibbon I R Aminus
  ribbon_square : ∀ x ∈ pair.ribbonDomain.domain.carrier,
    domainEmbedding.map (pair.ambientDomain.domain.boundaryInclusion.map
      (pair.ribbonEmbedding.map x)) = fiber.embedding.map (ribbonInFiber.map x)
  fiberMarking : InclusionMarking pair.ribbonCompletion fiber.ambient
    (fun x => ribbonInFiber.map x.val)
  ribbon_nonempty : pair.ribbonDomain.domain.carrier.Nonempty

/-- The fixed based Euclidean cotangent disk, not the supremum-norm disk. -/
def cotangentDisk {n : ℕ} : Set (Cotangent n) :=
  {x | realSquaredNorm x.2 ≤ 1}

/-- The terminal domain is the standard cotangent disk in its explicit
completion coordinates. The end equation fixes the standard radial marking. -/
structure CotangentPairData (n : ℕ) where
  pair : WitnessedPair n
  marking : pair.ambientManifold.SmoothEquiv (cotangentManifold n)
  primitive : pair.ambientManifold.pullback (cotangentManifold n) marking
    (lambdaCanForm n) = pair.ambientCompletion.ambient.primitive
  domain_image : (fun x => marking (pair.ambientCompletion.inclusion.map x)) ''
    pair.ambientDomain.domain.carrier = cotangentDisk
  boundary_image : Set.range (fun x => marking (pair.ambientCompletion.inclusion.map
    (pair.ambientDomain.domain.boundaryInclusion.map x))) = cosphere
  standard_end : ∀ (x : pair.ambientDomain.domain.boundary.Point) (r : ℝ), 0 ≤ r →
    let q := marking (pair.ambientCompletion.inclusion.map
      (pair.ambientDomain.domain.boundaryInclusion.map x))
    marking (pair.ambientCompletion.endMap (x, r)) = (q.1, Real.exp r • q.2)

namespace CotangentPairData

/-- The actual embedding of the full intrinsic ribbon core in cotangent
coordinates, using this very endpoint's primitive and standard marking. -/
def embeddedCore {n : ℕ} (E : CotangentPairData n) : Set (Cotangent n) :=
  (fun x => E.marking (E.pair.ambientCompletion.inclusion.map
    (E.pair.ambientDomain.domain.boundaryInclusion.map (E.pair.ribbonEmbedding.map x)))) ''
      E.pair.ribbonCompletion.core

end CotangentPairData

/-- One existential package for the terminal ribbon, the actual finite chain,
literal full-core equality, and grading on that same chain (`g:chain`). -/
structure EndpointComparison {n : ℕ} {I : ToricInput n}
    {R K Aminus A : ℝ} {m : RoundingChoice} (initial : InitialPairData I R K Aminus A m) where
  endpoint : CotangentPairData n
  chain : ComparisonChain initial.pair endpoint.pair
  core_eq : endpoint.embeddedCore = fltzLink I
  sourceDatum : initial.pair.Maslov
  source_prescribed : IsLogarithmicGrading initial.ambientMarking.equiv sourceDatum
  endpointDatum : endpoint.pair.Maslov
  graded : GradedComparisonChain initial.pair chain sourceDatum endpointDatum
  verticalDatum : endpoint.pair.Maslov
  vertical_prescribed : IsVerticalGrading endpoint.marking verticalDatum
  endpoint_homotopy : MaslovHomotopy endpointDatum verticalDatum

/-- G1: both time directions and finite type for every nonnegative real K,
including values below the ribbon threshold. -/
def AllNonnegativeComplete {n : ℕ} (I : ToricInput n) : Prop :=
  ∀ K : ℝ, 0 ≤ K → Nonempty (FiniteTypePrimitive (lgManifold n) (lambdaKForm I K))

/-- G2 with its chosen ambient bound and radius displayed, so the conditional
comparison of choices can refer to their precise common parameter range. -/
def InitialRangeAssertions {n : ℕ} (I : ToricInput n) (Aamb R0 : ℝ) : Prop :=
  AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ((ratioSet I R).Nonempty ∧ BddAbove (ratioSet I R) ∧
          ∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
        ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
          ∀ K : ℝ, K0 I R ≤ K →
            ∀ Aminus A : ℝ, Afib < Aminus → Aminus < A →
              (∃ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m) ∧
              ∀ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m →
                Nonempty (InitialPairData I R K Aminus A m)

/-- G1–G2 alone, for the separate conditional comparison of initial choices.
Every bound/rounding/marking here is a conclusion; geometric admissibility
contains only the exact band conditions, not fullness or comparison data. -/
def InitialGeometricAssertions {n : ℕ} (I : ToricInput n) : Prop :=
  AllNonnegativeComplete I ∧
    ∃ Aamb R0 : ℝ, InitialRangeAssertions I Aamb R0

/-- The unproved target for one finite toric input. The source quantifier order
is literal: a shared ambient bound/radius, every large R, every valid fiber
bound, every K above the formula-defined supremum, every allowed level pair,
existence of a rounding, and then every admissible rounding. -/
def GeometricTargetFor {n : ℕ} (I : ToricInput n) : Prop :=
  AllNonnegativeComplete I ∧
    ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ((ratioSet I R).Nonempty ∧ BddAbove (ratioSet I R) ∧
          ∃ Afib : ℝ, FiberEndBound I Aamb R Afib) ∧
        ∀ Afib : ℝ, FiberEndBound I Aamb R Afib →
          ∀ K : ℝ, K0 I R ≤ K →
            ∀ Aminus A : ℝ, Afib < Aminus → Aminus < A →
              (∃ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m) ∧
              ∀ m : RoundingChoice, GeometricAdmissibleRounding I R K Aminus A m →
                ∃ initial : InitialPairData I R K Aminus A m,
                  Nonempty (EndpointComparison initial)

/-- `thm:target` as a named proposition, with only the source's finite
combinatorial and coefficient data as inputs. No proof is asserted. -/
def GeometricTarget : Prop := ∀ n : ℕ, ∀ I : ToricInput n, GeometricTargetFor I

end FsFltz
