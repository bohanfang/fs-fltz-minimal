import FsFltz.Geometry.PotentialTailoringNormalizedJunction
import FsFltz.Geometry.TailoringRetainedRibbonMarkingFamily
import FsFltz.Geometry.PotentialPathRetainedRibbonMarkingFamily
import FsFltz.Geometry.PairFamilyFiniteChain

/-!
# The actual marked finite holomorphic-to-tailoring prefix

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
`eq:normalizedrounding` and common markings, lines 1260–1314, and assembly,
lines 2127–2258; `geoemtric-part-fsf.tex`, `def:chain`, lines 163–200.
The output bundles retain existing geometric pairs and actual marking maps.
Their finite-input producer constructs the junction on those very pairs.
The prefix ends before intrinsic shrinking, hitting maps and the full core.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- An actual inclusion marking of the retained ribbon onto the entire
regular fiber, with the literal intrinsic potential primitive. -/
structure FullFiberRibbonMarking {n : ℕ} (P : WitnessedPair n)
    (R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (f : LGSpace n → ℂ) (value : ℂ) (φ : RealSpace n → ℝ) where
  manifold : SmoothManifold (2 * n - 2)
  embedding : manifold.SmoothEmbedding (lgManifold n)
  primitive : CompletePrimitive manifold
    (manifold.pullback (lgManifold n) embedding.map (lambdaPotentialForm φ))
  inclusion : P.ribbonDomain.domain.Point → manifold.Point
  image : range embedding.map = {y | f y = value}
  compact_square : ∀ x, embedding.map (inclusion x) = R.map x.val
  marking : InclusionMarking P.ribbonCompletion primitive.toCompleteLiouvilleManifold inclusion

/-- Geometry of one actual embedded rounded pair deformation. The full
carrier and frontier equations prevent replacement by an unrelated pair. -/
structure EmbeddedRoundedPairFamily {n : ℕ}
    (ρ : Parameter → LGSpace n → ℝ) (f : Parameter → LGSpace n → ℂ)
    (φ : Parameter → RealSpace n → ℝ) (value : ℂ) (level coefficient : ℝ) where
  deformation : PairDeformation n
  embedding : ∀ t, (deformation.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)
  ambient_nonempty : ∀ t, (deformation.pair t).ambientDomain.domain.carrier.Nonempty
  ribbon_nonempty : ∀ t, (deformation.pair t).ribbonDomain.domain.carrier.Nonempty
  ambient_image : ∀ t, (embedding t).map '' (deformation.pair t).ambientDomain.domain.carrier =
    {y | ρ t y ≤ 0}
  ambient_frontier : ∀ t, (embedding t).map '' frontier (deformation.pair t).ambientDomain.domain.carrier =
    {y | ρ t y = 0}
  ribbon_image : ∀ t,
    ((embedding t).comp ((deformation.pair t).ambientDomain.domain.boundaryInclusion.comp
      (deformation.pair t).ribbonEmbedding)).map '' (deformation.pair t).ribbonDomain.domain.carrier =
    {y | f t y = value ∧ φ t y.1 ≤ level}
  ribbon_frontier : ∀ t,
    ((embedding t).comp ((deformation.pair t).ambientDomain.domain.boundaryInclusion.comp
      (deformation.pair t).ribbonEmbedding)).map '' frontier (deformation.pair t).ribbonDomain.domain.carrier =
    {y | f t y = value ∧ φ t y.1 = level}
  ambient_primitive : ∀ t, (deformation.pair t).ambientDomain.liouville.primitive =
    (deformation.pair t).ambientDomain.domain.extension.pullback (lgManifold n) (embedding t).map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm (φ t)) (f t) coefficient)
  ribbon_primitive : ∀ t, (deformation.pair t).ribbonDomain.liouville.primitive =
    (deformation.pair t).ribbonDomain.domain.extension.pullback (lgManifold n)
      ((embedding t).comp ((deformation.pair t).ambientDomain.domain.boundaryInclusion.comp
        (deformation.pair t).ribbonEmbedding)).map (lambdaPotentialForm (φ t))
  witness : ∀ t, (deformation.pair t).witness = (fun _ => 1)
  ambient_smooth : (deformation.pair parameterZero).ambientDomain.domain.extension.IsSmoothIntervalMapFamily
    (lgManifold n) (fun t x => (embedding t).map ((deformation.ambientPresentation t).extensionEquiv x))
  ribbon_smooth : (deformation.pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalMapFamily
    (lgManifold n) (fun t x =>
      ((embedding t).comp ((deformation.pair t).ambientDomain.domain.boundaryInclusion.comp
        (deformation.pair t).ribbonEmbedding)).map ((deformation.ribbonPresentation t).extensionEquiv x))
  ribbon_marking : ∀ t, FullFiberRibbonMarking (deformation.pair t)
    ((embedding t).comp ((deformation.pair t).ambientDomain.domain.boundaryInclusion.comp
      (deformation.pair t).ribbonEmbedding)) (f t) value (φ t)

/-- Smooth actual inclusion markings onto the entire fixed native ambient.
Both directions are measured in this very deformation's completions. -/
structure FullAmbientInclusionMarkingFamily {n : ℕ} (Q : PairDeformation n)
    (J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (α : Parameter → (lgManifold n).Form 1) where
  primitive : ∀ t, CompletePrimitive (lgManifold n) (α t)
  marking : ∀ t, InclusionMarking (Q.pair t).ambientCompletion
    (primitive t).toCompleteLiouvilleManifold (fun x => (J t).map x.val)
  forward_smooth : IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn
    (Q.pair parameterZero).ambientCompletion.ambient.manifold (lgManifold n) univ
    (fun t => (Q.ambientCompletionPresentation t).equiv.trans (marking t).equiv)
  inverse_smooth : IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn
    (lgManifold n) (Q.pair parameterZero).ambientCompletion.ambient.manifold univ
    (fun t => ((Q.ambientCompletionPresentation t).equiv.trans (marking t).equiv).symm)

/-- The actual smoothly marked outer completions for the tailored family.
The compact square retains inclusion in the specified logarithmic ambient. -/
structure OuterAmbientInclusionMarkingFamily {n : ℕ} (Q : PairDeformation n)
    (J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (ρ : LGSpace n → ℝ) (α : Parameter → (lgManifold n).Form 1) where
  domain : CompactDomain (2 * n)
  nativeEmbedding : domain.extension.SmoothEmbedding (lgManifold n)
  native_image : nativeEmbedding.map '' domain.carrier = {y | ρ y ≤ 0}
  liouville : Parameter → LiouvilleStructure domain
  native_primitive : ∀ t, (liouville t).primitive =
    domain.extension.pullback (lgManifold n) nativeEmbedding.map (α t)
  family : LocalizedCompletionFamily domain liouville
  inclusion : ∀ t, (Q.pair t).ambientDomain.domain.Point →
    (family.collars t).cylindricalCompletion.ambient.manifold.Point
  marking : ∀ t, InclusionMarking (Q.pair t).ambientCompletion
    (family.collars t).cylindricalCompletion.ambient (inclusion t)
  compact_square : ∀ t x,
    (nativeEmbedding.comp (family.collars t).originalInclusion).map (inclusion t x) = (J t).map x.val
  forward_smooth : IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn
    (Q.pair parameterZero).ambientCompletion.ambient.manifold
    (family.collars parameterZero).cylindricalCompletion.ambient.manifold univ
    (fun t => ((Q.ambientCompletionPresentation t).equiv.trans (marking t).equiv).trans
      (family.completionPresentation t).equiv.symm)
  inverse_smooth : IntrinsicSmoothBundle.HasSmoothManifoldTargetFamilyOn
    (family.collars parameterZero).cylindricalCompletion.ambient.manifold
    (Q.pair parameterZero).ambientCompletion.ambient.manifold univ
    (fun t => (((Q.ambientCompletionPresentation t).equiv.trans (marking t).equiv).trans
      (family.completionPresentation t).equiv.symm).symm)

/-- The explicit finite-input output before shrinking and hitting maps.
No geometric chain or marking is an input of its existence theorem. -/
structure PotentialTailoringMarkedPrefix {n : ℕ} (I : ToricInput n)
    (φ : RealSpace n → ℝ) (β Cplus Aminus K : ℝ) (m : RoundingChoice) where
  holomorphic : EmbeddedRoundedPairFamily
    (fun t y => potentialPath_roundedDefiningFunction I φ (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m (t.val, y))
    (fun t => W (I.alongCoefficientPath t.val))
    (fun t => potentialPath (fun u => realSquaredNorm u / 2) φ t.val)
    (Real.exp β : ℂ) Aminus (K / Real.exp β ^ 2)
  tailoring : EmbeddedRoundedPairFamily
    (fun t => tailoringRoundedDefiningFunction I φ β t.val (Real.exp β) (Cplus ^ 2 * β ^ 2 / 2) m)
    (fun t => tailoringFamily I β t.val) (fun _ => φ) 1 Aminus K
  holomorphic_ambient_marking : FullAmbientInclusionMarkingFamily holomorphic.deformation holomorphic.embedding
    (fun t => (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
      (W (I.alongCoefficientPath t.val)) (K / Real.exp β ^ 2))
  tailoring_ambient_marking : OuterAmbientInclusionMarkingFamily tailoring.deformation tailoring.embedding
    (fun y => φ y.1 - Cplus ^ 2 * β ^ 2 / 2)
    (fun t => (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K)
  junction : CompletionIdentification holomorphic.deformation.target tailoring.deformation.source
  junction_scale : junction.scale = 1
  junction_shift : junction.shift = (fun _ => 0)
  junction_ribbon : ∀ x ∈ holomorphic.deformation.target.ribbonDomain.domain.carrier,
    ((tailoring.embedding parameterZero).comp
      (tailoring.deformation.source.ambientDomain.domain.boundaryInclusion.comp
        tailoring.deformation.source.ribbonEmbedding)).map (junction.ribbonEquiv.map x) =
    ((holomorphic.embedding parameterOne).comp
      (holomorphic.deformation.target.ambientDomain.domain.boundaryInclusion.comp
        holomorphic.deformation.target.ribbonEmbedding)).map x
  junction_ambient : ∀ x ∈ holomorphic.deformation.target.ambientDomain.domain.carrier,
    ∃ y ∈ tailoring.deformation.source.ambientDomain.domain.carrier,
      (tailoring.embedding parameterZero).map y = (holomorphic.embedding parameterOne).map x ∧
      junction.ambientEquiv (holomorphic.deformation.target.ambientCompletion.inclusion.map x) =
        tailoring.deformation.source.ambientCompletion.inclusion.map y

namespace PotentialTailoringMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus K : ℝ} {m : RoundingChoice}

/-- Append exactly the two produced deformations and their constructed junction. -/
def chain (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m) :
    ComparisonChain P.holomorphic.deformation.source P.tailoring.deformation.target :=
  ((Quiver.Path.nil.cons (ComparisonStep.deformation P.holomorphic.deformation)).cons
    (ComparisonStep.identification P.junction)).cons (ComparisonStep.deformation P.tailoring.deformation)

@[simp] theorem chain_length (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m) :
    P.chain.length = 3 := rfl

@[simp] theorem chain_vertices (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m) :
    P.chain.vertices = [P.holomorphic.deformation.source, P.holomorphic.deformation.target,
      P.tailoring.deformation.source, P.tailoring.deformation.target] := rfl

end PotentialTailoringMarkedPrefix
end FsFltz
