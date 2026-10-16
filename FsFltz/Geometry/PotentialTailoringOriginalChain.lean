import FsFltz.Geometry.PotentialTailoringOriginalJunction

/-!
# The retained original-K leg of the marked comparison prefix

Source: `geometric-part-fsf-proof.tex`, assembly, lines 2148–2158,
and `geoemtric-part-fsf.tex`, `def:chain`, lines 163–200. The prescribed
logarithmic grading belongs to the actual original leg retained here.
The remaining three-arrow marked prefix and its presentation junction are
literal steps on the same endpoint tuples. Arbitrary initial-choice
comparisons and grading of the remaining legs are separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Constructed output containing the supplied-K original endpoints,
their actual graded leg and the exact previously retained marked prefix. -/
structure PotentialTailoringOriginalMarkedPrefix {n : ℕ} (I : ToricInput n)
    (φ : RealSpace n → ℝ) (β Cplus Aminus originalK K : ℝ) (m : RoundingChoice) where
  marked : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m
  original : InitialPairData I (Real.exp β) originalK Aminus (Cplus ^ 2 * β ^ 2 / 2) m
  matching : InitialPairData I (Real.exp β) (K / Real.exp β ^ 2) Aminus
    (Cplus ^ 2 * β ^ 2 / 2) m
  originalMaslov : original.pair.Maslov
  matchingMaslov : matching.pair.Maslov
  original_chain : ComparisonChain original.pair matching.pair
  original_length : original_chain.length = 1
  original_prescribed : IsLogarithmicGrading original.ambientMarking.equiv originalMaslov
  matching_prescribed : IsLogarithmicGrading matching.ambientMarking.equiv matchingMaslov
  original_grading : GradedComparisonChain original.pair original_chain originalMaslov matchingMaslov
  junction : CompletionIdentification matching.pair marked.holomorphic.deformation.source
  junction_scale : junction.scale = 1
  junction_shift : junction.shift = (fun _ => 0)
  junction_ribbon : ∀ x ∈ matching.pair.ribbonDomain.domain.carrier,
    ((marked.holomorphic.embedding parameterZero).comp
      (marked.holomorphic.deformation.source.ambientDomain.domain.boundaryInclusion.comp
        marked.holomorphic.deformation.source.ribbonEmbedding)).map (junction.ribbonEquiv.map x) =
    (matching.domainEmbedding.comp
      (matching.pair.ambientDomain.domain.boundaryInclusion.comp matching.pair.ribbonEmbedding)).map x
  junction_ambient : ∀ x ∈ matching.pair.ambientDomain.domain.carrier,
    ∃ y ∈ marked.holomorphic.deformation.source.ambientDomain.domain.carrier,
      (marked.holomorphic.embedding parameterZero).map y = matching.domainEmbedding.map x ∧
      junction.ambientEquiv (matching.pair.ambientCompletion.inclusion.map x) =
        marked.holomorphic.deformation.source.ambientCompletion.inclusion.map y

namespace PotentialTailoringOriginalMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus originalK K : ℝ} {m : RoundingChoice}

/-- The actual five-arrow comparison, with literal adjoining endpoint tuples. -/
def chain (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) :
    ComparisonChain P.original.pair P.marked.tailoring.deformation.target :=
  (P.original_chain.cons (ComparisonStep.identification P.junction)).comp P.marked.chain

@[simp] theorem chain_length
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) :
    P.chain.length = 5 := by
  simp [chain, Quiver.Path.length_comp, P.original_length]

end PotentialTailoringOriginalMarkedPrefix

/-- Attach the constructed prescribed-grading original leg to this exact
retained marked prefix. No original chain or matching equivalence is assumed. -/
theorem PotentialTailoringMarkedPrefix.exists_original_augmentation {n : ℕ}
    {I : ToricInput n} {φ : RealSpace n → ℝ} {β Cplus Aminus originalK K : ℝ}
    {m : RoundingChoice} (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    {Aamb Afib : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β)
    (hset : RatioSetWellDefined I (Real.exp β)) (hK : K0 I (Real.exp β) ≤ originalK)
    (hKL : originalK ≤ K / Real.exp β ^ 2)
    (hfib : FiberEndBound I Aamb (Real.exp β) Afib) (hlevels : Afib < Aminus)
    (hm : GeometricAdmissibleRounding I (Real.exp β) originalK Aminus
      (Cplus ^ 2 * β ^ 2 / 2) m) :
    ∃ T : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m,
      T.marked = P := by
  obtain ⟨S, U, s, u, C, hC, hs, hu, ⟨hg⟩⟩ :=
    exists_originalParameter_gradedComparisonChain I hamb hR hset hK hKL hfib hlevels m hm
  obtain ⟨q, hscale, hshift, hribbon, hambient⟩ := P.exists_original_source_identification U
  exact ⟨{ marked := P, original := S, matching := U
           originalMaslov := s, matchingMaslov := u, original_chain := C
           original_length := hC, original_prescribed := hs, matching_prescribed := hu
           original_grading := hg, junction := q, junction_scale := hscale
           junction_shift := hshift, junction_ribbon := hribbon, junction_ambient := hambient }, rfl⟩

end FsFltz
