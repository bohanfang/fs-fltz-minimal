import FsFltz.Geometry.HolomorphicMarkedGrading
import FsFltz.Geometry.OriginalInitialChoicePrefix
import FsFltz.Geometry.MaslovSameTensor

/-!
# The retained original-to-holomorphic marking on the whole completion

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030,
and `sec:assembly`, lines 2148–2158. The compact square and primitive
identity determine the actual global marking of the retained junction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Representatives prescribed by the same logarithmic marking determine
the same Maslov class, even when their compatible structures were chosen
independently. -/
theorem Geometry.IsLogarithmicGrading.class_eq {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2} {f : M.Point → LGSpace n}
    {s t : MaslovRepresentative M eta}
    (hs : IsLogarithmicGrading f s) (ht : IsLogarithmicGrading f t) :
    (Quot.mk _ s : MaslovClass M eta) = Quot.mk _ t := by
  apply s.class_eq_of_tensor_eq t
  funext x
  ext v
  exact (hs x v).trans (ht x v).symm

namespace PotentialTailoringOriginalMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus originalK K : ℝ} {m : RoundingChoice}

/-- The retained original-to-holomorphic identification is the identity in
the prescribed logarithmic coordinates on the entire completion. -/
theorem junction_marking
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) :
    P.junction.ambientEquiv.trans
      (P.marked.holomorphic_ambient_marking.marking parameterZero).equiv =
        P.matching.ambientMarking.equiv := by
  let M := P.marked.holomorphic_ambient_marking.marking parameterZero
  have hψzero : potentialPath (fun u => realSquaredNorm u / 2) φ 0 =
      (fun u => realSquaredNorm u / 2) := by
    funext u
    simp [potentialPath]
  have hαzero : (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ 0))
      (W I) (K / Real.exp β ^ 2) = lambdaKForm I (K / Real.exp β ^ 2) := by
    rw [hψzero, lambdaPotentialForm_quadratic]
    rfl
  have hpM : P.marked.holomorphic.deformation.source.ambientManifold.pullback
      (lgManifold n) M.equiv (lambdaKForm I (K / Real.exp β ^ 2)) =
        P.marked.holomorphic.deformation.source.ambientCompletion.ambient.primitive := by
    have hp := M.primitive
    change P.marked.holomorphic.deformation.source.ambientManifold.pullback
      (lgManifold n) M.equiv ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ 0))
        (W (I.alongCoefficientPath 0)) (K / Real.exp β ^ 2)) = _ at hp
    simpa only [PairDeformation.source, I.alongCoefficientPath_zero, hαzero] using hp
  apply P.matching.pair.ambientCompletion.equiv_eq_of_scaled_primitive_on_compact
    P.matching.ambient.toCompleteLiouvilleManifold
    (P.junction.ambientEquiv.trans M.equiv) P.matching.ambientMarking.equiv 1 1
  · change P.matching.pair.ambientManifold.pullback (lgManifold n)
      (M.equiv ∘ P.junction.ambientEquiv) (lambdaKForm I (K / Real.exp β ^ 2)) = _
    rw [P.matching.pair.ambientManifold.pullback_comp
      P.marked.holomorphic.deformation.source.ambientManifold (lgManifold n)
      (P.junction.ambientEquiv.mdifferentiable (by simp))
      (M.equiv.mdifferentiable (by simp)), hpM, P.junction.primitive, one_smul]
  · simpa only [one_smul] using P.matching.ambientMarking.primitive
  · intro x hx
    obtain ⟨y, hy, himage, hq⟩ := P.junction_ambient x hx
    change M.equiv (P.junction.ambientEquiv
      (P.matching.pair.ambientCompletion.inclusion.map x)) =
        P.matching.ambientMarking.equiv (P.matching.pair.ambientCompletion.inclusion.map x)
    rw [hq]
    exact (M.inclusion ⟨y, hy⟩).trans
      (himage.trans (P.matching.ambientMarking.inclusion ⟨x, hx⟩).symm)

/-- Pulling the prescribed target datum through this exact junction gives
a prescribed source datum and an actual graded identification. -/
theorem exists_prescribed_junction_lift
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (u : P.marked.holomorphic.deformation.source.Maslov)
    (hu : IsLogarithmicGrading
      (P.marked.holomorphic_ambient_marking.marking parameterZero).equiv u) :
    ∃ s : P.matching.pair.Maslov,
      IsLogarithmicGrading P.matching.ambientMarking.equiv s ∧
      Nonempty (GradedCompletionIdentification P.junction s u) := by
  let s := u.pullbackTo P.junction.ambientEquiv P.junction.pullback_symplecticForm
  refine ⟨s, ?_, (P.junction.gradedLift_iff_class_eq s u).mpr rfl⟩
  rw [← P.junction_marking]
  exact hu.pullbackTo P.junction.ambientEquiv
    (P.marked.holomorphic_ambient_marking.marking parameterZero).equiv
    P.junction.pullback_symplecticForm

/-- Any prescribed representative on either retained side gives a lift of
the actual original-to-holomorphic junction. -/
theorem prescribed_junction_lift
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (s : P.matching.pair.Maslov)
    (hs : IsLogarithmicGrading P.matching.ambientMarking.equiv s)
    (u : P.marked.holomorphic.deformation.source.Maslov)
    (hu : IsLogarithmicGrading
      (P.marked.holomorphic_ambient_marking.marking parameterZero).equiv u) :
    Nonempty (GradedCompletionIdentification P.junction s u) := by
  have hp := hu.pullbackTo P.junction.ambientEquiv
    (P.marked.holomorphic_ambient_marking.marking parameterZero).equiv
    P.junction.pullback_symplecticForm
  rw [P.junction_marking] at hp
  exact (P.junction.gradedLift_iff_class_eq s u).mpr (hs.class_eq hp)

/-- The first three arrows of the retained convenient comparison. -/
def holomorphicChain
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) :
    ComparisonChain P.original.pair P.marked.holomorphic.deformation.target :=
  (P.original_chain.cons (.identification P.junction)).cons
    (.deformation P.marked.holomorphic.deformation)

/-- The graded prefix is literally the prefix of the retained geometric
path, followed by its original normalization and tailoring arrows. -/
theorem chain_eq_holomorphicChain
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m) :
    P.chain = (P.holomorphicChain.cons (.identification P.marked.junction)).cons
      (.deformation P.marked.tailoring.deformation) := by
  simp only [chain, holomorphicChain, PotentialTailoringMarkedPrefix.chain,
    Quiver.Path.comp_cons, Quiver.Path.comp_nil]

/-- The actual retained original-coefficient, presentation-junction and
holomorphic arrows carry the original prescribed datum to a prescribed
holomorphic endpoint datum, with literal shared representatives. -/
theorem exists_graded_holomorphicChain
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hK : 0 ≤ K) :
    ∃ u : P.marked.holomorphic.deformation.target.Maslov,
      IsLogarithmicGrading
        (P.marked.holomorphic_ambient_marking.marking parameterOne).equiv u ∧
      P.holomorphicChain.length = 3 ∧
      Nonempty (GradedComparisonChain P.original.pair P.holomorphicChain P.originalMaslov u) := by
  obtain ⟨s, u, hs, hu, ⟨gh⟩⟩ := P.marked.exists_holomorphic_grading hφ hc hlower hK
  obtain ⟨gj⟩ := P.prescribed_junction_lift P.matchingMaslov P.matching_prescribed s hs
  refine ⟨u, hu, ?_, ⟨.cons (.cons P.original_grading (.identification gj)) (.deformation gh)⟩⟩
  simp only [holomorphicChain, Quiver.Path.length_cons, P.original_length]

/-- Every supplied original initial pair attaches to this exact graded
holomorphic prefix. Its three choice arrows and the three retained arrows
carry one prescribed source datum to a prescribed holomorphic endpoint. -/
theorem exists_graded_arbitrary_holomorphicChain
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    {Aamb Afib Afib' B E : ℝ} {p : RoundingChoice}
    (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β)
    (hset : RatioSetWellDefined I (Real.exp β)) (hKo : K0 I (Real.exp β) ≤ originalK)
    (hfib : FiberEndBound I Aamb (Real.exp β) Afib)
    (hfib' : FiberEndBound I Aamb (Real.exp β) Afib')
    (hB : Afib < B) (hAminus : Afib' < Aminus)
    (initial : InitialPairData I (Real.exp β) originalK B E p)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hK : 0 ≤ K) :
    ∃ C : InitialChoiceComparison initial P.original,
      C.targetDatum = P.originalMaslov ∧
      ∃ u : P.marked.holomorphic.deformation.target.Maslov,
        IsLogarithmicGrading
          (P.marked.holomorphic_ambient_marking.marking parameterOne).equiv u ∧
        (C.chain.comp P.holomorphicChain).length = 6 ∧
        Nonempty (GradedComparisonChain initial.pair (C.chain.comp P.holomorphicChain)
          C.sourceDatum u) := by
  obtain ⟨C, hC, hdatum, _hfour, _gfour, _height, _hpath⟩ :=
    P.exists_arbitrary_source_chain hamb hR hset hKo hfib hfib' hB hAminus initial
  obtain ⟨u, hu, hthree, ⟨g⟩⟩ := P.exists_graded_holomorphicChain hφ hc hlower hK
  have gC : GradedComparisonChain initial.pair C.chain C.sourceDatum P.originalMaslov := by
    rw [← hdatum]
    exact C.graded
  refine ⟨C, hdatum, u, hu, ?_, ⟨gC.comp g⟩⟩
  simp only [Quiver.Path.length_comp, hC, hthree]

end PotentialTailoringOriginalMarkedPrefix
end FsFltz
