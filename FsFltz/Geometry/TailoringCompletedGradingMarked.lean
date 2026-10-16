import FsFltz.Geometry.TailoringCompletedGradingLocalized
import FsFltz.Geometry.PotentialTailoringMarkedChain
import FsFltz.Geometry.PairDeformationMaslovFamily

/-!
# Grading on the same retained outer-marked deformation

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2025–2030.
The constructed outer completed family pulls through the retained actual
markings. The output is indexed by the original pair deformation and has
full formulas for its complex field and tensor at every interval time.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
namespace OuterAmbientInclusionMarkingFamily
variable {n : ℕ} {Q : PairDeformation n}
  {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
  {ρ : LGSpace n → ℝ} {α : Parameter → (lgManifold n).Form 1}

/-- The exact retained marking, expressed in the zero outer presentation. -/
def zeroOuterComparison (R : OuterAmbientInclusionMarkingFamily Q J ρ α) (t : Parameter) :
    Q.source.ambientManifold.SmoothEquiv
      (R.family.collars parameterZero).localizedDomain.domain.extension :=
  ((Q.ambientCompletionPresentation t).equiv.trans (R.marking t).equiv).trans
    (R.family.completionPresentation t).equiv.symm

/-- Actual native domain data construct a completed Maslov family on the
same retained deformation, with full all-slice formulas available to glue
its endpoint representatives to adjacent arrows. -/
theorem exists_completedMaslovFamily_of_domain
    (R : OuterAmbientInclusionMarkingFamily Q J ρ α)
    (αD : ℝ → R.domain.extension.Form 1) (hαD : R.domain.extension.IsSmoothFormFamily αD)
    (hαeq : ∀ t : Parameter, αD t.val = (R.liouville t).primitive)
    (s : MaslovFamily R.domain.extension (fun t => R.domain.extension.exteriorDerivative (αD t))) :
    ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
      (∀ t : Parameter, f.J t.val = pullbackAlmostComplex Q.source.ambientManifold
        (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
          (R.family.completedNativeComplex αD s.J t.val)) ∧
      ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor Q.source.ambientManifold
        (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
          (R.family.completedNativeTensor αD s.tensor t.val) := by
  let M := (R.family.collars parameterZero).localizedDomain.domain.extension
  obtain ⟨β, hβ, hβeq⟩ := R.family.completedPrimitive_smooth
  obtain ⟨g, hgJ, hgT⟩ := R.family.exists_completedMaslovFamily_with_native_formula αD hαD hαeq s
    (fun t => M.exteriorDerivative (β t)) (fun t => congrArg M.exteriorDerivative (hβeq t))
  have hprimitive (t : Parameter) : Q.source.ambientManifold.pullback M
      (R.zeroOuterComparison t) (β t.val) = Q.completedPrimitive t := by
    rw [hβeq t]
    rw [← Q.source.ambientManifold.pullback_comp M
      (R.family.collars t).localizedDomain.domain.extension
      ((R.zeroOuterComparison t).mdifferentiable (by simp))
      ((R.family.completionPresentation t).equiv.mdifferentiable (by simp))]
    have he : (R.family.completionPresentation t).equiv ∘ R.zeroOuterComparison t =
        (R.marking t).equiv ∘ (Q.ambientCompletionPresentation t).equiv := by
      funext x
      exact (R.family.completionPresentation t).equiv.apply_symm_apply _
    have hp : (Q.pair t).ambientManifold.pullback
        (R.family.collars t).localizedDomain.domain.extension (R.marking t).equiv
          (R.family.collars t).cylindricalCompletion.ambient.primitive =
        (Q.pair t).ambientCompletion.ambient.primitive := (R.marking t).primitive
    rw [he, Q.source.ambientManifold.pullback_comp (Q.pair t).ambientManifold
      (R.family.collars t).localizedDomain.domain.extension
      ((Q.ambientCompletionPresentation t).equiv.mdifferentiable (by simp))
      ((R.marking t).equiv.mdifferentiable (by simp)), hp]
    rfl
  have hform (t : Parameter) : Q.source.ambientManifold.pullback M
      (R.zeroOuterComparison t) (M.exteriorDerivative (β t.val)) = Q.completedSymplecticExtension t.val :=
    (Q.source.ambientManifold.exteriorDerivative_pullback M
      (R.zeroOuterComparison t).toContMDiffMap (β t.val) (hβ.slice t.property)).symm.trans
      ((congrArg Q.source.ambientManifold.exteriorDerivative (hprimitive t)).trans
        (Q.completedSymplecticExtension_apply t).symm)
  obtain ⟨f, hfJ, hfT⟩ := g.exists_localGermPullback R.zeroOuterComparison R.forward_smooth
    Q.completedSymplecticExtension hform
  refine ⟨f, ?_, ?_⟩
  · intro t
    rw [hfJ t, hgJ t]
  · intro t
    rw [hfT t, hgT t]

/-- The exact native primitive pulled to the retained outer domain. -/
def domainPrimitiveFamily {αN : ℝ → (lgManifold n).Form 1}
    (R : OuterAmbientInclusionMarkingFamily Q J ρ (fun t => αN t.val)) :
    ℝ → R.domain.extension.Form 1 :=
  fun t => R.domain.extension.pullback (lgManifold n) R.nativeEmbedding.map (αN t)

/-- The native ambient family determines domain data through the actual
embedding and its constructed open-image diffeomorphism. -/
def domainMaslovFamily {αN : ℝ → (lgManifold n).Form 1}
    (R : OuterAmbientInclusionMarkingFamily Q J ρ (fun t => αN t.val))
    (hαN : (lgManifold n).IsSmoothFormFamily αN)
    (s : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (αN t))) :
    MaslovFamily R.domain.extension
      (fun t => R.domain.extension.exteriorDerivative (R.domainPrimitiveFamily t)) :=
  s.pullbackPrimitiveEmbedding (fun _ ht => hαN.slice ht) R.nativeEmbedding

/-- The constructed native ambient family grades this very retained
deformation. Full formulas retain the native source and both endpoint
representatives for subsequent marked junction comparisons. -/
theorem exists_completedGrading {αN : ℝ → (lgManifold n).Form 1}
    (R : OuterAmbientInclusionMarkingFamily Q J ρ (fun t => αN t.val))
    (hαN : (lgManifold n).IsSmoothFormFamily αN)
    (s : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (αN t))) :
    ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
      Nonempty (GradedPairDeformation Q (Q.maslovFamilyRepresentative f parameterZero)
        (Q.maslovFamilyRepresentative f parameterOne)) ∧
      (∀ t : Parameter, f.J t.val = pullbackAlmostComplex Q.source.ambientManifold
        (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
          (R.family.completedNativeComplex R.domainPrimitiveFamily (R.domainMaslovFamily hαN s).J t.val)) ∧
      ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor Q.source.ambientManifold
        (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
          (R.family.completedNativeTensor R.domainPrimitiveFamily
            (R.domainMaslovFamily hαN s).tensor t.val) := by
  have hαD : R.domain.extension.IsSmoothFormFamily R.domainPrimitiveFamily :=
    R.domain.extension.isSmoothFormFamily_pullback_one (lgManifold n)
      R.nativeEmbedding.map αN hαN
  obtain ⟨f, hfJ, hfT⟩ := R.exists_completedMaslovFamily_of_domain R.domainPrimitiveFamily hαD
    (fun t => (R.native_primitive t).symm) (R.domainMaslovFamily hαN s)
  exact ⟨f, ⟨Q.gradedOfMaslovFamily f⟩, hfJ, hfT⟩

/-- Undoing the pair presentation leaves the actual outer marking, and
the constructed tensor recovers the cylindrical native tensor wherever
that marking lands in the retained outer compact carrier. -/
theorem maslovFamilyRepresentative_tensor_eq_cylindrical_of_marked_mem_carrier
    (R : OuterAmbientInclusionMarkingFamily Q J ρ α)
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (αD : ℝ → R.domain.extension.Form 1)
    (τ : ℝ → R.domain.extension.Point → SquaredCanonicalTensor n)
    (hf : ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor Q.source.ambientManifold
      (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
        (R.family.completedNativeTensor αD τ t.val))
    (t : Parameter) (s : MaslovRepresentative R.domain.extension
      (R.domain.extension.exteriorDerivative (R.liouville t).primitive))
    (hτ : τ t.val = s.tensor) (x : (Q.pair t).ambientManifold.Point)
    (hx : (R.marking t).equiv x ∈ (R.family.collars t).localizedDomain.domain.carrier) :
    (Q.maslovFamilyRepresentative f t).tensor x =
      pullbackSquaredTensor (Q.pair t).ambientManifold
        (R.family.collars t).localizedDomain.domain.extension (R.marking t).equiv
        ((R.family.collars t).cylindricalMaslovOfNative s).tensor x := by
  let e : (Q.pair t).ambientManifold.SmoothEquiv Q.source.ambientManifold :=
    (Q.ambientCompletionPresentation t).equiv.symm
  let m : (Q.pair t).ambientManifold.SmoothEquiv
      (R.family.collars t).localizedDomain.domain.extension := (R.marking t).equiv
  let c : (R.family.collars t).localizedDomain.domain.extension.SmoothEquiv
      (R.family.collars parameterZero).localizedDomain.domain.extension :=
    (R.family.completionPresentation t).equiv.symm
  have he : e.trans (R.zeroOuterComparison t) = m.trans c := by
    ext y
    change (R.family.completionPresentation t).equiv.symm
      ((R.marking t).equiv ((Q.ambientCompletionPresentation t).equiv
        ((Q.ambientCompletionPresentation t).equiv.symm y))) = _
    rw [(Q.ambientCompletionPresentation t).equiv.apply_symm_apply]
    rfl
  change pullbackSquaredTensor (Q.pair t).ambientManifold Q.source.ambientManifold e
    (f.tensor t.val) x = _
  rw [hf t, ← pullbackSquaredTensor_trans, he, pullbackSquaredTensor_trans]
  have hs := R.family.pullback_completedNativeTensor_eq_cylindrical_on_carrier
    αD τ t s hτ (m x) hx
  exact congrArg (fun T : SquaredCanonicalTensor n => T.compContinuousLinearMap
    (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) m x)) hs

end OuterAmbientInclusionMarkingFamily

namespace PotentialTailoringMarkedPrefix
variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
  {β Cplus Aminus K : ℝ} {m : RoundingChoice}

/-- Uniform Poisson positivity is the only remaining analytic input here:
the actual native shear and cylindrical extension grade the tailoring
arrow of this retained prefix, with its original endpoint representatives. -/
theorem exists_tailoring_grading (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K) :
    ∃ f : MaslovFamily P.tailoring.deformation.source.ambientManifold
      P.tailoring.deformation.completedSymplecticExtension,
      Nonempty (GradedPairDeformation P.tailoring.deformation
        (P.tailoring.deformation.maslovFamilyRepresentative f parameterZero)
        (P.tailoring.deformation.maslovFamilyRepresentative f parameterOne)) := by
  obtain ⟨f, hf, _, _⟩ := P.tailoring_ambient_marking.exists_completedGrading
    (isSmoothFormFamily_tailoringPrimitive I β K hφ)
    (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)
  exact ⟨f, hf⟩

end PotentialTailoringMarkedPrefix

/-- The geometric estimates produce actual grading on every retained
tailoring arrow beyond one threshold, uniformly before the base coefficient
and all retained rounded-domain choices. -/
theorem tailoringFamily_exists_uniform_retained_grading {n : ℕ}
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ K : ℝ, 0 ≤ K → ∀ Cplus Aminus : ℝ, ∀ m : RoundingChoice,
      ∀ P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m,
      ∃ f : MaslovFamily P.tailoring.deformation.source.ambientManifold
        P.tailoring.deformation.completedSymplecticExtension,
        Nonempty (GradedPairDeformation P.tailoring.deformation
          (P.tailoring.deformation.maslovFamilyRepresentative f parameterZero)
          (P.tailoring.deformation.maslovFamilyRepresentative f parameterOne)) := by
  obtain ⟨_d, _hd, _R, _hR, B, hB, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨B, hB, ?_⟩
  intro β hβ K hK Cplus Aminus m P
  exact P.exists_tailoring_grading hφ hc hlower
    (fun s hs y => (hπ β hβ s hs y
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)).1) hK

end FsFltz
