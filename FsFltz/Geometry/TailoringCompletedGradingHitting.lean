import FsFltz.Geometry.TailoringCompletedGradingMarked
import FsFltz.Geometry.TailoringHittingRibbonFamily

/-!
# Actual completed grading on the retained coefficient-removal arrow

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2032–2045.
The native decreasing-coefficient family extends over the same actual
outer collars used by the retained hitting deformation. The ribbon,
markings and geometric arrow remain those already constructed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The actual native primitive throughout the retained coefficient-removal
edge, with the fully tailored map fixed and coefficient decreasing to zero. -/
def hittingNativePrimitiveFamily {n : ℕ} (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β K : ℝ) (t : ℝ) : (lgManifold n).Form 1 :=
  (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) (K * (1 - t))

theorem isSmoothFormFamily_hittingNativePrimitive {n : ℕ} (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (β K : ℝ) :
    (lgManifold n).IsSmoothFormFamily (hittingNativePrimitiveFamily I φ β K) :=
  isSmoothFormFamily_rankTwoPrimitive_decreasing (lgManifold n)
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1) K

/-- Named native shear family for the actual coefficient-removal edge.
Its endpoint tensors remain available to the adjacent marked comparisons. -/
def hittingNativeMaslovFamily {n : ℕ} (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative
      (hittingNativePrimitiveFamily I φ β K t)) :=
  (potentialMaslovRepresentative hφ hc hlower).decreasingRankTwoPrimitiveFamily
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (tailoringFamily I β 1) (contMDiff_tailoringFamily_lgManifold I β 1) hπ K hK

/-- The same named native family on the actual retained outer domain. -/
def hittingNativeDomainMaslovFamily {n : ℕ} {D : CompactDomain (2 * n)}
    (ι : D.extension.SmoothEmbedding (lgManifold n))
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovFamily D.extension (fun t => D.extension.exteriorDerivative
      (D.extension.pullback (lgManifold n) ι.map (hittingNativePrimitiveFamily I φ β K t))) :=
  (hittingNativeMaslovFamily I hφ hc hlower β hπ K hK).pullbackPrimitiveEmbedding
    (fun _ ht => (isSmoothFormFamily_hittingNativePrimitive I hφ β K).slice ht) ι

namespace CompletedHittingRibbonFamily
variable {n : ℕ} {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
  {L : Parameter → LiouvilleStructure D}
  {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
  {b : Parameter → D.boundary.Point → ℝ}

/-- A native family grades this very retained hitting deformation;
the full completed fields are the specified cylindrical shear formulas. -/
theorem exists_completedGrading (H : CompletedHittingRibbonFamily D F L j b)
    (α : ℝ → D.extension.Form 1) (hα : D.extension.IsSmoothFormFamily α)
    (hαeq : ∀ t : Parameter, α t.val = (L t).primitive)
    (s : MaslovFamily D.extension (fun t => D.extension.exteriorDerivative (α t))) :
    ∃ f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension,
      Nonempty (GradedPairDeformation H.deformation
        (H.deformation.maslovFamilyRepresentative f parameterZero)
        (H.deformation.maslovFamilyRepresentative f parameterOne)) ∧
      (∀ t : Parameter, f.J t.val = H.ambient.completedNativeComplex α s.J t.val) ∧
      ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor α s.tensor t.val := by
  obtain ⟨f, hfJ, hfT⟩ := H.ambient.exists_completedMaslovFamily_with_native_formula α hα hαeq s
    H.deformation.completedSymplecticExtension H.deformation.completedSymplecticExtension_apply
  exact ⟨f, ⟨H.deformation.gradedOfMaslovFamily f⟩, hfJ, hfT⟩

/-- The actual slice representative of the retained hitting deformation
recovers its native cylindrical tensor on the whole compact domain. -/
theorem maslovFamilyRepresentative_tensor_eq_cylindrical_on_carrier
    (H : CompletedHittingRibbonFamily D F L j b)
    (f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (α : ℝ → D.extension.Form 1) (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n)
    (hf : ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor α τ t.val)
    (t : Parameter) (s : MaslovRepresentative D.extension
      (D.extension.exteriorDerivative (L t).primitive)) (hτ : τ t.val = s.tensor)
    (x : (H.ambient.collars t).localizedDomain.domain.extension.Point)
    (hx : x ∈ (H.ambient.collars t).localizedDomain.domain.carrier) :
    (H.deformation.maslovFamilyRepresentative f t).tensor x =
      ((H.ambient.collars t).cylindricalMaslovOfNative s).tensor x := by
  change pullbackSquaredTensor (H.ambient.collars t).localizedDomain.domain.extension
    (H.ambient.collars parameterZero).localizedDomain.domain.extension
    (H.ambient.completionPresentation t).equiv.symm (f.tensor t.val) x = _
  rw [hf t]
  exact H.ambient.pullback_completedNativeTensor_eq_cylindrical_on_carrier α τ t s hτ x hx

/-- Native analytic data grade the retained hitting arrow while retaining
the exact named native family and every completed slice formula. -/
theorem exists_completedGrading_of_native_with_formula (H : CompletedHittingRibbonFamily D F L j b)
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (ι : D.extension.SmoothEmbedding (lgManifold n))
    (hL : ∀ t : Parameter, (L t).primitive = D.extension.pullback (lgManifold n) ι.map
      (hittingNativePrimitiveFamily I φ β K t.val)) :
    let αD := fun t => D.extension.pullback (lgManifold n) ι.map
      (hittingNativePrimitiveFamily I φ β K t)
    let sD := hittingNativeDomainMaslovFamily ι I hφ hc hlower β hπ K hK
    ∃ f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension,
      Nonempty (GradedPairDeformation H.deformation
        (H.deformation.maslovFamilyRepresentative f parameterZero)
        (H.deformation.maslovFamilyRepresentative f parameterOne)) ∧
      (∀ t : Parameter, f.J t.val = H.ambient.completedNativeComplex αD sD.J t.val) ∧
      ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor αD sD.tensor t.val := by
  exact H.exists_completedGrading _
    (D.extension.isSmoothFormFamily_pullback_one (lgManifold n) ι.map _
      (isSmoothFormFamily_hittingNativePrimitive I hφ β K))
    (fun t => (hL t).symm) (hittingNativeDomainMaslovFamily ι I hφ hc hlower β hπ K hK)

/-- The actual decreasing primitive formula on the retained outer domain
constructs the required native input and hence the completed graded arrow. -/
theorem exists_completedGrading_of_native (H : CompletedHittingRibbonFamily D F L j b)
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (ι : D.extension.SmoothEmbedding (lgManifold n))
    (hL : ∀ t : Parameter, (L t).primitive = D.extension.pullback (lgManifold n) ι.map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
        (tailoringFamily I β 1) (K * (1 - t.val)))) :
    ∃ f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension,
      Nonempty (GradedPairDeformation H.deformation
        (H.deformation.maslovFamilyRepresentative f parameterZero)
        (H.deformation.maslovFamilyRepresentative f parameterOne)) := by
  obtain ⟨f, hf, _, _⟩ := H.exists_completedGrading_of_native_with_formula
    I hφ hc hlower β K hK hπ ι hL
  exact ⟨f, hf⟩

end CompletedHittingRibbonFamily
end FsFltz
