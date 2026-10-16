import FsFltz.Geometry.IntrinsicNativeIdentificationFamily
import FsFltz.Geometry.IntrinsicZeroRibbonFamily

/-!
# Joint native identifications in the actual localized family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 783–814. The collar-adapted compact presentation may move
interior points. Native identifications are therefore transported through
that very presentation. Both directions have jointly smooth extensions in
the real parameter, using the constructed compact atlas's ambient chart
extensions, rather than maps into a half-space beyond its boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

namespace DomainPresentationEquiv

variable {D E : CompactDomain 0}
local instance : ChartedSpace (Model 0) D.Point := D.zeroChartedSpace
local instance : ChartedSpace (Model 0) E.Point := E.zeroChartedSpace

/-- The actual extension presentation restricts to a native compact
diffeomorphism, using the proved ambient-chart smoothness bridge. -/
def zeroNativePointDiffeomorph (h : DomainPresentationEquiv D E) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) D.Point E.Point ∞ where
  toFun := fun x => ⟨h.extensionEquiv x.val, (h.mem_carrier_iff x.val).mpr x.property⟩
  invFun := fun y => ⟨h.extensionEquiv.symm y.val,
    (h.mem_carrier_iff _).mp (by rw [h.extensionEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv := fun x => Subtype.ext (h.extensionEquiv.symm_apply_apply x.val)
  right_inv := fun y => Subtype.ext (h.extensionEquiv.apply_symm_apply y.val)
  contMDiff_toFun := E.zero_contMDiff_iff_subtype_val.mpr
    (h.extensionEquiv.contMDiff.comp D.zero_contMDiff_subtype_val)
  contMDiff_invFun := D.zero_contMDiff_iff_subtype_val.mpr
    (h.extensionEquiv.symm.contMDiff.comp E.zero_contMDiff_subtype_val)

@[simp] theorem zeroNativePointDiffeomorph_val (h : DomainPresentationEquiv D E) (x : D.Point) :
    (h.zeroNativePointDiffeomorph x).val = h.extensionEquiv x.val := rfl

@[simp] theorem zeroNativePointDiffeomorph_symm_val (h : DomainPresentationEquiv D E) (x : E.Point) :
    (h.zeroNativePointDiffeomorph.symm x).val = h.extensionEquiv.symm x.val := rfl

end DomainPresentationEquiv

namespace LocalizedCompletionFamily

variable {D : CompactDomain 0}
  {L : Parameter → LiouvilleStructure D} (F : LocalizedCompletionFamily D L)
local instance : ChartedSpace (Model 0) D.Point := D.zeroChartedSpace
local instance (t : Parameter) : ChartedSpace (Model 0) (F.collars t).localizedDomain.domain.Point :=
  (F.collars t).localizedDomain.domain.zeroChartedSpace

/-- Both jointly smooth actual extension maps induce jointly smooth maps
on the fixed native compact manifold, including its boundary charts. -/
theorem jointlySmooth_zeroNativePointDiffeomorph :
    IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0)
      (fun t => (F.originalPresentation t).zeroNativePointDiffeomorph) := by
  constructor
  · apply D.zero_contMDiff_iff_subtype_val.mpr
    exact F.smooth_originalPresentation.comp
      (contMDiff_fst.prodMk (D.zero_contMDiff_subtype_val.comp contMDiff_snd))
  · apply D.zero_contMDiff_iff_subtype_val.mpr
    exact F.smooth_originalPresentation_symm.comp
      (contMDiff_fst.prodMk (D.zero_contMDiff_subtype_val.comp contMDiff_snd))

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The native identification after transport back through the actual
family presentation, expressed on the original fixed native manifold. -/
def zeroTransportedNativeDiffeomorph
    (e : Diffeomorph I 𝓘(ℝ, Model 0) M D.Point ∞) (t : ℝ) : Diffeomorph I I M M ∞ :=
  (e.trans (F.originalPresentation t).zeroNativePointDiffeomorph.symm).trans e.symm

/-- Both directions of the transported native identifications extend
jointly smoothly across the parameter endpoints. -/
theorem jointlySmooth_zeroTransportedNativeDiffeomorph
    (e : Diffeomorph I 𝓘(ℝ, Model 0) M D.Point ∞) :
    IsJointlySmoothDiffeomorphFamily I (F.zeroTransportedNativeDiffeomorph I e) := by
  have hs := F.jointlySmooth_zeroNativePointDiffeomorph
  constructor
  · exact e.symm.contMDiff.comp (hs.2.comp
      (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))
  · exact e.symm.contMDiff.comp (hs.1.comp
      (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)))

/-- The transported map is computed from the retained all-real ambient
inverse. This includes every native compact point. -/
theorem zeroTransportedNativeDiffeomorph_val
    (e : Diffeomorph I 𝓘(ℝ, Model 0) M D.Point ∞) (t : ℝ) (x : M) :
    (e (F.zeroTransportedNativeDiffeomorph I e t x)).val =
      (F.originalPresentation t).extensionEquiv.symm (e x).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The inverse uses the retained all-real ambient forward map. -/
theorem zeroTransportedNativeDiffeomorph_symm_val
    (e : Diffeomorph I 𝓘(ℝ, Model 0) M D.Point ∞) (t : ℝ) (x : M) :
    (e ((F.zeroTransportedNativeDiffeomorph I e t).symm x)).val =
      (F.originalPresentation t).extensionEquiv (e x).val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The same relative native map agrees with the actual constructed
localized compact presentation. It is not an unrelated smooth family. -/
theorem zeroTransportedNativeDiffeomorph_square
    (e : Diffeomorph I 𝓘(ℝ, Model 0) M D.Point ∞) (t : Parameter) (x : M) :
    (F.compactPresentation t).extensionEquiv
      (((e.trans (F.collars parameterZero).originalPointDiffeomorph_of_dimension_zero.symm)
        (F.zeroTransportedNativeDiffeomorph I e t.val x)).val) =
      ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val := by
  apply Subtype.ext
  apply Subtype.ext
  rw [F.original_projection]
  change (F.originalPresentation t.val).extensionEquiv
      (e (F.zeroTransportedNativeDiffeomorph I e t.val x)).val = (e x).val
  rw [F.zeroTransportedNativeDiffeomorph_val]
  exact (F.originalPresentation t.val).extensionEquiv.apply_symm_apply _

end LocalizedCompletionFamily
namespace IntrinsicZeroLiouville
open SmoothManifold
variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Native zero-dimensional ribbon families produce actual pair
deformations, including the completed families. The formula retains the
time-dependent embeddings and witnesses rather than replacing either by
its reference slice. -/
theorem exists_native_zero_pairDeformation_on_fixed_ambient_with_presentations
    (D : CompactDomain 2) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → D.boundary.Point)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : (sourceManifold M).IsSmoothIntervalMapFamily D.boundary j)
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x) :
    ∃ hprimitive : ∀ t x, x ∈ (compactDomain M).carrier →
      (compactDomain M).extension.pullback D.boundary
        (nativeRibbonEmbedding D (j t) (hj t)).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          ((liouvilleFamily μ) t).primitive x,
    ∃ (ambient : LocalizedCompletionFamily D L)
      (ribbon : LocalizedCompletionFamily (compactDomain M) (liouvilleFamily μ))
      (Q : PairDeformation 1),
      Q = D.localizedPairDeformation (n := 1) (compactDomain M) L (liouvilleFamily μ)
        (fun t => nativeRibbonEmbedding D (j t) (hj t)) b hL
        (primitiveFamily_smooth μ) hjs hb hpositive ambient ribbon hprimitive ∧
      (Q.pair = fun t => localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
        (ambient.collars t) (ribbon.collars t) (j t) (hj t) (b t)
        (hb.contMDiff_slice t) (hpositive t)) ∧
      ∀ t, (localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
        (ambient.collars t) (ribbon.collars t) (j t) (hj t) (b t)
        (hb.contMDiff_slice t) (hpositive t)).embeddedCore = range (j t) := by
  let hprimitive : ∀ t x, x ∈ (compactDomain M).carrier →
      (compactDomain M).extension.pullback D.boundary
        (nativeRibbonEmbedding D (j t) (hj t)).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x =
          ((liouvilleFamily μ) t).primitive x := fun t x _ => by
    change (sourceManifold M).pullback D.boundary
      (nativeRibbonEmbedding D (j t) (hj t)).map
      (fun y => b t y • D.boundaryForm (L t).primitive y) x = μ t x
    rw [positiveForm_eq_zero M 0 ((sourceManifold M).pullback D.boundary _ _),
      positiveForm_eq_zero M 0 (μ t)]
  obtain ⟨ambient, ribbon, Q, rfl⟩ :=
    D.exists_localized_pairDeformation_with_presentations (n := 1) (compactDomain M)
      L (liouvilleFamily μ) (fun t => nativeRibbonEmbedding D (j t) (hj t)) b
      hL (primitiveFamily_smooth μ) hjs hb hpositive hprimitive
  refine ⟨hprimitive, ambient, ribbon,
    D.localizedPairDeformation (n := 1) (compactDomain M) L (liouvilleFamily μ)
      (fun t => nativeRibbonEmbedding D (j t) (hj t)) b hL
      (primitiveFamily_smooth μ) hjs hb hpositive ambient ribbon hprimitive,
    rfl, rfl, ?_⟩
  intro t
  exact localizedZeroWitnessedPair_embeddedCore ⟨D, L t⟩ (μ t)
    (ambient.collars t) (ribbon.collars t) (j t) (hj t) (b t)
    (hb.contMDiff_slice t) (hpositive t)

end IntrinsicZeroLiouville

end FsFltz.Geometry
