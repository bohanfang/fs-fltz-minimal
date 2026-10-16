import FsFltz.Geometry.CylindricalCompletion
import FsFltz.Geometry.LiouvilleCompletionFamily
import FsFltz.Geometry.FamilyFlowCollar

/-!
# Compatible localized completion assembly

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.

The actual compact presentation maps restrict to the localized extensions
when they carry the same two-sided collars. The cylinder completions are
constructed from those collars, rather than supplied by the caller.
The resulting family concerns the localized extension presentations; it
does not assert a completion embedding for an arbitrary original extension.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
set_option backward.isDefEq.respectTransparency false

namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D E : LiouvilleDomain d} (C : FlowCollar D) (C' : FlowCollar E)

/-- The native map from a localized extension to the original extension. -/
def originalInclusion : C.localizedDomain.domain.extension.SmoothEmbedding D.domain.extension :=
  { map := ⟨fun z => z.val.val, contMDiff_subtype_val.comp contMDiff_subtype_val⟩
    embedding := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    immersion := by
      intro z
      change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
        (fun y : C.localizedDomain.domain.extension.Point => y.val.val) z)
      erw [D.neighborhoodDomain.extension.mfderiv_comp_restrict_val D.domain.extension
        C.neighborhood z
        ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)),
        D.domain.extension.mfderiv_restrict_val]
      exact Function.injective_id }

@[simp] theorem originalInclusion_apply (z : C.localizedDomain.domain.extension.Point) :
    C.originalInclusion.map z = z.val.val := rfl

/-- The interior of the compact carrier is unchanged under the native open
symplectic-neighborhood inclusion. -/
theorem mem_neighborhoodInterior_iff (z : D.neighborhoodDomain.extension.Point) :
    z ∈ interior D.neighborhoodDomain.carrier ↔ z.val ∈ interior D.domain.carrier := by
  have he := D.symplecticNeighborhood.isOpen.isOpenMap_subtype_val
    |>.preimage_interior_eq_interior_preimage continuous_subtype_val D.domain.carrier
  change z ∈ interior (Subtype.val ⁻¹' D.domain.carrier) ↔
    z ∈ Subtype.val ⁻¹' interior D.domain.carrier
  exact Set.ext_iff.mp he z |>.symm

/-- A localized extension contains exactly the original compact interior
and the original points of its specified open collar. -/
theorem original_mem_localized (z : D.domain.extension.Point) :
    (∃ y : C.localizedDomain.domain.extension.Point, y.val.val = z) ↔
      z ∈ interior D.domain.carrier ∨
        ∃ q ∈ (C.strip : Set (D.domain.boundary.Point × ℝ)), (C.map q).val = z := by
  constructor
  · rintro ⟨y, rfl⟩
    rcases y.property with hy | hy
    · exact Or.inl ((mem_neighborhoodInterior_iff y.val).mp hy)
    · obtain ⟨q, he⟩ := hy
      exact Or.inr ⟨q.val, q.property, congrArg Subtype.val he⟩
  · intro hz
    rcases hz with hz | ⟨q, hq, rfl⟩
    · let y : D.neighborhoodDomain.extension.Point :=
        ⟨z, D.carrier_subset_symplecticNeighborhood (interior_subset hz)⟩
      exact ⟨⟨y, Or.inl ((mem_neighborhoodInterior_iff y).mpr hz)⟩, rfl⟩
    · exact ⟨⟨C.map q, Or.inr ⟨⟨q, hq⟩, rfl⟩⟩, rfl⟩

variable (h : DomainPresentationEquiv D.domain E.domain)
  (hwidth : C.width = C'.width)
  (hcollar : ∀ q ∈ (C.strip : Set (D.domain.boundary.Point × ℝ)),
    h.extensionEquiv (C.map q).val = (C'.map (h.boundaryEquiv q.1, q.2)).val)

include hwidth hcollar in
private theorem maps_localized (z : C.localizedDomain.domain.extension.Point) :
    ∃ y : C'.localizedDomain.domain.extension.Point,
      y.val.val = h.extensionEquiv z.val.val := by
  apply C'.original_mem_localized _ |>.mpr
  rcases (C.original_mem_localized z.val.val).mp ⟨z, rfl⟩ with hz | ⟨q, hq, hqz⟩
  · left
    have he := h.extensionEquiv.toHomeomorph.image_interior D.domain.carrier
    change h.extensionEquiv '' interior D.domain.carrier =
      interior (h.extensionEquiv '' D.domain.carrier) at he
    rw [h.carrier] at he
    rw [← he]
    exact ⟨z.val.val, hz, rfl⟩
  · right
    refine ⟨(h.boundaryEquiv q.1, q.2), ?_, ?_⟩
    · exact ⟨mem_univ _, by simpa only [← hwidth] using hq.2⟩
    · rw [← hcollar q hq, hqz]

private def localizedMap (z : C.localizedDomain.domain.extension.Point) :
    C'.localizedDomain.domain.extension.Point :=
  Classical.choose (C.maps_localized C' h hwidth hcollar z)

private theorem localizedMap_val (z : C.localizedDomain.domain.extension.Point) :
    (C.localizedMap C' h hwidth hcollar z).val.val = h.extensionEquiv z.val.val :=
  Classical.choose_spec (C.maps_localized C' h hwidth hcollar z)

private theorem smooth_localizedMap : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
    (C.localizedMap C' h hwidth hcollar) := by
  apply (ContMDiff.subtypeVal_comp_iff C'.neighborhood _).mp
  apply (ContMDiff.subtypeVal_comp_iff E.symplecticNeighborhood _).mp
  have he : (fun z => (C.localizedMap C' h hwidth hcollar z).val.val) =
      fun z => h.extensionEquiv (C.originalInclusion.map z) :=
    funext (C.localizedMap_val C' h hwidth hcollar)
  change ContMDiff _ _ ∞ (fun z => (C.localizedMap C' h hwidth hcollar z).val.val)
  rw [he]
  exact h.extensionEquiv.contMDiff.comp C.originalInclusion.map.contMDiff

private def reversePresentation : DomainPresentationEquiv E.domain D.domain :=
  { extensionEquiv := h.extensionEquiv.symm
    carrier := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← h.carrier] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simpa only [h.extensionEquiv.symm_apply_apply] using hx
      · intro hz
        refine ⟨h.extensionEquiv z, ?_, h.extensionEquiv.symm_apply_apply z⟩
        rw [← h.carrier]
        exact ⟨z, hz, rfl⟩
    boundaryEquiv := h.boundaryEquiv.symm
    boundary_square := by
      intro x
      apply h.extensionEquiv.injective
      change h.extensionEquiv (h.extensionEquiv.symm _) = h.extensionEquiv _
      rw [h.extensionEquiv.apply_symm_apply, h.boundary_square,
        h.boundaryEquiv.apply_symm_apply] }

include hwidth hcollar in
private theorem reverseCollar :
    ∀ q ∈ (C'.strip : Set (E.domain.boundary.Point × ℝ)),
      h.extensionEquiv.symm (C'.map q).val =
        (C.map (h.boundaryEquiv.symm q.1, q.2)).val := by
  intro q hq
  apply h.extensionEquiv.injective
  change h.extensionEquiv (h.extensionEquiv.symm _) = h.extensionEquiv _
  rw [h.extensionEquiv.apply_symm_apply]
  have hp : (h.boundaryEquiv.symm q.1, q.2) ∈ C.strip :=
    ⟨mem_univ _, by simpa only [hwidth] using hq.2⟩
  rw [hcollar _ hp, h.boundaryEquiv.apply_symm_apply]

private def localizedInverse :=
  C'.localizedMap C (reversePresentation h) hwidth.symm
    (C.reverseCollar C' h hwidth hcollar)

private theorem localized_inverse_left (z : C.localizedDomain.domain.extension.Point) :
    C.localizedInverse C' h hwidth hcollar (C.localizedMap C' h hwidth hcollar z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  dsimp only [localizedInverse]
  rw [C'.localizedMap_val, C.localizedMap_val]
  exact h.extensionEquiv.symm_apply_apply _

private theorem localized_inverse_right (z : C'.localizedDomain.domain.extension.Point) :
    C.localizedMap C' h hwidth hcollar (C.localizedInverse C' h hwidth hcollar z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  dsimp only [localizedInverse]
  rw [C.localizedMap_val, C'.localizedMap_val]
  exact h.extensionEquiv.apply_symm_apply _

private theorem localizedMap_bijective : Function.Bijective
    (C.localizedMap C' h hwidth hcollar) := by
  constructor
  · intro z w he
    apply Subtype.ext
    apply Subtype.ext
    apply h.extensionEquiv.injective
    change h.extensionEquiv z.val.val = h.extensionEquiv w.val.val
    simpa only [C.localizedMap_val C' h hwidth hcollar] using
      congrArg (fun y => y.val.val) he
  · intro y
    exact ⟨C.localizedInverse C' h hwidth hcollar y,
      C.localized_inverse_right C' h hwidth hcollar y⟩

/-- Exact collar compatibility restricts an actual compact presentation
to an actual presentation of the localized extension manifolds. -/
def localizedPresentation : DomainPresentationEquiv C.localizedDomain.domain
    C'.localizedDomain.domain where
  extensionEquiv :=
    { toFun := C.localizedMap C' h hwidth hcollar
      invFun := C.localizedInverse C' h hwidth hcollar
      left_inv := C.localized_inverse_left C' h hwidth hcollar
      right_inv := C.localized_inverse_right C' h hwidth hcollar
      contMDiff_toFun := C.smooth_localizedMap C' h hwidth hcollar
      contMDiff_invFun := C'.smooth_localizedMap C (reversePresentation h) hwidth.symm
        (C.reverseCollar C' h hwidth hcollar) }
  carrier := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (C.localizedMap C' h hwidth hcollar z).val.val ∈ E.domain.carrier
      rw [C.localizedMap_val C' h hwidth hcollar]
      rw [← h.carrier]
      exact ⟨z.val.val, hz, rfl⟩
    · intro hy
      obtain ⟨z, rfl⟩ := (C.localizedMap_bijective C' h hwidth hcollar).2 y
      refine ⟨z, ?_, rfl⟩
      change z.val.val ∈ D.domain.carrier
      change (C.localizedMap C' h hwidth hcollar z).val.val ∈ E.domain.carrier at hy
      rw [C.localizedMap_val C' h hwidth hcollar, ← h.carrier] at hy
      obtain ⟨w, hw, he⟩ := hy
      exact h.extensionEquiv.injective he ▸ hw
  boundaryEquiv := h.boundaryEquiv
  boundary_square := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (C.localizedMap_val C' h hwidth hcollar _).trans (h.boundary_square x)

@[simp] theorem localizedPresentation_val (z : C.localizedDomain.domain.extension.Point) :
    ((C.localizedPresentation C' h hwidth hcollar).extensionEquiv z).val.val =
      h.extensionEquiv z.val.val := C.localizedMap_val C' h hwidth hcollar z

/-- The localized primitive is literally the supplied original primitive
under the two native open inclusions, on the whole localized extension. -/
theorem original_primitive (z : C.localizedDomain.domain.extension.Point) :
    C.localizedDomain.liouville.primitive z = D.liouville.primitive z.val.val :=
  (D.neighborhoodStructure.restrict_primitive C.neighborhood
    C.carrier_subset_neighborhood z).trans (D.neighborhood_primitive z.val)

/-- The localized primitive is the actual smooth pullback of the original
primitive, rather than a new independently specified coefficient family. -/
theorem localized_primitive_pullback : C.localizedDomain.liouville.primitive =
    C.localizedDomain.domain.extension.pullback D.domain.extension C.originalInclusion.map
      D.liouville.primitive := by
  funext z
  rw [C.original_primitive]
  unfold SmoothManifold.pullback
  change D.liouville.primitive z.val.val =
    (D.liouville.primitive z.val.val).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
        (fun y : C.localizedDomain.domain.extension.Point => y.val.val) z)
  erw [D.neighborhoodDomain.extension.mfderiv_comp_restrict_val D.domain.extension
    C.neighborhood z
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)),
    D.domain.extension.mfderiv_restrict_val]
  ext vs
  rfl

/-- Transport on the localized extensions is exactly the restriction of
transport on the original compact extension presentations. -/
theorem localizedPresentation_pullback_primitive :
    C.localizedDomain.domain.extension.pullback C'.localizedDomain.domain.extension
      (C.localizedPresentation C' h hwidth hcollar).extensionEquiv
      C'.localizedDomain.liouville.primitive =
    C.localizedDomain.domain.extension.pullback D.domain.extension C.originalInclusion.map
      (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive) := by
  rw [C'.localized_primitive_pullback]
  rw [← C.localizedDomain.domain.extension.pullback_comp C'.localizedDomain.domain.extension
    E.domain.extension
    ((C.localizedPresentation C' h hwidth hcollar).extensionEquiv.contMDiff.mdifferentiable
      (by simp))
    (C'.originalInclusion.map.contMDiff.mdifferentiable (by simp))]
  have he : C'.originalInclusion.map ∘
      (C.localizedPresentation C' h hwidth hcollar).extensionEquiv =
      h.extensionEquiv ∘ C.originalInclusion.map := by
    funext z
    exact C.localizedPresentation_val C' h hwidth hcollar z
  rw [he]
  exact C.localizedDomain.domain.extension.pullback_comp D.domain.extension E.domain.extension
    (C.originalInclusion.map.contMDiff.mdifferentiable (by simp))
    (h.extensionEquiv.contMDiff.mdifferentiable (by simp)) E.liouville.primitive

include hwidth hcollar in
/-- The same finite collar square becomes the stretched cylindrical square
for every radius on the actual open end, including the negative overlap. -/
theorem localizedPresentation_cylindricalEnd (q : D.domain.boundary.Point × ℝ)
    (hq : -C.width < q.2) :
    (C.localizedPresentation C' h hwidth hcollar).extensionEquiv
      (C.cylindricalCompletion.endMap q) =
        C'.cylindricalCompletion.endMap (h.boundaryEquiv q.1, q.2) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((C.localizedPresentation C' h hwidth hcollar).extensionEquiv
      (C.cylindricalFlowEndMap q)).val.val =
    (C'.cylindricalFlowEndMap (h.boundaryEquiv q.1, q.2)).val.val
  rw [C.localizedPresentation_val C' h hwidth hcollar,
    C.cylindricalFlowEndMap_eq_endMap q hq,
    C'.cylindricalFlowEndMap_eq_endMap _ (by simpa only [← hwidth] using hq)]
  rw [C.endMap_val q hq,
    C'.endMap_val _ (by simpa only [← hwidth] using hq)]
  have hinverse : CollarStretch.inverse C.positive_width q.2 =
      CollarStretch.inverse C'.positive_width q.2 := by
    congr 1
  rw [← hinverse]
  exact hcollar _ ⟨mem_univ _, CollarStretch.inverse_mem_collar C.positive_width hq⟩

/-- Equal-width collars and their actual compact presentation square
construct a presentation of the two constructed cylindrical completions. -/
def cylindricalCompletionPresentation : CompletionPresentationEquiv
    C.cylindricalCompletion C'.cylindricalCompletion
      (C.localizedPresentation C' h hwidth hcollar) where
  equiv := (C.localizedPresentation C' h hwidth hcollar).extensionEquiv
  compact_square := fun _ _ => rfl
  end_square := fun x r hr =>
    C.localizedPresentation_cylindricalEnd C' h hwidth hcollar (x, r)
      (lt_of_lt_of_le (neg_lt_zero.mpr C.positive_width) hr)

end LiouvilleDomain.FlowCollar

/-- The constructed localized completion family of one fixed compact
Liouville family. All completion objects are the actual cylindrical
constructions from `collars`; the remaining fields record their compatible
presentations and proved regularity. This structure is an output of the
construction, not additional input to it. -/
structure LocalizedCompletionFamily {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D) where
  width : ℝ
  positive_width : 0 < width
  collars : ∀ t : Parameter, LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d)
  collar_width : ∀ t, (collars t).width = width
  originalPresentation : ℝ → DomainPresentationEquiv D D
  boundary_originalPresentation : ∀ t,
    (originalPresentation t).boundaryEquiv = Diffeomorph.refl _ _ ∞
  smooth_originalPresentation : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
    𝓘(ℝ, Model d) ∞
    (fun p : ℝ × D.extension.Point => (originalPresentation p.1).extensionEquiv p.2)
  smooth_originalPresentation_symm : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
    𝓘(ℝ, Model d) ∞
    (fun p : ℝ × D.extension.Point => (originalPresentation p.1).extensionEquiv.symm p.2)
  originalPresentation_zero : ∀ x, (originalPresentation 0).extensionEquiv x = x
  compactPresentation : ∀ t : Parameter, DomainPresentationEquiv
    (collars parameterZero).localizedDomain.domain (collars t).localizedDomain.domain
  boundary_compactPresentation_eq : ∀ t,
    (compactPresentation t).boundaryEquiv = (originalPresentation t.val).boundaryEquiv
  original_projection : ∀ t z, ((compactPresentation t).extensionEquiv z).val.val =
    (originalPresentation t.val).extensionEquiv z.val.val
  compactPresentation_zero : ∀ z, (compactPresentation parameterZero).extensionEquiv z = z
  compactPrimitive_smooth : (collars parameterZero).localizedDomain.domain.extension.IsSmoothIntervalFormFamily (fun t =>
      (collars parameterZero).localizedDomain.domain.extension.pullback
        (collars t).localizedDomain.domain.extension (compactPresentation t).extensionEquiv
          (collars t).localizedDomain.liouville.primitive)
  compactField_smooth : (collars parameterZero).localizedDomain.domain.extension.IsSmoothIntervalVectorFieldFamily (fun t =>
      (collars parameterZero).localizedDomain.domain.extension.pullbackVectorField
        (collars t).localizedDomain.domain.extension (compactPresentation t).extensionEquiv
          (collars t).localizedDomain.liouville.field)
  completionPresentation : ∀ t, CompletionPresentationEquiv
    (collars parameterZero).cylindricalCompletion (collars t).cylindricalCompletion
      (compactPresentation t)
  completionPresentation_eq : ∀ t,
    (completionPresentation t).equiv = (compactPresentation t).extensionEquiv
  completionPresentation_zero : ∀ z, (completionPresentation parameterZero).equiv z = z
  completedPrimitive_smooth : (collars parameterZero).localizedDomain.domain.extension.IsSmoothIntervalFormFamily (fun t =>
      (collars parameterZero).localizedDomain.domain.extension.pullback
        (collars t).localizedDomain.domain.extension (completionPresentation t).equiv
          (collars t).cylindricalCompletion.ambient.primitive)
  completedField_smooth : (collars parameterZero).localizedDomain.domain.extension.IsSmoothIntervalVectorFieldFamily (fun t =>
      (collars parameterZero).localizedDomain.domain.extension.pullbackVectorField
        (collars t).localizedDomain.domain.extension (completionPresentation t).equiv
          (collars t).cylindricalCompletion.ambient.field)

namespace LocalizedCompletionFamily

/-- The generated localized boundary map is the original boundary identity.
The stored natural boundary square avoids introducing a second presentation. -/
theorem boundary_compactPresentation {d : ℕ} {D : CompactDomain d}
    {L : Parameter → LiouvilleStructure D} (F : LocalizedCompletionFamily D L) :
    ∀ t, (F.compactPresentation t).boundaryEquiv =
      (Diffeomorph.refl _ _ ∞ : D.boundary.SmoothEquiv D.boundary) :=
  fun t => (F.boundary_compactPresentation_eq t).trans (F.boundary_originalPresentation t.val)

end LocalizedCompletionFamily

namespace CompactDomain

/-- A presented family of localized Liouville domains has smooth actual
transported fields once its transported primitives are smooth. Localization
provides global nondegeneracy and canonical contraction on these extensions,
so arbitrary off-carrier fields of the original domains are not involved. -/
theorem isSmoothIntervalVectorFieldFamily_localized_pullback
    {d : ℕ} (D : CompactDomain d) (L : Parameter → LiouvilleStructure D)
    (A : ∀ t : Parameter, LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d))
    (H : ∀ t : Parameter, DomainPresentationEquiv
      (A parameterZero).localizedDomain.domain (A t).localizedDomain.domain)
    (hα : (A parameterZero).localizedDomain.domain.extension.IsSmoothIntervalFormFamily
      (fun t => (A parameterZero).localizedDomain.domain.extension.pullback
        (A t).localizedDomain.domain.extension (H t).extensionEquiv
          (A t).localizedDomain.liouville.primitive)) :
    (A parameterZero).localizedDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
      (fun t => (A parameterZero).localizedDomain.domain.extension.pullbackVectorField
        (A t).localizedDomain.domain.extension (H t).extensionEquiv
          (A t).localizedDomain.liouville.field) := by
  let M := (A parameterZero).localizedDomain.domain.extension
  apply M.isSmoothIntervalVectorFieldFamily_of_liouvilleEquation
    (fun t => M.pullback (A t).localizedDomain.domain.extension (H t).extensionEquiv
      (A t).localizedDomain.liouville.primitive) hα
  · intro t x
    let N := (A t).localizedDomain.domain.extension
    let f := (H t).extensionEquiv
    let α := (A t).localizedDomain.liouville.primitive
    have hd := M.exteriorDerivative_pullback N f.toContMDiffMap
      α (A t).localizedDomain.liouville.smooth_primitive
    change M.exteriorDerivative (M.pullback N f α) =
      M.pullback N f (N.exteriorDerivative α) at hd
    rw [hd]
    exact M.nondegenerate_pullback_equiv N f _ x ((A t).localized_nondegenerate (f x))
  · intro t x v
    let N := (A t).localizedDomain.domain.extension
    let f := (H t).extensionEquiv
    let α := (A t).localizedDomain.liouville.primitive
    let Z := (A t).localizedDomain.liouville.field
    have hd := M.exteriorDerivative_pullback N f.toContMDiffMap
      α (A t).localizedDomain.liouville.smooth_primitive
    change M.exteriorDerivative (M.pullback N f α) =
      M.pullback N f (N.exteriorDerivative α) at hd
    rw [hd]
    have he : (fun i : Fin 2 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x
        (![M.pullbackVectorField N f Z x, v] i)) =
        ![Z (f x), mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x v] := by
      funext i
      fin_cases i
      · exact M.mfderiv_pullbackVectorField N f Z x
      · rfl
    change (N.exteriorDerivative α (f x))
      (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x
        (![M.pullbackVectorField N f Z x, v] i)) =
      evalOne α (f x) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f x v)
    rw [he]
    exact (A t).localized_contraction (f x) _

/-- Coherent equal-width collars and a smooth compact presentation family
assemble the actual cylindrical completions into a smooth family. Each
completed presentation is the lifted compact presentation itself. Joint
regularity is proved from the original primitive family and the exact collar
equations; pointwise completions are constructed, rather than hypotheses. -/
theorem exists_smooth_cylindricalCompletionFamily_of_flowCollarPresentations
    {d : ℕ} (D : CompactDomain d) (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (δ : ℝ) (hδ : 0 < δ)
    (A : ∀ t : Parameter, LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d))
    (hwidth : ∀ t, (A t).width = δ)
    (h : ℝ → DomainPresentationEquiv D D)
    (hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2))
    (hcollar : ∀ (t : Parameter), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      (h t.val).extensionEquiv ((A parameterZero).map q).val =
        ((A t).map ((h t.val).boundaryEquiv q.1, q.2)).val) :
    ∃ H : ∀ t : Parameter, DomainPresentationEquiv
        (A parameterZero).localizedDomain.domain (A t).localizedDomain.domain,
      (∀ t, (H t).boundaryEquiv = (h t.val).boundaryEquiv) ∧
      (∀ t z, ((H t).extensionEquiv z).val.val = (h t.val).extensionEquiv z.val.val) ∧
      (A parameterZero).localizedDomain.domain.extension.IsSmoothIntervalFormFamily
        (fun t => (A parameterZero).localizedDomain.domain.extension.pullback
          (A t).localizedDomain.domain.extension (H t).extensionEquiv
            (A t).localizedDomain.liouville.primitive) ∧
      ∃ p : ∀ t, CompletionPresentationEquiv (A parameterZero).cylindricalCompletion
          (A t).cylindricalCompletion (H t),
        (∀ t, (p t).equiv = (H t).extensionEquiv) ∧
        (A parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalFormFamily
          (fun t => (A parameterZero).cylindricalCompletion.ambient.manifold.pullback
            (A t).cylindricalCompletion.ambient.manifold (p t).equiv
              (A t).cylindricalCompletion.ambient.primitive) ∧
        (A parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalVectorFieldFamily
          (fun t => (A parameterZero).cylindricalCompletion.ambient.manifold.pullbackVectorField
            (A t).cylindricalCompletion.ambient.manifold (p t).equiv
              (A t).cylindricalCompletion.ambient.field) := by
  let hw := fun t : Parameter => (hwidth parameterZero).trans (hwidth t).symm
  have hc : ∀ (t : Parameter), ∀ q ∈ (A parameterZero).strip,
      (h t.val).extensionEquiv ((A parameterZero).map q).val =
        ((A t).map ((h t.val).boundaryEquiv q.1, q.2)).val := by
    intro t q hq
    exact hcollar t q ⟨hq.1, by simpa only [hwidth parameterZero] using hq.2⟩
  let H := fun t : Parameter =>
    (A parameterZero).localizedPresentation (A t) (h t.val) (hw t) (hc t)
  have horig := D.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
    D.extension (fun t => (h t).extensionEquiv) hs (fun t => (L t).primitive) hα
  have hrest := SmoothManifold.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
      (A parameterZero).localizedDomain.domain.extension D.extension
      (fun _ => (A parameterZero).originalInclusion.map)
      ((A parameterZero).originalInclusion.map.contMDiff.comp contMDiff_snd)
      (fun t => D.extension.pullback D.extension (h t.val).extensionEquiv (L t).primitive)
      horig
  have hpull : (A parameterZero).localizedDomain.domain.extension.IsSmoothIntervalFormFamily
      (fun t => (A parameterZero).localizedDomain.domain.extension.pullback
        (A t).localizedDomain.domain.extension (H t).extensionEquiv
          (A t).localizedDomain.liouville.primitive) := by
    have he : (fun t : Parameter => (A parameterZero).localizedDomain.domain.extension.pullback
        (A t).localizedDomain.domain.extension (H t).extensionEquiv
          (A t).localizedDomain.liouville.primitive) =
        fun t : Parameter => (A parameterZero).localizedDomain.domain.extension.pullback
          D.extension (A parameterZero).originalInclusion.map
          (D.extension.pullback D.extension (h t.val).extensionEquiv (L t).primitive) := by
      funext t
      exact (A parameterZero).localizedPresentation_pullback_primitive (A t)
        (h t.val) (hw t) (hc t)
    rw [he]
    exact hrest
  let p := fun t : Parameter =>
    (A parameterZero).cylindricalCompletionPresentation (A t) (h t.val) (hw t) (hc t)
  have hsquare : ∀ (t : Parameter), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ (A parameterZero).localizedDomain.domain.carrier,
        (A parameterZero).cylindricalCompletion.inclusion.map x =
          (A parameterZero).cylindricalCompletion.endMap q →
        (A t).cylindricalCompletion.inclusion.map ((H t).extensionEquiv x) =
          (A t).cylindricalCompletion.endMap ((H t).boundaryEquiv q.1, q.2) := by
    intro t q hq x _hx he
    change x = (A parameterZero).cylindricalCompletion.endMap q at he
    change (H t).extensionEquiv x = _
    rw [he]
    exact (A parameterZero).localizedPresentation_cylindricalEnd (A t) (h t.val)
      (hw t) (hc t) q (by simpa only [hwidth parameterZero] using hq.2.1)
  obtain ⟨α, hαext, hαeq⟩ := hpull
  obtain ⟨hprimitive, hfield⟩ := Completion.isSmoothIntervalPrimitiveAndFieldFamily_of_collar_presentations
      (A parameterZero).cylindricalCompletion
      (fun t => (A t).localizedDomain) (fun t => (A t).cylindricalCompletion)
      H p α hαext hαeq δ hδ hsquare
  exact ⟨H, (fun _ => rfl), (fun t => (A parameterZero).localizedPresentation_val
    (A t) (h t.val) (hw t) (hc t)), ⟨α, hαext, hαeq⟩, p, (fun _ => rfl),
      hprimitive, hfield⟩

end CompactDomain

namespace LocalizedCompletionFamily

/-- Assemble the output record from actual compatible collar and compact
presentation data. The regularity fields are proved by the earlier family
consumer, not supplied to this construction. -/
def ofCollarPresentations {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (δ : ℝ) (hδ : 0 < δ)
    (A : ∀ t : Parameter, LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d))
    (hwidth : ∀ t, (A t).width = δ)
    (h : ℝ → DomainPresentationEquiv D D)
    (hboundary : ∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞)
    (hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2))
    (hsinv : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv.symm p.2))
    (hzero : ∀ x, (h 0).extensionEquiv x = x)
    (hcollar : ∀ (t : Parameter) q, q ∈ univ ×ˢ Ioo (-δ) δ →
      (h t.val).extensionEquiv ((A parameterZero).map q).val = ((A t).map q).val) :
    FsFltz.Geometry.LocalizedCompletionFamily D L := by
  have hc : ∀ (t : Parameter), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      (h t.val).extensionEquiv ((A parameterZero).map q).val =
        ((A t).map ((h t.val).boundaryEquiv q.1, q.2)).val := by
    intro t q hq
    rw [hboundary]
    exact hcollar t q hq
  let assembly := D.exists_smooth_cylindricalCompletionFamily_of_flowCollarPresentations
    L hα δ hδ A hwidth h hs hc
  let H := Classical.choose assembly
  have hH := Classical.choose_spec assembly
  have hHboundary := hH.1
  have hHprojection := hH.2.1
  have hcompact := hH.2.2.1
  let p := Classical.choose hH.2.2.2
  have hp := Classical.choose_spec hH.2.2.2
  have hpH := hp.1
  have hHzero : ∀ z, (H parameterZero).extensionEquiv z = z := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rw [hHprojection]
    exact hzero z.val.val
  exact
    { width := δ
      positive_width := hδ
      collars := A
      collar_width := hwidth
      originalPresentation := h
      boundary_originalPresentation := hboundary
      smooth_originalPresentation := hs
      smooth_originalPresentation_symm := hsinv
      originalPresentation_zero := hzero
      compactPresentation := H
      boundary_compactPresentation_eq := hHboundary
      original_projection := hHprojection
      compactPresentation_zero := hHzero
      compactPrimitive_smooth := hcompact
      compactField_smooth := D.isSmoothIntervalVectorFieldFamily_localized_pullback L A H hcompact
      completionPresentation := p
      completionPresentation_eq := hpH
      completionPresentation_zero := fun z =>
        (congrArg (fun f => f z) (hpH parameterZero)).trans (hHzero z)
      completedPrimitive_smooth := hp.2.1
      completedField_smooth := hp.2.2 }

end LocalizedCompletionFamily

namespace CompactDomain

/-- Smooth interval primitives on a fixed compact domain construct their
own compatible localized completions, together with smooth compact and
completed presentations. The actual original compact primitive, field and
boundary form are retained by the native inclusions.

No collars, pointwise completions, presentation compatibility or completed
regularity are hypotheses. This concerns the localized extension
presentations and does not assert a completion embedding of an arbitrary
original extension or the toric geometric comparison theorem. -/
def localizedCompletionFamily {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    FsFltz.Geometry.LocalizedCompletionFamily D L := by
  let flow := D.exists_liouvilleFamily_flowCollarPresentation L hα
  let δ := Classical.choose flow
  have hδ := (Classical.choose_spec flow).1
  let collarData := (Classical.choose_spec flow).2
  let A := Classical.choose collarData
  have hA := Classical.choose_spec collarData
  let h := Classical.choose hA.2
  have hh := Classical.choose_spec hA.2
  exact LocalizedCompletionFamily.ofCollarPresentations D L hα δ hδ A hA.1 h
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2

/-- Existence of the constructed one-domain localized completion family.
Its only input regularity is smoothness of the original compact primitives. -/
theorem exists_smooth_localizedCompletionFamily_of_liouvilleFamily
    {d : ℕ} (D : CompactDomain d) (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    Nonempty (FsFltz.Geometry.LocalizedCompletionFamily D L) :=
  ⟨D.localizedCompletionFamily L hα⟩

end CompactDomain
end FsFltz.Geometry
