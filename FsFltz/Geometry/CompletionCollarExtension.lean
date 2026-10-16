import FsFltz.Geometry.CompletionCollar

/-!
# Local extension of intrinsic collars to compact presentations

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–189; and `sec:lean`, lines 788–814.

For supplied completions, their compact inclusions are diffeomorphisms onto
open images. Intersecting those images with the intrinsic collar comparison
constructs open neighborhoods of every compact boundary point in the original
extension manifolds. The comparison on these neighborhoods, including its
smooth inverse and its compact-carrier preservation, is constructed from the
actual end maps. No negative-radius agreement is an input.

Extending this local comparison through the compact interior and constructing
jointly smooth choices for varying completions remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

/-- The native boundary presentation is compact because it embeds onto the
closed frontier of the compact carrier. -/
theorem isCompact_boundary {d : ℕ} (D : CompactDomain d) :
    IsCompact (univ : Set D.boundary.Point) := by
  rw [D.boundaryInclusion.embedding.isCompact_iff, image_univ, D.boundary_range]
  exact D.compact.of_isClosed_subset isClosed_frontier D.compact.isClosed.frontier_subset

end CompactDomain

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- The actual open image of the compact inclusion's smooth extension. -/
def inclusionImage : TopologicalSpace.Opens C.ambient.manifold.Point :=
  C.inclusion_isLocalDiffeomorph.image

def inclusionInImage (x : D.domain.extension.Point) : C.inclusionImage :=
  ⟨C.inclusion.map x, ⟨x, rfl⟩⟩

private theorem inclusionInImage_bijective : Function.Bijective C.inclusionInImage := by
  constructor
  · intro x y h
    exact C.inclusion.embedding.injective (congrArg Subtype.val h)
  · rintro ⟨z, x, rfl⟩
    exact ⟨x, rfl⟩

private def inclusionEquiv : D.domain.extension.Point ≃ C.inclusionImage :=
  Equiv.ofBijective C.inclusionInImage C.inclusionInImage_bijective

/-- The unique compact-extension representative of a point in the open image. -/
def inclusionCoordinates (z : C.inclusionImage) : D.domain.extension.Point :=
  C.inclusionEquiv.symm z

@[simp] theorem inclusionCoordinates_inclusionInImage (x : D.domain.extension.Point) :
    C.inclusionCoordinates (C.inclusionInImage x) = x :=
  C.inclusionEquiv.symm_apply_apply x

@[simp] theorem inclusionInImage_inclusionCoordinates (z : C.inclusionImage) :
    C.inclusionInImage (C.inclusionCoordinates z) = z :=
  C.inclusionEquiv.apply_symm_apply z

@[simp] theorem inclusionMap_inclusionCoordinates (z : C.inclusionImage) :
    C.inclusion.map (C.inclusionCoordinates z) = z.val :=
  congrArg Subtype.val (C.inclusionInImage_inclusionCoordinates z)

theorem contMDiff_inclusionCoordinates :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ C.inclusionCoordinates := by
  intro z
  let l := C.inclusion_isLocalDiffeomorph (C.inclusionCoordinates z)
  have hi : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ l.localInverse z.val := by
    rw [← C.inclusionMap_inclusionCoordinates z]
    exact l.localInverse_contMDiffAt
  apply (hi.comp z (contMDiff_subtype_val z)).congr_of_eventuallyEq
  have ht : Tendsto (Subtype.val : C.inclusionImage → C.ambient.manifold.Point)
      (𝓝 z) (𝓝 (C.inclusion.map (C.inclusionCoordinates z))) := by
    rw [C.inclusionMap_inclusionCoordinates]
    exact continuous_subtype_val.continuousAt
  filter_upwards [l.localInverse_eventuallyEq_right.comp_tendsto ht] with y hy
  apply C.inclusion.embedding.injective
  exact (C.inclusionMap_inclusionCoordinates y).trans hy.symm

/-- The compact inclusion is inverted on its actual open image; regularity
of the selected inverse follows from the inverse function theorem. -/
def inclusionDiffeomorph :
    Diffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      D.domain.extension.Point C.inclusionImage ∞ where
  __ := C.inclusionEquiv
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff C.inclusionImage
    C.inclusionInImage).mp C.inclusion.map.contMDiff
  contMDiff_invFun := C.contMDiff_inclusionCoordinates

variable {e : ℕ} {E : LiouvilleDomain e} (C' : Completion E)

/-- End coordinates on which both compact-extension inclusions can be
inverted. This is an actual open subset, constructed rather than assumed. -/
def compactCollarCoordinates (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    TopologicalSpace.Opens (D.domain.boundary.Point × ℝ) where
  carrier := C.endMap ⁻¹' C.inclusionImage ∩
    (fun q => C'.endMap (b q.1, q.2)) ⁻¹' C'.inclusionImage
  is_open' := (C.inclusionImage.isOpen.preimage C.smooth_endMap.continuous).inter
    (C'.inclusionImage.isOpen.preimage
      (C'.smooth_endMap.comp
        ((b.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)).continuous)

/-- A neighborhood of the whole compact boundary in the original extension
manifold, obtained by pulling the constructed end neighborhood back. -/
def compactCollarNeighborhood (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    TopologicalSpace.Opens D.domain.extension.Point where
  carrier := C.inclusion.map ⁻¹' (C.endMap '' C.compactCollarCoordinates C' b)
  is_open' := (C.endMap_isLocalDiffeomorph.isOpenMap _
    (C.compactCollarCoordinates C' b).isOpen).preimage C.inclusion.map.contMDiff.continuous

theorem mem_compactCollarCoordinates_zero
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) (x : D.domain.boundary.Point) :
    (x, 0) ∈ C.compactCollarCoordinates C' b := by
  constructor
  · exact ⟨D.domain.boundaryInclusion.map x, (C.endMap_zero x).symm⟩
  · exact ⟨E.domain.boundaryInclusion.map (b x), (C'.endMap_zero (b x)).symm⟩

/-- Every compact boundary point belongs to the constructed open neighborhood. -/
theorem boundary_mem_compactCollarNeighborhood
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) (x : D.domain.boundary.Point) :
    D.domain.boundaryInclusion.map x ∈ C.compactCollarNeighborhood C' b :=
  ⟨(x, 0), C.mem_compactCollarCoordinates_zero C' b x, C.endMap_zero x⟩

def compactCollarInBasin (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) : C.escapingBasin :=
  ⟨C.inclusion.map z.val, by
    obtain ⟨q, _, he⟩ := z.property
    exact ⟨q, he⟩⟩

def compactCollarEndCoordinates (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) : D.domain.boundary.Point × ℝ :=
  C.endCoordinates (C.compactCollarInBasin C' b z)

@[simp] theorem endMap_compactCollarEndCoordinates
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C.endMap (C.compactCollarEndCoordinates C' b z) = C.inclusion.map z.val :=
  C.endMap_endCoordinates (C.compactCollarInBasin C' b z)

theorem compactCollarEndCoordinates_mem
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C.compactCollarEndCoordinates C' b z ∈ C.compactCollarCoordinates C' b := by
  obtain ⟨q, hq, he⟩ := z.property
  have hq' := C.endMap_injective ((C.endMap_compactCollarEndCoordinates C' b z).trans he.symm)
  rwa [hq']

theorem contMDiff_compactCollarEndCoordinates
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.compactCollarEndCoordinates C' b) := by
  have hs : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (C.compactCollarInBasin C' b) :=
    (ContMDiff.subtypeVal_comp_iff C.escapingBasin _).mp
      (C.inclusion.map.contMDiff.comp contMDiff_subtype_val)
  exact C.contMDiff_endCoordinates.comp hs

/-- The selected collar comparison lifted to the target's original compact
extension, on an actual neighborhood of the source compact boundary. -/
def compactCollarExtensionMap
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) : E.domain.extension.Point :=
  C'.inclusionCoordinates
    ⟨C'.endMap (b (C.compactCollarEndCoordinates C' b z).1,
      (C.compactCollarEndCoordinates C' b z).2),
      (C.compactCollarEndCoordinates_mem C' b z).2⟩

@[simp] theorem inclusionMap_compactCollarExtensionMap
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C'.inclusion.map (C.compactCollarExtensionMap C' b z) =
      C'.endMap (b (C.compactCollarEndCoordinates C' b z).1,
        (C.compactCollarEndCoordinates C' b z).2) :=
  C'.inclusionMap_inclusionCoordinates _

theorem compactCollarExtensionMap_mem
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C.compactCollarExtensionMap C' b z ∈ C'.compactCollarNeighborhood C b.symm := by
  let q := C.compactCollarEndCoordinates C' b z
  have hq := C.compactCollarEndCoordinates_mem C' b z
  refine ⟨(b q.1, q.2), ⟨hq.2, ?_⟩, ?_⟩
  · change C.endMap (b.symm (b q.1), q.2) ∈ C.inclusionImage
    have hsource : C.endMap q ∈ C.inclusionImage := hq.1
    simpa only [Diffeomorph.symm_apply_apply, Prod.eta] using hsource
  · exact (C.inclusionMap_compactCollarExtensionMap C' b z).symm

def compactCollarExtension
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) : C'.compactCollarNeighborhood C b.symm :=
  ⟨C.compactCollarExtensionMap C' b z, C.compactCollarExtensionMap_mem C' b z⟩

@[simp] theorem compactCollarEndCoordinates_extension
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C'.compactCollarEndCoordinates C b.symm (C.compactCollarExtension C' b z) =
      (b (C.compactCollarEndCoordinates C' b z).1,
        (C.compactCollarEndCoordinates C' b z).2) := by
  apply C'.endMap_injective
  rw [C'.endMap_compactCollarEndCoordinates]
  exact C.inclusionMap_compactCollarExtensionMap C' b z

theorem contMDiff_compactCollarExtensionMap
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (C.compactCollarExtensionMap C' b) := by
  apply C'.contMDiff_inclusionCoordinates.comp
  apply (ContMDiff.subtypeVal_comp_iff C'.inclusionImage _).mp
  exact C'.smooth_endMap.comp
    (((b.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd).comp
      (C.contMDiff_compactCollarEndCoordinates C' b))

theorem contMDiff_compactCollarExtension
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (C.compactCollarExtension C' b) :=
  (ContMDiff.subtypeVal_comp_iff (C'.compactCollarNeighborhood C b.symm) _).mp
    (C.contMDiff_compactCollarExtensionMap C' b)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem compactCollarExtension_symm_extension
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C'.compactCollarExtension C b.symm (C.compactCollarExtension C' b z) = z := by
  apply Subtype.ext
  apply C.inclusion.embedding.injective
  change C.inclusion.map (C'.compactCollarExtensionMap C b.symm
    (C.compactCollarExtension C' b z)) = C.inclusion.map z.val
  rw [C'.inclusionMap_compactCollarExtensionMap,
    C.compactCollarEndCoordinates_extension]
  simp only [Diffeomorph.symm_apply_apply, Prod.eta]
  exact C.endMap_compactCollarEndCoordinates C' b z

/-- The actual local compact-extension diffeomorphism. Both smooth directions
are constructed by inverting the inclusions and the intrinsic end maps. -/
def compactCollarDiffeomorph
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    Diffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
      (C.compactCollarNeighborhood C' b) (C'.compactCollarNeighborhood C b.symm) ∞ where
  toFun := C.compactCollarExtension C' b
  invFun := C'.compactCollarExtension C b.symm
  left_inv := C.compactCollarExtension_symm_extension C' b
  right_inv := by
    intro z
    exact C'.compactCollarExtension_symm_extension C b.symm z
  contMDiff_toFun := C.contMDiff_compactCollarExtension C' b
  contMDiff_invFun := C'.contMDiff_compactCollarExtension C b.symm

@[simp] theorem compactCollarEndCoordinates_boundary
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) (x : D.domain.boundary.Point) :
    C.compactCollarEndCoordinates C' b
      ⟨D.domain.boundaryInclusion.map x, C.boundary_mem_compactCollarNeighborhood C' b x⟩ =
        (x, 0) := by
  apply C.endMap_injective
  rw [C.endMap_compactCollarEndCoordinates, C.endMap_zero]

/-- The constructed compact collar map extends precisely the selected
boundary diffeomorphism on every boundary point. -/
@[simp] theorem compactCollarExtensionMap_boundary
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) (x : D.domain.boundary.Point) :
    C.compactCollarExtensionMap C' b
      ⟨D.domain.boundaryInclusion.map x, C.boundary_mem_compactCollarNeighborhood C' b x⟩ =
        E.domain.boundaryInclusion.map (b x) := by
  apply C'.inclusion.embedding.injective
  rw [C.inclusionMap_compactCollarExtensionMap,
    C.compactCollarEndCoordinates_boundary, C'.endMap_zero]

/-- Membership in the actual compact piece is exactly nonpositive radius
on every intrinsic end trajectory. -/
theorem endMap_mem_compact_iff (q : D.domain.boundary.Point × ℝ) :
    C.endMap q ∈ C.inclusion.map '' D.domain.carrier ↔ q.2 ≤ 0 := by
  constructor
  · intro hq
    by_contra hn
    exact C.overlap q.1 q.2 (lt_of_not_ge hn) hq
  · intro hq
    rcases lt_or_eq_of_le hq with hr | hr
    · exact C.endMap_mem_compact_of_neg q hr
    · rcases q with ⟨x, r⟩
      dsimp at hr
      subst r
      refine ⟨D.domain.boundaryInclusion.map x, ?_, (C.endMap_zero x).symm⟩
      apply D.domain.compact.isClosed.frontier_subset
      rw [← D.domain.boundary_range]
      exact ⟨x, rfl⟩

theorem compactCollar_mem_carrier_iff
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    z.val ∈ D.domain.carrier ↔ (C.compactCollarEndCoordinates C' b z).2 ≤ 0 := by
  rw [← C.endMap_mem_compact_iff, C.endMap_compactCollarEndCoordinates]
  exact C.inclusion.embedding.injective.mem_set_image.symm

/-- Both directions of compact-carrier preservation follow from the exact
radius equation. This is local geometry, with no global extension premise. -/
theorem compactCollarExtensionMap_mem_carrier_iff
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C.compactCollarExtensionMap C' b z ∈ E.domain.carrier ↔ z.val ∈ D.domain.carrier := by
  change (C.compactCollarExtension C' b z).val ∈ E.domain.carrier ↔ _
  rw [C'.compactCollar_mem_carrier_iff, C.compactCollar_mem_carrier_iff,
    C.compactCollarEndCoordinates_extension]

/-- The local extension agrees with the already constructed intrinsic
comparison throughout its neighborhood, including negative radii. -/
theorem compactCollarExtensionMap_intrinsic
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (z : C.compactCollarNeighborhood C' b) :
    C'.inclusion.map (C.compactCollarExtensionMap C' b z) =
      C.collarComparisonMap C' b (C.compactCollarInBasin C' b z) := by
  rw [C.inclusionMap_compactCollarExtensionMap]
  have he := C.collarComparisonMap_endInBasin C' b
    (C.compactCollarEndCoordinates C' b z).1 (C.compactCollarEndCoordinates C' b z).2
  simpa only [compactCollarEndCoordinates, Prod.eta, endInBasin_endCoordinates] using he.symm

/-- Every nonpositive radius belongs to the constructed coordinate
neighborhood, independently of the selected boundary diffeomorphism. -/
theorem mem_compactCollarCoordinates_of_nonpos
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : D.domain.boundary.Point × ℝ) (hq : q.2 ≤ 0) :
    q ∈ C.compactCollarCoordinates C' b := by
  constructor
  · obtain ⟨x, _, he⟩ := (C.endMap_mem_compact_iff q).mpr hq
    exact ⟨x, he⟩
  · obtain ⟨x, _, he⟩ := (C'.endMap_mem_compact_iff (b q.1, q.2)).mpr hq
    exact ⟨x, he⟩

/-- Compactness supplies one positive width on which the extended compact
inclusion can be inverted at every boundary point. All negative radii are
already in the compact piece, so the constructed tube extends to them too. -/
theorem exists_inclusionCollarWidth :
    ∃ δ : ℝ, 0 < δ ∧ univ ×ˢ Iio δ ⊆ C.endMap ⁻¹' C.inclusionImage := by
  let V := C.endMap ⁻¹' (C.inclusionImage : Set C.ambient.manifold.Point)
  have hV : IsOpen V := C.inclusionImage.isOpen.preimage C.smooth_endMap.continuous
  have hzero : univ ×ˢ ({0} : Set ℝ) ⊆ V := by
    rintro ⟨x, r⟩ ⟨_, hr⟩
    have hr' : r = 0 := hr
    subst r
    exact ⟨D.domain.boundaryInclusion.map x, (C.endMap_zero x).symm⟩
  obtain ⟨U, W, _, hW, hU, hzeroW, hUW⟩ := generalized_tube_lemma
    D.domain.isCompact_boundary isCompact_singleton hV hzero
  have hzW : (0 : ℝ) ∈ W := hzeroW (mem_singleton 0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hzW)
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨x, r⟩ ⟨_, hr⟩
  change r < δ at hr
  by_cases hr0 : r ≤ 0
  · obtain ⟨y, _, he⟩ := (C.endMap_mem_compact_iff (x, r)).mpr hr0
    exact ⟨y, he⟩
  · apply hUW
    refine ⟨hU (mem_univ x), hball ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (lt_of_not_ge hr0)]
      using hr

/-- One actual collar width works for every boundary diffeomorphism between
these fixed supplied completions. Thus no parameter-dependent shrinking is
needed for a family of such boundary maps. -/
theorem exists_common_compactCollarWidth :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ b : D.domain.boundary.SmoothEquiv E.domain.boundary,
        univ ×ˢ Iio δ ⊆
          (C.compactCollarCoordinates C' b : Set (D.domain.boundary.Point × ℝ)) := by
  obtain ⟨δ, hδ, hD⟩ := C.exists_inclusionCollarWidth
  obtain ⟨ε, hε, hE⟩ := C'.exists_inclusionCollarWidth
  refine ⟨min δ ε, lt_min hδ hε, ?_⟩
  intro b q hq
  have hr : q.2 < min δ ε := hq.2
  have hrD : q.2 ∈ Iio δ := lt_of_lt_of_le hr (min_le_left _ _)
  have hrE : (b q.1, q.2).2 ∈ Iio ε := lt_of_lt_of_le hr (min_le_right _ _)
  exact ⟨hD ⟨mem_univ _, hrD⟩, hE ⟨mem_univ _, hrE⟩⟩

/-- An actual point of the compact-extension collar, constructed from its
end coordinates by the proved smooth inverse of the inclusion. -/
def compactCollarPoint (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.compactCollarCoordinates C' b) : C.compactCollarNeighborhood C' b :=
  ⟨C.inclusionCoordinates ⟨C.endMap q.val, q.property.1⟩,
    ⟨q.val, q.property,
      (C.inclusionMap_inclusionCoordinates ⟨C.endMap q.val, q.property.1⟩).symm⟩⟩

@[simp] theorem compactCollarEndCoordinates_compactCollarPoint
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.compactCollarCoordinates C' b) :
    C.compactCollarEndCoordinates C' b (C.compactCollarPoint C' b q) = q.val := by
  apply C.endMap_injective
  rw [C.endMap_compactCollarEndCoordinates]
  exact C.inclusionMap_inclusionCoordinates ⟨C.endMap q.val, q.property.1⟩

theorem contMDiff_compactCollarPoint
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    (C.compactCollarPoint C' b) := by
  apply (ContMDiff.subtypeVal_comp_iff (C.compactCollarNeighborhood C' b) _).mp
  change ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    (fun q : C.compactCollarCoordinates C' b =>
      C.inclusionCoordinates ⟨C.endMap q.val, q.property.1⟩)
  apply C.contMDiff_inclusionCoordinates.comp
  apply (ContMDiff.subtypeVal_comp_iff C.inclusionImage _).mp
  exact C.smooth_endMap.comp contMDiff_subtype_val

set_option backward.isDefEq.respectTransparency false in
/-- The original compact-extension neighborhood has genuine smooth collar
coordinates on the constructed open coordinate domain. -/
def compactCollarParametrization
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    Diffeomorph ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
      (C.compactCollarCoordinates C' b) (C.compactCollarNeighborhood C' b) ∞ where
  toFun := C.compactCollarPoint C' b
  invFun := fun z => ⟨C.compactCollarEndCoordinates C' b z,
    C.compactCollarEndCoordinates_mem C' b z⟩
  left_inv := by
    intro q
    apply Subtype.ext
    exact C.compactCollarEndCoordinates_compactCollarPoint C' b q
  right_inv := by
    intro z
    apply Subtype.ext
    apply C.inclusion.embedding.injective
    change C.inclusion.map (C.inclusionCoordinates
      ⟨C.endMap (C.compactCollarEndCoordinates C' b z), _⟩) = C.inclusion.map z.val
    rw [C.inclusionMap_inclusionCoordinates]
    exact C.endMap_compactCollarEndCoordinates C' b z
  contMDiff_toFun := C.contMDiff_compactCollarPoint C' b
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (C.compactCollarCoordinates C' b) _).mp
      (C.contMDiff_compactCollarEndCoordinates C' b)

/-- The actual collar-extension map on this collar is the radius-preserving
boundary formula; the equation is an output of the construction. -/
theorem compactCollarExtensionMap_compactCollarPoint
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.compactCollarCoordinates C' b) :
    C'.inclusion.map (C.compactCollarExtensionMap C' b (C.compactCollarPoint C' b q)) =
      C'.endMap (b q.val.1, q.val.2) := by
  rw [C.inclusionMap_compactCollarExtensionMap,
    C.compactCollarEndCoordinates_compactCollarPoint]

/-- A selected positive collar width depends only on the fixed completions,
not on the boundary diffeomorphism or a parameter in a family of such maps. -/
def commonCompactCollarWidth : ℝ :=
  (C.exists_common_compactCollarWidth C').choose

theorem commonCompactCollarWidth_pos : 0 < C.commonCompactCollarWidth C' :=
  (C.exists_common_compactCollarWidth C').choose_spec.1

def commonCompactCollarStrip : TopologicalSpace.Opens (D.domain.boundary.Point × ℝ) :=
  ⟨univ ×ˢ Iio (C.commonCompactCollarWidth C'), isOpen_univ.prod isOpen_Iio⟩

theorem commonCompactCollarStrip_subset
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    (C.commonCompactCollarStrip C' : Set (D.domain.boundary.Point × ℝ)) ⊆
      C.compactCollarCoordinates C' b :=
  (C.exists_common_compactCollarWidth C').choose_spec.2 b

def commonCompactCollarPoint
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.commonCompactCollarStrip C') : C.compactCollarNeighborhood C' b :=
  C.compactCollarPoint C' b ⟨q.val, C.commonCompactCollarStrip_subset C' b q.property⟩

theorem contMDiff_commonCompactCollarPoint
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
      (C.commonCompactCollarPoint C' b) := by
  apply (C.contMDiff_compactCollarPoint C' b).comp
  exact (ContMDiff.subtypeVal_comp_iff (C.compactCollarCoordinates C' b) _).mp
    contMDiff_subtype_val

@[simp] theorem commonCompactCollarPoint_coordinates
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.commonCompactCollarStrip C') :
    C.compactCollarEndCoordinates C' b (C.commonCompactCollarPoint C' b q) = q.val :=
  C.compactCollarEndCoordinates_compactCollarPoint C' b _

theorem commonCompactCollarPoint_injective
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    Function.Injective (C.commonCompactCollarPoint C' b) := by
  intro q p he
  apply Subtype.ext
  simpa only [commonCompactCollarPoint_coordinates] using
    congrArg (C.compactCollarEndCoordinates C' b) he

/-- The local compact comparison on the genuinely common collar domain. -/
def commonCompactCollarComparison
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.commonCompactCollarStrip C') : E.domain.extension.Point :=
  C.compactCollarExtensionMap C' b (C.commonCompactCollarPoint C' b q)

theorem contMDiff_commonCompactCollarComparison
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary) :
    ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model e) ∞
      (C.commonCompactCollarComparison C' b) :=
  (C.contMDiff_compactCollarExtensionMap C' b).comp
    (C.contMDiff_commonCompactCollarPoint C' b)

@[simp] theorem inclusionMap_commonCompactCollarComparison
    (b : D.domain.boundary.SmoothEquiv E.domain.boundary)
    (q : C.commonCompactCollarStrip C') :
    C'.inclusion.map (C.commonCompactCollarComparison C' b q) =
      C'.endMap (b q.val.1, q.val.2) := by
  rw [commonCompactCollarComparison, C.inclusionMap_compactCollarExtensionMap,
    C.commonCompactCollarPoint_coordinates]

/-- A jointly smooth family of boundary diffeomorphisms gives a jointly
smooth family of actual local compact-extension comparisons on one fixed
collar domain. Completions are fixed here; no varying-completion extension
or compact-interior isotopy extension is asserted. -/
theorem contMDiff_commonCompactCollarComparison_family
    (b : ℝ → D.domain.boundary.SmoothEquiv E.domain.boundary)
    (hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (d - 1)))
      𝓘(ℝ, Model (e - 1)) ∞ (fun p : ℝ × D.domain.boundary.Point => b p.1 p.2)) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × C.commonCompactCollarStrip C' =>
        C.commonCompactCollarComparison C' (b p.1) p.2) := by
  let F : ℝ × C.commonCompactCollarStrip C' → C'.inclusionImage := fun p =>
    ⟨C'.endMap (b p.1 p.2.val.1, p.2.val.2),
      (C.commonCompactCollarStrip_subset C' (b p.1) p.2.property).2⟩
  have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × C.commonCompactCollarStrip C' => p.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hF : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model e) ∞ F := by
    apply (ContMDiff.subtypeVal_comp_iff C'.inclusionImage F).mp
    exact C'.smooth_endMap.comp
      ((hb.comp (contMDiff_fst.prodMk hq.fst)).prodMk hq.snd)
  have he : (fun p : ℝ × C.commonCompactCollarStrip C' =>
      C.commonCompactCollarComparison C' (b p.1) p.2) = C'.inclusionCoordinates ∘ F := by
    funext p
    apply C'.inclusion.embedding.injective
    rw [C.inclusionMap_commonCompactCollarComparison]
    exact (C'.inclusionMap_inclusionCoordinates (F p)).symm
  rw [he]
  exact C'.contMDiff_inclusionCoordinates.comp hF

end Completion
end FsFltz.Geometry
