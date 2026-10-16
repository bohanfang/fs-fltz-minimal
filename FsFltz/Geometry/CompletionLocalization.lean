import FsFltz.Geometry.LiouvilleCollar

/-!
# A localized extension for cylindrical completion

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160, and `sec:lean`,
lines 783–814. The constructed Liouville collar supplies an open extension
consisting exactly of the compact interior and a two-sided collar. Its
exterior is precisely the positive collar. Restricting the domain to this
extension preserves its compact piece and boundary primitive.

The inverse collar coordinates are constructed by the inverse function
theorem. No completion or completed flow is an input. Extending the collar
primitive along an infinite cylinder and proving its complete flow remain
separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain

/-- The actual two-sided boundary flow collar and its defining geometric
properties, constructed from a compact Liouville domain below. -/
structure FlowCollar {d : ℕ} (D : LiouvilleDomain d) where
  width : ℝ
  positive_width : 0 < width
  flow : Flow ℝ D.neighborhoodDomain.extension.Point
  smooth_action : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
    (fun p : ℝ × D.neighborhoodDomain.extension.Point => flow p.1 p.2)
  solves : ∀ x : D.neighborhoodDomain.boundary.Point, ∀ t ∈ Ioo (-width) width,
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => flow s (D.neighborhoodDomain.boundaryInclusion.map x)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field
        (flow t (D.neighborhoodDomain.boundaryInclusion.map x))))
  injective : InjOn (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
    flow p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1))
    (univ ×ˢ Ioo (-width) width)
  localDiffeomorph : IsLocalDiffeomorphOn
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
      flow p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1))
    (univ ×ˢ Ioo (-width) width)
  side : ∀ x : D.neighborhoodDomain.boundary.Point, ∀ t ∈ Ioo (-width) width,
    flow t (D.neighborhoodDomain.boundaryInclusion.map x) ∈
      D.neighborhoodDomain.carrier ↔ t ≤ 0
  primitive : ∀ (x : D.neighborhoodDomain.boundary.Point) (r : ℝ),
    r ∈ Ioo (-width) width → ∀ (v : Model (d - 1)) (s : ℝ),
    evalOne D.neighborhoodStructure.primitive
      (flow r (D.neighborhoodDomain.boundaryInclusion.map x))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
          flow p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (x, r) (v, s)) =
      Real.exp r * evalOne (D.domain.boundaryForm D.liouville.primitive) x v

/-- Existence uses the proved collar construction, including its actual
side identity and primitive, with no collar hypotheses. -/
theorem nonempty_flowCollar {d : ℕ} (D : LiouvilleDomain d) : Nonempty (FlowCollar D) := by
  obtain ⟨δ, F, hδ, hF, hode, hinj, hdiff, _, hside, hprimitive⟩ :=
    D.exists_liouville_collar
  exact ⟨⟨δ, hδ, F, hF, hode, hinj, hdiff, hside, hprimitive⟩⟩

/-- Choose a collar produced by the foundation theorem. -/
def flowCollar {d : ℕ} (D : LiouvilleDomain d) : FlowCollar D :=
  Classical.choice D.nonempty_flowCollar

namespace FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

/-- The original boundary flow map, defined at all auxiliary flow times. -/
def map (p : D.neighborhoodDomain.boundary.Point × ℝ) :
    D.neighborhoodDomain.extension.Point :=
  C.flow p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)

@[simp] theorem map_zero (x : D.neighborhoodDomain.boundary.Point) :
    C.map (x, 0) = D.neighborhoodDomain.boundaryInclusion.map x :=
  C.flow.map_zero_apply _

/-- The native open source of the constructed collar. -/
def strip : TopologicalSpace.Opens (D.neighborhoodDomain.boundary.Point × ℝ) :=
  ⟨univ ×ˢ Ioo (-C.width) C.width, isOpen_univ.prod isOpen_Ioo⟩

theorem smooth_map : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, Model d) ∞ C.map :=
  C.smooth_action.comp (contMDiff_snd.prodMk
    (D.neighborhoodDomain.boundaryInclusion.map.contMDiff.comp contMDiff_fst))

/-- The collar map on its actual open strip. -/
def stripMap (p : C.strip) : D.neighborhoodDomain.extension.Point := C.map p.val

theorem smooth_stripMap : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, Model d) ∞ C.stripMap :=
  C.smooth_map.comp contMDiff_subtype_val

theorem isOpenEmbedding_stripMap : Topology.IsOpenEmbedding C.stripMap := by
  have hloc : IsLocalHomeomorph C.stripMap := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact C.localDiffeomorph.isLocalHomeomorphOn.comp
      C.strip.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn
      (fun p _ => p.property)
  exact hloc.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp C.injective)

/-- The actual open collar image. -/
def image : TopologicalSpace.Opens D.neighborhoodDomain.extension.Point :=
  ⟨range C.stripMap, C.isOpenEmbedding_stripMap.isOpen_range⟩

/-- The collar parametrization into its actual image. -/
def imageMap (p : C.strip) : C.image := ⟨C.stripMap p, ⟨p, rfl⟩⟩

private theorem imageMap_bijective : Function.Bijective C.imageMap := by
  constructor
  · intro p q he
    apply Subtype.ext
    exact C.injective p.property q.property (congrArg Subtype.val he)
  · rintro ⟨z, p, rfl⟩
    exact ⟨p, rfl⟩

private def imageEquiv : C.strip ≃ C.image :=
  Equiv.ofBijective C.imageMap C.imageMap_bijective

/-- Unique actual boundary and radius coordinates on the collar image. -/
def coordinates (z : C.image) : D.neighborhoodDomain.boundary.Point × ℝ :=
  (C.imageEquiv.symm z).val

theorem coordinates_mem_strip (z : C.image) : C.coordinates z ∈ C.strip :=
  (C.imageEquiv.symm z).property

@[simp] theorem coordinates_imageMap (p : C.strip) :
    C.coordinates (C.imageMap p) = p.val :=
  congrArg Subtype.val (C.imageEquiv.symm_apply_apply p)

@[simp] theorem map_coordinates (z : C.image) : C.map (C.coordinates z) = z.val :=
  congrArg Subtype.val (C.imageEquiv.apply_symm_apply z)

/-- The inverse is smooth because it agrees locally with the genuine
inverse-function-theorem inverse. Its regularity is not supplied as data. -/
theorem smooth_coordinates : ContMDiff 𝓘(ℝ, Model d)
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ C.coordinates := by
  intro z
  let l := C.localDiffeomorph ⟨C.coordinates z, C.coordinates_mem_strip z⟩
  have hi : ContMDiffAt 𝓘(ℝ, Model d)
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ l.localInverse z.val := by
    rw [← C.map_coordinates z]
    exact l.localInverse_contMDiffAt
  have hix : l.localInverse z.val = C.coordinates z := by
    rw [← C.map_coordinates z]
    exact l.localInverse_left_inv l.localInverse_mem_target
  have hn : ∀ᶠ y in 𝓝 z.val, l.localInverse y ∈ C.strip :=
    hi.continuousAt.preimage_mem_nhds (by
      rw [hix]
      exact C.strip.isOpen.mem_nhds (C.coordinates_mem_strip z))
  have hv : Tendsto (Subtype.val : C.image → D.neighborhoodDomain.extension.Point)
      (𝓝 z) (𝓝 z.val) := continuous_subtype_val.continuousAt
  have hr : ∀ᶠ y in 𝓝 z.val, C.map (l.localInverse y) = y := by
    have hr' := l.localInverse_eventuallyEq_right
    change C.map ∘ l.localInverse =ᶠ[𝓝 (C.map (C.coordinates z))] id at hr'
    rw [C.map_coordinates z] at hr'
    exact hr'
  apply (hi.comp z (contMDiff_subtype_val z)).congr_of_eventuallyEq
  filter_upwards [hv.eventually hn, hv.eventually hr] with y hy he
  exact C.injective (C.coordinates_mem_strip y) hy
    ((C.map_coordinates y).trans he.symm)

/-- An actual smooth equivalence between the open strip and the collar
image, with both directions obtained from the constructed flow. -/
def diffeomorph : Diffeomorph ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, Model d) C.strip C.image ∞ where
  __ := C.imageEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff C.image C.imageMap).mp C.smooth_stripMap
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff C.strip C.imageEquiv.symm).mp C.smooth_coordinates

/-- The open extension contains only the compact interior and the actual
two-sided collar. It discards unrelated points of the original extension. -/
def neighborhood : TopologicalSpace.Opens D.neighborhoodDomain.extension.Point :=
  ⟨interior D.neighborhoodDomain.carrier ∪ C.image,
    isOpen_interior.union C.image.isOpen⟩

theorem carrier_subset_neighborhood : D.neighborhoodDomain.carrier ⊆ C.neighborhood := by
  intro z hz
  by_cases hi : z ∈ interior D.neighborhoodDomain.carrier
  · exact Or.inl hi
  · have hf : z ∈ frontier D.neighborhoodDomain.carrier := by
      by_contra hn
      exact hi ((mem_interior_iff_notMem_frontier hz).mpr hn)
    obtain ⟨x, rfl⟩ : ∃ x, D.neighborhoodDomain.boundaryInclusion.map x = z := by
      rwa [← D.neighborhoodDomain.boundary_range] at hf
    exact Or.inr ⟨⟨(x, 0), mem_univ x, neg_lt_zero.mpr C.positive_width,
      C.positive_width⟩, C.map_zero x⟩

/-- Every exterior point of the localized extension has unique positive
collar coordinates; there are no other exterior components. -/
theorem neighborhood_diff_carrier :
    (C.neighborhood : Set D.neighborhoodDomain.extension.Point) \ D.neighborhoodDomain.carrier =
      C.map '' (univ ×ˢ Ioo (0 : ℝ) C.width) := by
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    rcases hz with hi | hi
    · exact (hn (interior_subset hi)).elim
    · obtain ⟨p, rfl⟩ := hi
      refine ⟨p.val, ⟨mem_univ _, ?_, p.property.2.2⟩, rfl⟩
      exact lt_of_not_ge (fun ht => hn ((C.side p.val.1 p.val.2 p.property.2).mpr ht))
  · rintro ⟨⟨x, r⟩, ⟨_, hr0, hrδ⟩, rfl⟩
    have hr : r ∈ Ioo (-C.width) C.width :=
      ⟨lt_trans (neg_lt_zero.mpr C.positive_width) hr0, hrδ⟩
    exact ⟨Or.inr ⟨⟨(x, r), mem_univ x, hr⟩, rfl⟩,
      fun hm => (not_le_of_gt hr0) ((C.side x r hr).mp hm)⟩

/-- The actual compact Liouville domain on this smaller open extension.
Its primitive and outward field are obtained by restriction. -/
def localizedDomain : LiouvilleDomain d where
  domain := D.neighborhoodDomain.restrict C.neighborhood C.carrier_subset_neighborhood
  liouville := D.neighborhoodStructure.restrict C.neighborhood C.carrier_subset_neighborhood

/-- Localization preserves the compact domain itself by its original
open-subset inclusion. -/
def compactHomeomorph : C.localizedDomain.domain.Point ≃ₜ D.neighborhoodDomain.Point :=
  D.neighborhoodDomain.restrictPointHomeomorph C.neighborhood C.carrier_subset_neighborhood

set_option backward.isDefEq.respectTransparency false in
/-- The boundary form of the localized domain is literally the original
boundary restriction, which will determine the infinite-cylinder primitive. -/
theorem localized_boundaryForm :
    C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive =
      D.domain.boundaryForm D.liouville.primitive := by
  change (D.neighborhoodDomain.restrict C.neighborhood C.carrier_subset_neighborhood).boundaryForm
    ((D.neighborhoodDomain.extension.restrict C.neighborhood).pullback
      D.neighborhoodDomain.extension Subtype.val D.neighborhoodStructure.primitive) = _
  rw [D.neighborhoodDomain.boundaryForm_restrict C.neighborhood
    C.carrier_subset_neighborhood D.neighborhoodStructure.primitive]
  exact D.neighborhood_boundaryForm

end FlowCollar
end LiouvilleDomain
end FsFltz.Geometry
