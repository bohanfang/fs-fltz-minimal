import FsFltz.Geometry.CompletionLocalization
import FsFltz.Geometry.CollarStretch

/-!
# An actual cylindrical end on the localized collar extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 783–814. The constructed boundary flow collar and the
proved scalar inverse supply a smooth infinite positive end in the actual
open ambient neighborhood. Its exterior, covering, and compact slabs are
geometric properties of these maps; no completion is an input.

The total maps below use the boundary point at radius zero outside their
stated open source. Smoothness is asserted only on the displayed source.
The complete flow and its negative-radius end map remain separate work.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

/-- A total lift of the actual collar map into the localized neighborhood. -/
def collarMap (p : D.neighborhoodDomain.boundary.Point × ℝ) :
    C.localizedDomain.domain.extension.Point :=
  if hp : p ∈ C.strip then ⟨C.map p, Or.inr ⟨⟨p, hp⟩, rfl⟩⟩
  else ⟨C.map (p.1, 0), Or.inr ⟨⟨(p.1, 0), mem_univ _,
    neg_lt_zero.mpr C.positive_width, C.positive_width⟩, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem collarMap_val (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : p ∈ C.strip) : (C.collarMap p).val = C.map p := by
  unfold collarMap
  rw [dite_eq_left hp]

theorem smooth_collarMap_on : ContMDiffOn
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    C.collarMap C.strip := by
  intro p hp
  apply (ContMDiffWithinAt.subtypeVal_comp_iff C.neighborhood C.collarMap C.strip p).mp
  apply (C.smooth_map p).contMDiffWithinAt.congr
  · intro q hq
    exact C.collarMap_val q hq
  · exact C.collarMap_val p hp

/-- The stretched cylindrical coordinate map into the actual localized ambient. -/
def endMap (p : D.neighborhoodDomain.boundary.Point × ℝ) :
    C.localizedDomain.domain.extension.Point :=
  C.collarMap (p.1, CollarStretch.inverse C.positive_width p.2)

/-- The true open radial source of the stretched collar. -/
def endStrip : TopologicalSpace.Opens (D.neighborhoodDomain.boundary.Point × ℝ) :=
  ⟨univ ×ˢ Ioi (-C.width), isOpen_univ.prod isOpen_Ioi⟩

theorem endMap_val (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : -C.width < p.2) :
    (C.endMap p).val = C.map (p.1, CollarStretch.inverse C.positive_width p.2) :=
  C.collarMap_val _ ⟨mem_univ _, CollarStretch.inverse_mem_collar C.positive_width hp⟩

theorem smooth_endMap_on : ContMDiffOn
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    C.endMap C.endStrip := by
  exact C.smooth_collarMap_on.comp
    (contMDiff_fst.prodMk
      ((CollarStretch.inverse_contDiff C.positive_width).contMDiff.comp
        contMDiff_snd)).contMDiffOn
    (fun p hp => ⟨mem_univ _, CollarStretch.inverse_mem_collar C.positive_width hp.2⟩)

/-- The stretched end map on its actual open source. -/
def endStripMap (p : C.endStrip) : C.localizedDomain.domain.extension.Point :=
  C.endMap p.val

theorem smooth_endStripMap : ContMDiff
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
    C.endStripMap := by
  intro p
  exact (C.smooth_endMap_on.contMDiffAt (C.endStrip.isOpen.mem_nhds p.property)).comp p
    (contMDiff_subtype_val p)

@[simp] theorem endMap_zero (x : D.neighborhoodDomain.boundary.Point) :
    C.endMap (x, 0) = C.localizedDomain.domain.boundaryInclusion.map x := by
  apply Subtype.ext
  rw [C.endMap_val (x, 0) (neg_lt_zero.mpr C.positive_width),
    CollarStretch.inverse_zero, C.map_zero]
  rfl

/-- The scalar inverse reparameterizes the actual open source onto the finite strip. -/
def reparameterization (p : C.endStrip) : C.strip :=
  ⟨(p.val.1, CollarStretch.inverse C.positive_width p.val.2),
    mem_univ _, CollarStretch.inverse_mem_collar C.positive_width p.property.2⟩

theorem smooth_reparameterization : ContMDiff
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ C.reparameterization :=
  (ContMDiff.subtypeVal_comp_iff C.strip C.reparameterization).mp
    ((contMDiff_fst.comp contMDiff_subtype_val).prodMk
      ((CollarStretch.inverse_contDiff C.positive_width).contMDiff.comp
        (contMDiff_snd.comp contMDiff_subtype_val)))

/-- The forward stretch gives the inverse source reparameterization. -/
def reparameterizationInverse (p : C.strip) : C.endStrip :=
  ⟨(p.val.1, CollarStretch.stretch C.width p.val.2), mem_univ _,
    lt_of_lt_of_le p.property.2.1 (CollarStretch.le_stretch p.property.2.2)⟩

theorem smooth_reparameterizationInverse : ContMDiff
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞ C.reparameterizationInverse := by
  apply (ContMDiff.subtypeVal_comp_iff C.endStrip C.reparameterizationInverse).mp
  intro p
  exact ((contMDiff_fst.comp contMDiff_subtype_val) p).prodMk
    ((CollarStretch.stretch_contDiffAt p.property.2.2).contMDiffAt.comp p
      ((contMDiff_snd.comp contMDiff_subtype_val) p))

/-- A proved smooth source equivalence, with no completion involved. -/
def reparameterizationDiffeomorph : Diffeomorph
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) C.endStrip C.strip ∞ where
  toFun := C.reparameterization
  invFun := C.reparameterizationInverse
  left_inv := by
    intro p
    apply Subtype.ext
    change (p.val.1, CollarStretch.stretch C.width
      (CollarStretch.inverse C.positive_width p.val.2)) = p.val
    simp
  right_inv := by
    intro p
    apply Subtype.ext
    change (p.val.1, CollarStretch.inverse C.positive_width
      (CollarStretch.stretch C.width p.val.2)) = p.val
    simp [CollarStretch.inverse_stretch C.positive_width p.property.2.2]
  contMDiff_toFun := C.smooth_reparameterization
  contMDiff_invFun := C.smooth_reparameterizationInverse

/-- The stretched source parametrizes the exact original collar image. -/
theorem isOpenEmbedding_endStripMap : Topology.IsOpenEmbedding C.endStripMap := by
  apply C.neighborhood.isOpenEmbedding'.of_comp C.endStripMap
  have he := C.isOpenEmbedding_stripMap.comp
    C.reparameterizationDiffeomorph.toHomeomorph.isOpenEmbedding
  convert he using 1
  funext p
  exact C.endMap_val p.val p.property.2

/-- The nonnegative end, with its native subspace topology. -/
def nonnegativeEndMap (p : {p : D.neighborhoodDomain.boundary.Point × ℝ // 0 ≤ p.2}) :
    C.localizedDomain.domain.extension.Point := C.endMap p.val

theorem isEmbedding_nonnegativeEndMap : Topology.IsEmbedding C.nonnegativeEndMap := by
  let i : {p : D.neighborhoodDomain.boundary.Point × ℝ // 0 ≤ p.2} → C.endStrip :=
    fun p => ⟨p.val, mem_univ _, lt_of_lt_of_le (neg_lt_zero.mpr C.positive_width) p.property⟩
  have hi : Topology.IsEmbedding i :=
    (Topology.IsEmbedding.subtypeVal.of_comp_iff).mp Topology.IsEmbedding.subtypeVal
  exact C.isOpenEmbedding_endStripMap.isEmbedding.comp hi

set_option backward.isDefEq.respectTransparency false in
/-- The actual stretched map is an immersion throughout its open radial source. -/
theorem endMap_mfderiv_injective (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : -C.width < p.2) : Function.Injective
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) C.endMap p) := by
  let q : C.endStrip := ⟨p, mem_univ _, hp⟩
  let e := C.reparameterizationDiffeomorph.trans C.diffeomorph
  have he : Function.Injective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) e q) :=
    (e.isInvertible_mfderiv (by simp)).injective
  have heval := mfderiv_comp (f := e)
    (g := (Subtype.val : C.image → D.neighborhoodDomain.extension.Point)) q
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiableAt (by simp))
  erw [D.neighborhoodDomain.extension.mfderiv_restrict_val C.image (e q)] at heval
  have hCval := mfderiv_comp (f := C.endStripMap)
    (g := (Subtype.val : C.neighborhood → D.neighborhoodDomain.extension.Point)) q
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    (C.smooth_endStripMap.mdifferentiableAt (by simp))
  erw [D.neighborhoodDomain.extension.mfderiv_restrict_val C.neighborhood
    (C.endStripMap q)] at hCval
  have hfun : (Subtype.val : C.image → D.neighborhoodDomain.extension.Point) ∘ e =
      (Subtype.val : C.neighborhood → D.neighborhoodDomain.extension.Point) ∘
        C.endStripMap := by
    funext z
    exact (C.endMap_val z.val z.property.2).symm
  rw [hfun, hCval] at heval
  have hstrip : Function.Injective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
        C.endStripMap q) := by
    simp only [ContinuousLinearMap.id_comp] at heval
    rw [heval]
    exact he
  have hcomp := mfderiv_comp
    (f := (Subtype.val : C.endStrip → D.neighborhoodDomain.boundary.Point × ℝ))
    (g := C.endMap) q
    ((C.smooth_endMap_on.contMDiffAt (C.endStrip.isOpen.mem_nhds q.property)).mdifferentiableAt
      (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
  change mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
    C.endStripMap q = _ at hcomp
  rw [hcomp] at hstrip
  have hi : Function.Injective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        (Subtype.val : C.endStrip → D.neighborhoodDomain.boundary.Point × ℝ) q) := by
    intro v w hvw
    apply hstrip
    exact congrArg
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) C.endMap p) hvw
  have hs := LinearMap.surjective_of_injective (f :=
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (Subtype.val : C.endStrip → D.neighborhoodDomain.boundary.Point × ℝ) q).toLinearMap) hi
  intro v w hvw
  obtain ⟨v', rfl⟩ := hs v
  obtain ⟨w', rfl⟩ := hs w
  exact congrArg _ (hstrip hvw)

/-- The stretched radial sign detects the actual compact side. -/
theorem endMap_mem_carrier_iff (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : -C.width < p.2) :
    C.endMap p ∈ C.localizedDomain.domain.carrier ↔ p.2 ≤ 0 := by
  change (C.endMap p).val ∈ D.neighborhoodDomain.carrier ↔ p.2 ≤ 0
  rw [C.endMap_val p hp]
  change C.flow _ _ ∈ D.neighborhoodDomain.carrier ↔ p.2 ≤ 0
  rw [C.side p.1 _
    (CollarStretch.inverse_mem_collar C.positive_width hp)]
  simpa using (CollarStretch.inverse_strictMono C.positive_width).le_iff_le
    (a := p.2) (b := 0)

/-- There are no exterior components other than the actual positive cylinder. -/
theorem exterior_eq_endMap_image :
    C.localizedDomain.domain.carrierᶜ = C.endMap '' (univ ×ˢ Ioi (0 : ℝ)) := by
  ext z
  constructor
  · intro hz
    have hz' : z.val ∈ (C.neighborhood : Set D.neighborhoodDomain.extension.Point) \
        D.neighborhoodDomain.carrier := ⟨z.property, hz⟩
    rw [C.neighborhood_diff_carrier] at hz'
    obtain ⟨⟨x, t⟩, ⟨_, ht0, htδ⟩, he⟩ := hz'
    have hr0 : 0 < CollarStretch.stretch C.width t :=
      lt_of_lt_of_le ht0 (CollarStretch.le_stretch htδ)
    refine ⟨(x, CollarStretch.stretch C.width t), ⟨mem_univ _, hr0⟩, ?_⟩
    apply Subtype.ext
    rw [C.endMap_val _ (lt_trans (neg_lt_zero.mpr C.positive_width) hr0),
      CollarStretch.inverse_stretch C.positive_width htδ]
    exact he
  · rintro ⟨p, hp, rfl⟩
    change ¬ C.endMap p ∈ C.localizedDomain.domain.carrier
    rw [C.endMap_mem_carrier_iff p (lt_trans (neg_lt_zero.mpr C.positive_width) hp.2)]
    exact not_le_of_gt hp.2

/-- The original compact carrier together with the nonnegative actual end
covers the entire localized ambient. -/
theorem endMap_covering :
    C.localizedDomain.domain.carrier ∪ C.endMap '' (univ ×ˢ Ici (0 : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z ∈ C.localizedDomain.domain.carrier
  · exact Or.inl hz
  · have hz' : z ∈ C.endMap '' (univ ×ˢ Ioi (0 : ℝ)) := by
      rw [← C.exterior_eq_endMap_image]
      exact hz
    exact Or.inr (image_mono (Set.prod_mono Subset.rfl Ioi_subset_Ici_self) hz')

/-- Every closed bounded radial slab inside the open end source is compact. -/
theorem isCompact_endMap_slab {a b : ℝ} (ha : -C.width < a) :
    IsCompact (C.endMap '' (univ ×ˢ Icc a b)) := by
  apply (D.neighborhoodDomain.isCompact_boundary.prod isCompact_Icc).image_of_continuousOn
  exact C.smooth_endMap_on.continuousOn.mono
    (fun p hp => ⟨mem_univ _, lt_of_lt_of_le ha hp.2.1⟩)

/-- Add one finite end slab to the original compact carrier. -/
def enlargedCompact : Set C.localizedDomain.domain.extension.Point :=
  C.localizedDomain.domain.carrier ∪ C.endMap '' (univ ×ˢ Icc (0 : ℝ) 1)

theorem isCompact_enlargedCompact : IsCompact C.enlargedCompact :=
  C.localizedDomain.domain.compact.union
    (C.isCompact_endMap_slab (neg_lt_zero.mpr C.positive_width))

/-- Outside the displayed compact set, the constructed end coordinates
have radius at least one, as required for uniform-time continuation. -/
theorem endMap_covers_outside_enlargedCompact
    (z : C.localizedDomain.domain.extension.Point) (hz : z ∉ C.enlargedCompact) :
    ∃ x r, 1 ≤ r ∧ C.endMap (x, r) = z := by
  have hn : z ∉ C.localizedDomain.domain.carrier := fun hm => hz (Or.inl hm)
  have he : z ∈ C.endMap '' (univ ×ˢ Ioi (0 : ℝ)) := by
    rw [← C.exterior_eq_endMap_image]
    exact hn
  obtain ⟨⟨x, r⟩, ⟨_, hr0⟩, he⟩ := he
  refine ⟨x, r, ?_, he⟩
  by_contra hr
  exact hz (Or.inr ⟨(x, r), ⟨mem_univ _, hr0.le, le_of_lt (lt_of_not_ge hr)⟩, he⟩)

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
