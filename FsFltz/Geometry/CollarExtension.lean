import FsFltz.Geometry.CollarIsotopy
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Relative collar velocity and its compactly supported extension

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and `sec:lean`,
lines 788–814. The embedded interpolation of `CollarIsotopy` supplies its
Eulerian velocity on an actual common collar. A smooth cutoff extends this
velocity to the original target extension manifold, with compact support,
zero boundary values, and the exact interpolation ODE on a smaller collar.

This is the vector-field prerequisite for relative isotopy extension.
`CollarSmoothEvolution` integrates the produced field to a jointly smooth
evolution and uses its inverse to construct a collar-adapted compact
presentation and a smooth completed presentation. Coherent choices for
varying completions remain pending. This module supplies the velocity
producer and assumes no collar compatibility of the compact presentation.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CollarExtension

variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- The time-coordinate unit vector is a smooth native tangent-bundle
section, including when the other factor has dimension zero. -/
theorem contMDiff_timeUnitSection :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p : ℝ × Q =>
        (⟨p, (1, (0 : E))⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hq : ContMDiff I I.tangent ∞
      (Bundle.zeroSection E (TangentSpace I : Q → Type)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace I : Q → Type)
  exact contMDiff_equivTangentBundleProd_symm.comp
    ((ht.comp contMDiff_fst).prodMk (hq.comp contMDiff_snd))

/-- Differentiating a jointly smooth family in its actual time coordinate
gives a jointly smooth native tangent vector along that family. -/
theorem contMDiffOn_timeVelocity
    {F N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    {f : ℝ × Q → N} {U : Set (ℝ × Q)} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F) ∞ f U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q =>
        (⟨f p, mfderiv ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F)
          f p (1, (0 : E))⟩ : TangentBundle 𝓘(ℝ, F) N)) U := by
  have hv := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    hU.uniqueMDiffOn |>.comp
      (contMDiff_timeUnitSection (E := E) (Q := Q)).contMDiffOn (fun _ hp => hp)
  apply hv.congr
  intro p hp
  dsimp only [Function.comp_def, tangentMapWithin]
  rw [mfderivWithin_eq_mfderiv (hU.uniqueMDiffOn p hp)
    ((hf.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))]

/-- A smooth compactly supported cutoff equals one on a genuine open
neighborhood of a given compact set, and its closed support lies in the
prescribed open domain. -/
theorem exists_smooth_compact_cutoff [FiniteDimensional ℝ E]
    [LocallyCompactSpace H] [T2Space Q] [SecondCountableTopology Q]
    {K U : Set Q} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Q → ℝ) (V : TopologicalSpace.Opens Q),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ K ⊆ (V : Set Q) ∧
      (∀ p ∈ V, χ p = 1) ∧ IsCompact (tsupport χ) ∧ tsupport χ ⊆ U := by
  let := ChartedSpace.locallyCompactSpace H Q
  obtain ⟨B, hBo, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨S, hSo, hKS, hSc⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hBo).mem_nhdsSet.mpr (subset_inter hKU hKB))
  obtain ⟨V, hVo, hKV, hVc⟩ := hK.exists_isOpen_closure_subset (hSo.mem_nhdsSet.mpr hKS)
  obtain ⟨χ, hχ, _, hχS, hχV⟩ := exists_contMDiff_support_eq_eq_one_iff I
    (n := ⊤) hSo isClosed_closure hVc
  have hcc : IsCompact (closure S) := hBc.of_isClosed_subset isClosed_closure
    (hSc.trans (inter_subset_right.trans subset_closure))
  refine ⟨χ, ⟨V, hVo⟩, hχ, hKV, ?_, ?_, ?_⟩
  · intro p hp
    exact (hχV p).mp (subset_closure hp)
  · simpa only [tsupport, hχS] using hcc
  · simpa only [tsupport, hχS] using hSc.trans inter_subset_left

/-- One collar width serves every time and every point of a compact
boundary. The open set may be smaller than the original interpolation domain. -/
theorem exists_uniform_width {B : Type} [TopologicalSpace B]
    {U : Set (ℝ × (B × ℝ))} (hB : IsCompact (univ : Set B)) (hU : IsOpen U)
    (hseam : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-δ) δ) ⊆ U := by
  obtain ⟨T, V, _, hVo, hIT, hBV, hTV⟩ := generalized_tube_lemma isCompact_Icc
    (hB.prod isCompact_singleton) hU hseam
  obtain ⟨P, Q, _, hQo, hBP, hzeroQ, hPQ⟩ := generalized_tube_lemma
    hB isCompact_singleton hVo hBV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hQo.mem_nhds (hzeroQ (mem_singleton 0)))
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
  apply hTV
  refine ⟨hIT ht, hPQ ⟨hBP (mem_univ x), hball ?_⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

/-- The common collar extends across both parameter endpoints. Compactness
provides one positive time margin and one positive spatial width. -/
theorem exists_uniform_time_width {B : Type} [TopologicalSpace B]
    {U : Set (ℝ × (B × ℝ))} (hB : IsCompact (univ : Set B)) (hU : IsOpen U)
    (hseam : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      Ioo (-ε) (1 + ε) ×ˢ (univ ×ˢ Ioo (-δ) δ) ⊆ U := by
  obtain ⟨T, V, hTo, hVo, hIT, hBV, hTV⟩ := generalized_tube_lemma isCompact_Icc
    (hB.prod isCompact_singleton) hU hseam
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.mem_nhds_iff.mp
    (hTo.mem_nhds (hIT (show (0 : ℝ) ∈ Icc 0 1 by simp)))
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp
    (hTo.mem_nhds (hIT (show (1 : ℝ) ∈ Icc 0 1 by simp)))
  obtain ⟨P, Q, _, hQo, hBP, hzeroQ, hPQ⟩ := generalized_tube_lemma
    hB isCompact_singleton hVo hBV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hQo.mem_nhds (hzeroQ (mem_singleton 0)))
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have htime : Ioo (-ε) (1 + ε) ⊆ T := by
    intro t ht
    by_cases ht₀ : t < 0
    · apply hball₀
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht₀]
      have : ε ≤ ε₀ := min_le_left _ _
      linarith [ht.1]
    · by_cases ht₁ : 1 < t
      · apply hball₁
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t - 1)]
        have : ε ≤ ε₁ := min_le_right _ _
        linarith [ht.2]
      · exact hIT ⟨le_of_not_gt ht₀, le_of_not_gt ht₁⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
  apply hTV
  refine ⟨htime ht, hPQ ⟨hBP (mem_univ x), hball ?_⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

end CollarExtension

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- A constructed neighborhood certificate for the existing interpolation.
The constructor below proves existence from the compact presentation. -/
structure EmbeddedPresentationCollar where
  source : TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ))
  width : ℝ
  width_pos : 0 < width
  width_mem : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-width) width) ⊆
    (source : Set (ℝ × (D.domain.boundary.Point × ℝ)))
  source_mem : (source : Set (ℝ × (D.domain.boundary.Point × ℝ))) ⊆
    (C.compactPresentationInterpolationDomain C' h : Set (ℝ × (D.domain.boundary.Point × ℝ)))
  seam_mem : ∀ p ∈ source, ∀ x : D.domain.boundary.Point, (p.1, (x, 0)) ∈ source
  embedding : Topology.IsOpenEmbedding (fun p : source =>
    C.presentationCollarInterpolationWithParameter C' h p.val)
  localDiffeomorph : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
    ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
    (C.presentationCollarInterpolationWithParameter C' h)
    (source : Set (ℝ × (D.domain.boundary.Point × ℝ)))

/-- The collar certificate has no compatibility hypothesis. -/
def embeddedPresentationCollar : C.EmbeddedPresentationCollar C' h := by
  apply Classical.choice
  obtain ⟨U, δ, hδ, hw, hU, he, hd⟩ :=
    C.exists_common_embedded_collarInterpolation C' h
  have hseam : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆
      (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) := by
    rintro ⟨t, x, r⟩ ⟨ht, hx, hr⟩
    have hr0 : r = 0 := hr
    subst r
    exact hw ⟨ht, hx, by simpa using hδ⟩
  obtain ⟨T, V, hT, _, hIT, hBV, hTV⟩ := generalized_tube_lemma isCompact_Icc
    (D.domain.isCompact_boundary.prod isCompact_singleton) U.isOpen hseam
  let U₀ : TopologicalSpace.Opens (ℝ × (D.domain.boundary.Point × ℝ)) :=
    ⟨(U : Set (ℝ × (D.domain.boundary.Point × ℝ))) ∩ (T ×ˢ univ),
      U.isOpen.inter (hT.prod isOpen_univ)⟩
  have hs : (U₀ : Set (ℝ × (D.domain.boundary.Point × ℝ))) ⊆
      (U : Set (ℝ × (D.domain.boundary.Point × ℝ))) := inter_subset_left
  have hd₀ : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (C.presentationCollarInterpolationWithParameter C' h) U₀ :=
    fun p => hd ⟨p.val, hs p.property⟩
  have hl : IsLocalHomeomorph (fun p : U₀ =>
      C.presentationCollarInterpolationWithParameter C' h p.val) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hd₀.isLocalHomeomorphOn.comp U₀.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn
      (fun p _ => p.property)
  have hj : InjOn (C.presentationCollarInterpolationWithParameter C' h) U₀ :=
    (Set.injOn_iff_injective.mpr he.injective).mono hs
  refine ⟨⟨U₀, δ, hδ, ?_, hs.trans hU, ?_,
    hl.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp hj), hd₀⟩⟩
  · intro p hp
    exact ⟨hw hp, hIT hp.1, mem_univ _⟩
  · intro p hp x
    exact ⟨hTV ⟨hp.2.1, hBV ⟨mem_univ x, mem_singleton 0⟩⟩,
      hp.2.1, mem_univ _⟩

@[simp] theorem compactPresentationInterpolation_boundary
    (t : ℝ) (x : D.domain.boundary.Point) :
    C.compactPresentationInterpolation C' h (t, (x, 0)) =
      E.domain.boundaryInclusion.map (h.boundaryEquiv x) := by
  simp [compactPresentationInterpolation]

set_option backward.isDefEq.respectTransparency false in
theorem compactPresentationInterpolation_timeVelocity_boundary
    (t : ℝ) (x : D.domain.boundary.Point) :
    mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model d) (C.compactPresentationInterpolation C' h)
      (t, (x, 0)) (1, (0, 0)) = 0 := by
  have hf : ContMDiffAt ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (C.compactPresentationInterpolation C' h) (t, (x, 0)) :=
    (C.contMDiffOn_compactPresentationInterpolation C' h).contMDiffAt
      ((C.compactPresentationInterpolationDomain C' h).isOpen.mem_nhds
        (C.mem_compactPresentationInterpolationDomain_boundary C' h t x))
  have he : (fun s : ℝ => C.compactPresentationInterpolation C' h (s, (x, 0))) =
      (fun _ => E.domain.boundaryInclusion.map (h.boundaryEquiv x)) := by
    funext s
    exact C.compactPresentationInterpolation_boundary C' h s x
  have hc := mfderiv_comp (f := fun s : ℝ => (s, (x, (0 : ℝ))))
    (g := C.compactPresentationInterpolation C' h) t
    (hf.mdifferentiableAt (by simp)) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
    (fun s : ℝ => C.compactPresentationInterpolation C' h (s, (x, 0))) t = _ at hc
  rw [he, mfderiv_const, mfderiv_prod_left] at hc
  exact (congrArg (fun L => L (1 : ℝ)) hc).symm

/-- The actual collar domain in the original compact extension. -/
def extensionCollarDomain : TopologicalSpace.Opens D.domain.extension.Point where
  carrier := C.inclusion.map ⁻¹' C.escapingBasin
  is_open' := C.escapingBasin.isOpen.preimage C.inclusion.map.contMDiff.continuous

def extensionCollarCoordinates (z : C.extensionCollarDomain) : D.domain.boundary.Point × ℝ :=
  C.endCoordinates ⟨C.inclusion.map z.val, z.property⟩

theorem contMDiff_extensionCollarCoordinates :
    ContMDiff 𝓘(ℝ, Model d) ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      C.extensionCollarCoordinates := by
  apply C.contMDiff_endCoordinates.comp
  apply (ContMDiff.subtypeVal_comp_iff C.escapingBasin _).mp
  exact C.inclusion.map.contMDiff.comp contMDiff_subtype_val

@[simp] theorem endMap_extensionCollarCoordinates (z : C.extensionCollarDomain) :
    C.endMap (C.extensionCollarCoordinates z) = C.inclusion.map z.val :=
  C.endMap_endCoordinates _

theorem presentationCollarPoint_mem_extensionCollarDomain
    (q : D.domain.boundary.Point × ℝ) (hq : q ∈ C.presentationCollarSourceDomain) :
    C.presentationCollarPoint q ∈ C.extensionCollarDomain := by
  change C.inclusion.map (C.presentationCollarPoint q) ∈ C.escapingBasin
  rw [C.inclusionMap_presentationCollarPoint q hq]
  exact ⟨q, rfl⟩

@[simp] theorem extensionCollarCoordinates_presentationCollarPoint
    (q : D.domain.boundary.Point × ℝ) (hq : q ∈ C.presentationCollarSourceDomain) :
    C.extensionCollarCoordinates ⟨C.presentationCollarPoint q,
      C.presentationCollarPoint_mem_extensionCollarDomain q hq⟩ = q := by
  apply C.endMap_injective
  rw [C.endMap_extensionCollarCoordinates, C.inclusionMap_presentationCollarPoint q hq]

@[simp] theorem presentationCollarPoint_extensionCollarCoordinates
    (z : C.extensionCollarDomain) :
    C.presentationCollarPoint (C.extensionCollarCoordinates z) = z.val := by
  apply C.inclusion.embedding.injective
  rw [C.inclusionMap_presentationCollarPoint]
  · exact C.endMap_extensionCollarCoordinates z
  · exact ⟨z.val, (C.endMap_extensionCollarCoordinates z).symm⟩

namespace EmbeddedPresentationCollar

variable {C C' h} (A : C.EmbeddedPresentationCollar C' h)

def image : TopologicalSpace.Opens (ℝ × (E.domain.boundary.Point × ℝ)) where
  carrier := range (fun p : A.source =>
    C.presentationCollarInterpolationWithParameter C' h p.val)
  is_open' := A.embedding.isOpen_range

/-- The unique source point on the actual open image of the augmented
interpolation. Its joint smoothness is proved from the local inverses. -/
def coordinates (z : A.image) : ℝ × (D.domain.boundary.Point × ℝ) :=
  z.property.choose.val

theorem coordinates_mem (z : A.image) : A.coordinates z ∈ A.source :=
  z.property.choose.property

@[simp] theorem interpolation_coordinates (z : A.image) :
    C.presentationCollarInterpolationWithParameter C' h (A.coordinates z) = z.val :=
  z.property.choose_spec

theorem coordinates_interpolation (p : ℝ × (D.domain.boundary.Point × ℝ))
    (hp : p ∈ A.source) :
    A.coordinates ⟨C.presentationCollarInterpolationWithParameter C' h p,
      ⟨⟨p, hp⟩, rfl⟩⟩ = p := by
  have hinj : InjOn (C.presentationCollarInterpolationWithParameter C' h) A.source :=
    Set.injOn_iff_injective.mpr A.embedding.injective
  exact hinj (A.coordinates_mem _) hp (A.interpolation_coordinates _)

theorem contMDiff_coordinates :
    ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞ A.coordinates := by
  intro z
  let l := A.localDiffeomorph ⟨A.coordinates z, A.coordinates_mem z⟩
  have hi : ContMDiffAt ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      l.localInverse z.val := by
    rw [← A.interpolation_coordinates z]
    exact l.localInverse_contMDiffAt
  have hz : l.localInverse z.val = A.coordinates z := by
    rw [← A.interpolation_coordinates z]
    exact l.localInverse_left_inv l.localInverse_mem_target
  apply (hi.comp z (contMDiff_subtype_val z)).congr_of_eventuallyEq
  have ht : Tendsto (Subtype.val : A.image → ℝ × (E.domain.boundary.Point × ℝ))
      (𝓝 z) (𝓝 (C.presentationCollarInterpolationWithParameter C' h (A.coordinates z))) := by
    rw [A.interpolation_coordinates]
    exact continuous_subtype_val.continuousAt
  have hn : ∀ᶠ y in 𝓝 z, l.localInverse y.val ∈ A.source :=
    (hi.continuousAt.comp continuousAt_subtype_val).preimage_mem_nhds
      (by simpa only [Function.comp_apply, hz] using
        A.source.isOpen.mem_nhds (A.coordinates_mem z))
  filter_upwards [hn, l.localInverse_eventuallyEq_right.comp_tendsto ht] with y hy he
  have hinj : InjOn (C.presentationCollarInterpolationWithParameter C' h) A.source :=
    Set.injOn_iff_injective.mpr A.embedding.injective
  apply hinj (A.coordinates_mem y) hy
  exact (A.interpolation_coordinates y).trans he.symm

private theorem extensionCollarEmbedding :
    Topology.IsOpenEmbedding
      (fun p : ℝ × C'.extensionCollarDomain => (p.1, p.2.val)) :=
  Topology.IsOpenEmbedding.id.prodMap C'.extensionCollarDomain.isOpenEmbedding'

def targetSource : TopologicalSpace.Opens (ℝ × C'.extensionCollarDomain) where
  carrier := (fun p => (p.1, C'.extensionCollarCoordinates p.2)) ⁻¹' A.image
  is_open' := A.image.isOpen.preimage
    (continuous_fst.prodMk (C'.contMDiff_extensionCollarCoordinates.continuous.comp continuous_snd))

/-- The Eulerian velocity is defined on an actual open neighborhood in
time times the target compact extension, rather than abstract end coordinates. -/
def target : TopologicalSpace.Opens (ℝ × E.domain.extension.Point) where
  carrier := (fun p : ℝ × C'.extensionCollarDomain => (p.1, p.2.val)) '' A.targetSource
  is_open' := (extensionCollarEmbedding (C' := C')).isOpenMap _ A.targetSource.isOpen

def targetInCollar (p : A.target) : ℝ × C'.extensionCollarDomain :=
  (p.val.1, ⟨p.val.2, by
    obtain ⟨q, _, hq⟩ := p.property
    rw [← hq]
    exact q.2.property⟩)

theorem targetInCollar_mem (p : A.target) : A.targetInCollar p ∈ A.targetSource := by
  obtain ⟨q, hq, he⟩ := p.property
  have hqe : A.targetInCollar p = q := by
    apply Prod.ext
    · exact (congrArg Prod.fst he).symm
    · apply Subtype.ext
      exact (congrArg Prod.snd he).symm
  rwa [hqe]

theorem contMDiff_targetInCollar :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ A.targetInCollar := by
  apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
  apply (ContMDiff.subtypeVal_comp_iff C'.extensionCollarDomain _).mp
  exact contMDiff_snd.comp contMDiff_subtype_val

def extensionCoordinates (p : A.target) : ℝ × (D.domain.boundary.Point × ℝ) :=
  A.coordinates ⟨((A.targetInCollar p).1,
    C'.extensionCollarCoordinates (A.targetInCollar p).2), A.targetInCollar_mem p⟩

theorem extensionCoordinates_mem (p : A.target) : A.extensionCoordinates p ∈ A.source :=
  A.coordinates_mem _

theorem contMDiff_extensionCoordinates :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      A.extensionCoordinates := by
  apply A.contMDiff_coordinates.comp
  apply (ContMDiff.subtypeVal_comp_iff A.image _).mp
  exact A.contMDiff_targetInCollar.fst.prodMk
    (C'.contMDiff_extensionCollarCoordinates.comp A.contMDiff_targetInCollar.snd)

@[simp] theorem extensionCoordinates_time (p : A.target) :
    (A.extensionCoordinates p).1 = p.val.1 := by
  exact congrArg Prod.fst (A.interpolation_coordinates _)

@[simp] theorem compactInterpolation_extensionCoordinates (p : A.target) :
    C.compactPresentationInterpolation C' h (A.extensionCoordinates p) = p.val.2 := by
  have he := congrArg Prod.snd (A.interpolation_coordinates
    ⟨((A.targetInCollar p).1, C'.extensionCollarCoordinates (A.targetInCollar p).2),
      A.targetInCollar_mem p⟩)
  change C.presentationCollarInterpolation C' h (A.extensionCoordinates p) =
    C'.extensionCollarCoordinates (A.targetInCollar p).2 at he
  rw [compactPresentationInterpolation, he, C'.presentationCollarPoint_extensionCollarCoordinates]
  rfl

theorem compactInterpolation_mem_target (p : ℝ × (D.domain.boundary.Point × ℝ))
    (hp : p ∈ A.source) :
    (p.1, C.compactPresentationInterpolation C' h p) ∈ A.target := by
  let z : C'.extensionCollarDomain :=
    ⟨C.compactPresentationInterpolation C' h p,
      C'.presentationCollarPoint_mem_extensionCollarDomain _ (A.source_mem hp).2⟩
  refine ⟨(p.1, z), ?_, rfl⟩
  change (p.1, C'.extensionCollarCoordinates z) ∈ A.image
  rw [show C'.extensionCollarCoordinates z = C.presentationCollarInterpolation C' h p from
    C'.extensionCollarCoordinates_presentationCollarPoint _ (A.source_mem hp).2]
  exact ⟨⟨p, hp⟩, rfl⟩

theorem extensionCoordinates_compactInterpolation
    (p : ℝ × (D.domain.boundary.Point × ℝ)) (hp : p ∈ A.source) :
    A.extensionCoordinates ⟨(p.1, C.compactPresentationInterpolation C' h p),
      A.compactInterpolation_mem_target p hp⟩ = p := by
  have hinj : InjOn (C.presentationCollarInterpolationWithParameter C' h) A.source :=
    Set.injOn_iff_injective.mpr A.embedding.injective
  apply hinj (A.extensionCoordinates_mem _) hp
  apply Prod.ext
  · exact A.extensionCoordinates_time _
  · apply C'.endMap_injective
    have he := congrArg C'.inclusion.map (A.compactInterpolation_extensionCoordinates
      ⟨(p.1, C.compactPresentationInterpolation C' h p), A.compactInterpolation_mem_target p hp⟩)
    change C'.inclusion.map (C'.presentationCollarPoint _) =
      C'.inclusion.map (C'.presentationCollarPoint _) at he
    rwa [C'.inclusionMap_presentationCollarPoint _ (A.source_mem (A.extensionCoordinates_mem _)).2,
      C'.inclusionMap_presentationCollarPoint _ (A.source_mem hp).2] at he

/-- The actual Eulerian velocity in the target extension. Its value outside
the constructed target collar is zero and makes no inverse assertion there. -/
def velocity (p : ℝ × E.domain.extension.Point) : E.domain.extension.Tangent p.2 :=
  if hp : p ∈ A.target then
    mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model d) (C.compactPresentationInterpolation C' h)
      (A.extensionCoordinates ⟨p, hp⟩) (1, (0, 0))
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_velocity :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × E.domain.extension.Point =>
        (⟨p.2, A.velocity p⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) A.target := by
  have hv := CollarExtension.contMDiffOn_timeVelocity A.source.isOpen
    ((C.contMDiffOn_compactPresentationInterpolation C' h).mono A.source_mem)
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : A.target =>
        (⟨p.val.2, A.velocity p.val⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) := by
    intro p
    have hg := (hv.contMDiffAt (A.source.isOpen.mem_nhds (A.extensionCoordinates_mem p))).comp
      p (A.contMDiff_extensionCoordinates p)
    apply hg.congr_of_eventuallyEq
    filter_upwards [] with q
    dsimp only [Function.comp_def]
    rw [A.compactInterpolation_extensionCoordinates q]
    simp only [velocity, dite_eq_left q.property]
    rfl
  intro p hp
  exact ((contMDiffAt_subtype_iff (U := A.target)
    (f := fun q : ℝ × E.domain.extension.Point =>
      (⟨q.2, A.velocity q⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point))).mp
      (hs ⟨p, hp⟩)).contMDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- The velocity really generates the supplied interpolation on its collar. -/
theorem velocity_compactInterpolation
    (p : ℝ × (D.domain.boundary.Point × ℝ)) (hp : p ∈ A.source) :
    A.velocity (p.1, C.compactPresentationInterpolation C' h p) =
      mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        𝓘(ℝ, Model d) (C.compactPresentationInterpolation C' h) p (1, (0, 0)) := by
  rw [velocity, dite_eq_left (A.compactInterpolation_mem_target p hp),
    A.extensionCoordinates_compactInterpolation p hp]

set_option backward.isDefEq.respectTransparency false in
/-- The interpolation solves the nonautonomous manifold ODE for its
constructed Eulerian field, on the actual open collar source. -/
theorem hasMFDerivAt_compactInterpolation
    (t : ℝ) (q : D.domain.boundary.Point × ℝ) (hp : (t, q) ∈ A.source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => C.compactPresentationInterpolation C' h (s, q)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (A.velocity (t, C.compactPresentationInterpolation C' h (t, q)))) := by
  have hf := (C.contMDiffOn_compactPresentationInterpolation C' h).contMDiffAt
    ((C.compactPresentationInterpolationDomain C' h).isOpen.mem_nhds (A.source_mem hp))
  have hi : ContMDiff 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) ∞
      (fun s : ℝ => (s, q)) := contMDiff_id.prodMk contMDiff_const
  have hm := mfderiv_comp (f := fun s : ℝ => (s, q))
    (g := C.compactPresentationInterpolation C' h) t
    (hf.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
    (fun s => C.compactPresentationInterpolation C' h (s, q)) t = _ at hm
  have he : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => C.compactPresentationInterpolation C' h (s, q)) t =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (A.velocity (t, C.compactPresentationInterpolation C' h (t, q))) := by
    rw [hm, mfderiv_prod_left, A.velocity_compactInterpolation (t, q) hp]
    apply ContinuousLinearMap.ext
    intro s
    change ℝ at s
    change mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model d) (C.compactPresentationInterpolation C' h) (t, q) (s, 0) =
      s • (mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        𝓘(ℝ, Model d) (C.compactPresentationInterpolation C' h) (t, q) (1, (0, 0)))
    rw [← map_smul]
    congr 1
    change (s, (0 : Model (d - 1) × ℝ)) = s • (1, (0 : Model (d - 1) × ℝ))
    simp
  have hs := (hf.comp t (hi t)).mdifferentiableAt (by simp) |>.hasMFDerivAt
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
    (fun s => C.compactPresentationInterpolation C' h (s, q)) t
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => C.compactPresentationInterpolation C' h (s, q)) t) at hs
  rwa [he] at hs

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem velocity_boundary (t : ℝ) (y : E.domain.boundary.Point) :
    A.velocity (t, E.domain.boundaryInclusion.map y) = 0 := by
  by_cases hp : (t, E.domain.boundaryInclusion.map y) ∈ A.target
  · let p : A.target := ⟨(t, E.domain.boundaryInclusion.map y), hp⟩
    have hs := A.seam_mem (A.extensionCoordinates p) (A.extensionCoordinates_mem p)
      (h.boundaryEquiv.symm y)
    rw [A.extensionCoordinates_time p] at hs
    have hg : A.extensionCoordinates p = (t, (h.boundaryEquiv.symm y, 0)) := by
      simpa only [C.compactPresentationInterpolation_boundary C' h,
        Diffeomorph.apply_symm_apply] using
        A.extensionCoordinates_compactInterpolation (t, (h.boundaryEquiv.symm y, 0)) hs
    rw [velocity, dite_eq_left hp]
    change mfderiv _ _ _ (A.extensionCoordinates p) _ = 0
    rw [hg]
    exact C.compactPresentationInterpolation_timeVelocity_boundary C' h t _
  · simp only [velocity, dite_eq_right hp]

private def spatialVelocity (p : ℝ × E.domain.extension.Point) :
    TangentSpace ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) p :=
  (0, A.velocity p)

private theorem contMDiffOn_spatialVelocity :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)).tangent) ∞
      (fun p => (⟨p, A.spatialVelocity p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (ℝ × E.domain.extension.Point))) A.target := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
    ((ht.comp contMDiff_fst).contMDiffOn.prodMk A.contMDiffOn_velocity)

/-- The cutoff multiplies the constructed geometric velocity; it does not
alter the ambient primitive or assert an integrated comparison map. -/
def supportedVelocity (χ : ℝ × E.domain.extension.Point → ℝ)
    (p : ℝ × E.domain.extension.Point) : E.domain.extension.Tangent p.2 :=
  χ p • A.velocity p

theorem contMDiff_supportedVelocity
    (χ : ℝ × E.domain.extension.Point → ℝ)
    (hχ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupp : tsupport χ ⊆ (A.target : Set (ℝ × E.domain.extension.Point))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p => (⟨p.2, A.supportedVelocity χ p⟩ :
        TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) := by
  have hs := hχ.contMDiffOn.smul_section_of_tsupport A.target.isOpen hχsupp
    A.contMDiffOn_spatialVelocity
  exact (contMDiff_equivTangentBundleProd.comp hs).snd

@[simp] theorem supportedVelocity_boundary
    (χ : ℝ × E.domain.extension.Point → ℝ) (t : ℝ) (x : E.domain.boundary.Point) :
    A.supportedVelocity χ (t, E.domain.boundaryInclusion.map x) = 0 := by
  simp only [supportedVelocity, A.velocity_boundary, smul_zero]

theorem supportedVelocity_eq_zero_of_notMem_tsupport
    (χ : ℝ × E.domain.extension.Point → ℝ) (p : ℝ × E.domain.extension.Point)
    (hp : p ∉ tsupport χ) : A.supportedVelocity χ p = 0 := by
  rw [supportedVelocity, image_eq_zero_of_notMem_tsupport hp, zero_smul]

end EmbeddedPresentationCollar

set_option backward.isDefEq.respectTransparency false in
/-- A supplied compact presentation produces a smooth time-dependent vector
field on the entire original target extension, supported in one compact set
in time and space and zero on its boundary. On one positive-width collar the
actual interpolation solves its ODE exactly. No interior diffeomorphism or
collar compatibility is an input to this producer. -/
theorem exists_compactlySupported_collarVelocity_open_time :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point)),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      (∀ (t : ℝ) (x : E.domain.boundary.Point), Z t (E.domain.boundaryInclusion.map x) = 0) ∧
      ∀ t ∈ Ioo (-ε) (1 + ε), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
          (fun s => C.compactPresentationInterpolation C' h (s, q)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (Z t (C.compactPresentationInterpolation C' h (t, q)))) := by
  let A := C.embeddedPresentationCollar C' h
  let B : Set (ℝ × E.domain.extension.Point) :=
    Icc (0 : ℝ) 1 ×ˢ (E.domain.boundaryInclusion.map '' univ)
  have hB : IsCompact B := isCompact_Icc.prod
    (E.domain.isCompact_boundary.image E.domain.boundaryInclusion.map.contMDiff.continuous)
  have hBA : B ⊆ A.target := by
    rintro ⟨t, z⟩ ⟨ht, y, _, rfl⟩
    change (t, E.domain.boundaryInclusion.map y) ∈ A.target
    have hs : (t, (h.boundaryEquiv.symm y, 0)) ∈ A.source :=
      A.width_mem ⟨ht, mem_univ _, by simpa using A.width_pos⟩
    simpa only [C.compactPresentationInterpolation_boundary C' h,
      Diffeomorph.apply_symm_apply] using A.compactInterpolation_mem_target _ hs
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) := by
    change LocallyCompactSpace (ℝ × Model d)
    infer_instance
  obtain ⟨χ, V, hχ, hBV, hχone, hχcompact, hχsupp⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) hB A.target.isOpen hBA
  have hJ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun p => (p.1, C.compactPresentationInterpolation C' h p)) A.source :=
    contMDiff_fst.contMDiffOn.prodMk
      ((C.contMDiffOn_compactPresentationInterpolation C' h).mono A.source_mem)
  let U : Set (ℝ × (D.domain.boundary.Point × ℝ)) :=
    (A.source : Set _) ∩ (fun p => (p.1, C.compactPresentationInterpolation C' h p)) ⁻¹' V
  have hU : IsOpen U := hJ.continuousOn.isOpen_inter_preimage A.source.isOpen V.isOpen
  have hseam : Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆ U := by
    rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
    have hr0 : r = 0 := hr
    subst r
    refine ⟨A.width_mem ⟨ht, mem_univ x, by simpa using A.width_pos⟩, ?_⟩
    change (t, C.compactPresentationInterpolation C' h (t, (x, 0))) ∈ V
    rw [C.compactPresentationInterpolation_boundary]
    exact hBV ⟨ht, ⟨h.boundaryEquiv x, mem_univ _, rfl⟩⟩
  obtain ⟨ε, hε, δ, hδ, hw⟩ := CollarExtension.exists_uniform_time_width
    D.domain.isCompact_boundary hU hseam
  let Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x :=
    fun t x => A.supportedVelocity χ (t, x)
  refine ⟨ε, hε, δ, hδ, Z, tsupport χ, A.contMDiff_supportedVelocity χ hχ hχsupp,
    hχcompact, ?_, ?_, ?_⟩
  · intro p hp
    exact A.supportedVelocity_eq_zero_of_notMem_tsupport χ p hp
  · intro t x
    exact A.supportedVelocity_boundary χ t x
  · intro t ht q hq
    have hp : (t, q) ∈ U := hw ⟨ht, hq⟩
    have he : Z t (C.compactPresentationInterpolation C' h (t, q)) =
        A.velocity (t, C.compactPresentationInterpolation C' h (t, q)) := by
      dsimp only [Z, EmbeddedPresentationCollar.supportedVelocity]
      rw [hχone _ hp.2, one_smul]
    rw [he]
    exact A.hasMFDerivAt_compactInterpolation t q hp.1

/-- The closed parameter-interval version of the constructed velocity. The
stronger producer also supplies the ODE across both interval endpoints. -/
theorem exists_compactlySupported_collarVelocity :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point)),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      (∀ (t : ℝ) (x : E.domain.boundary.Point), Z t (E.domain.boundaryInclusion.map x) = 0) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
          (fun s => C.compactPresentationInterpolation C' h (s, q)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (Z t (C.compactPresentationInterpolation C' h (t, q)))) := by
  obtain ⟨ε, hε, δ, hδ, Z, K, hZ, hK, hzero, hboundary, hode⟩ :=
    C.exists_compactlySupported_collarVelocity_open_time C' h
  refine ⟨δ, hδ, Z, K, hZ, hK, hzero, hboundary, ?_⟩
  intro t ht q hq
  exact hode t ⟨by linarith [ht.1], by linarith [ht.2]⟩ q hq

end Completion
end FsFltz.Geometry
