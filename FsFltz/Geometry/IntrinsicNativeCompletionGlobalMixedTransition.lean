import FsFltz.Geometry.IntrinsicNativeCompletionMixedCanonicalTransition
import FsFltz.Geometry.IntrinsicNativeCompletionReverseMixedCanonicalTransition

/-!
# Canonical-square transitions on the original completed family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 788–814. The functions below live on the actual completed
total base. Their values use the unique preimages in the original interior
and full signed cylinder. Smoothness on the image-chart overlaps is proved
from the real mixed transition germs and the actual smooth inverse patch
germs of the original family atlas. Same-branch transitions use the proved
original chart transitions and those same inverse patches.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

private def patchOverlapScalar {U V X : Type*} (i : U → X) (j : V → X)
    (f : U → V → ℂ) (x : X) : ℂ := by
  classical
  exact if h : ∃ u v, i u = x ∧ j v = x then f h.choose h.choose_spec.choose else 0

private theorem patchOverlapScalar_apply {U V X : Type*} (i : U → X) (j : V → X)
    (hi : Function.Injective i) (hj : Function.Injective j) (f : U → V → ℂ)
    (u : U) (v : V) (hpoint : i u = j v) :
    patchOverlapScalar i j f (i u) = f u v := by
  classical
  have h : ∃ a b, i a = i u ∧ j b = i u := ⟨u, v, rfl, hpoint.symm⟩
  rw [patchOverlapScalar, dite_eq_left h]
  have hu : h.choose = u := hi h.choose_spec.choose_spec.1
  have hv : h.choose_spec.choose = v := hj (h.choose_spec.choose_spec.2.trans hpoint)
  exact congrArg₂ f hu hv

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}

local instance globalMixedBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance globalMixedBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ
local instance globalMixedProductCharts : ChartedSpace (Model k × ℝ)
    (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance globalMixedProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞
    (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

/-- The end-to-interior scalar on the actual completed total base. Outside
the common patch range its value is zero; no regularity there is asserted. -/
def originalEndToInteriorCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ :=
  patchOverlapScalar (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
    (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
    (fun u v => squaredCoframeTransition (c.nativeCoframe N u) (d.nativeCoframe N v))

/-- The reverse scalar uses the same original preimages and normalization. -/
def originalInteriorToEndCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ :=
  patchOverlapScalar (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
    (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
    (fun u v => squaredCoframeTransition (d.nativeCoframe N v) (c.nativeCoframe N u))

include hjoint in
theorem originalEndToInteriorCanonicalTransition_apply
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M)
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u = totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) v) :
    originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u) =
        squaredCoframeTransition (c.nativeCoframe N u) (d.nativeCoframe N v) :=
  patchOverlapScalar_apply _ _
    (isOpenEmbedding_totalInterior hδ (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hzero hjoint).injective
    (isOpenEmbedding_totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hjoint).injective _ u v hpoint

include hjoint in
theorem originalInteriorToEndCanonicalTransition_apply
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M)
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u = totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) v) :
    originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u) =
        squaredCoframeTransition (d.nativeCoframe N v) (c.nativeCoframe N u) :=
  patchOverlapScalar_apply _ _
    (isOpenEmbedding_totalInterior hδ (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hzero hjoint).injective
    (isOpenEmbedding_totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hjoint).injective _ u v hpoint

include hboundary hmix in
private theorem originalTotalCylinder_inverse_germ
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ∃ g : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → Parameter × Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g
        (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) v) ∧
      g (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) v) = v ∧
      ∀ᶠ x in 𝓝 (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) v),
        totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) (g x) = x := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  apply RelativeOpenCover.inverse_germ
    (isOpenEmbedding_totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hjoint) v
  apply IsManifold.subset_maximalAtlas
  exact Or.inr ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) v,
    chart_mem_atlas _ v, rfl⟩

include hboundary hmix in
private theorem originalTotalInterior_inverse_germ
    (u : Parameter × IntrinsicInterior.Point k M) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ∃ g : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → Parameter × IntrinsicInterior.Point k M,
      ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g
        (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u) ∧
      g (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u) = u ∧
      ∀ᶠ x in 𝓝 (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) u),
        totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) (g x) = x := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  apply RelativeOpenCover.inverse_germ
    (isOpenEmbedding_totalInterior hδ (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) hzero hjoint) u
  apply IsManifold.subset_maximalAtlas
  exact Or.inl ⟨chartAt (ModelProd (EuclideanHalfSpace 1) (Model (k + 1))) u,
    chart_mem_atlas _ u, rfl⟩

include hC hinv hjoint hmix PE in
/-- At every genuine mixed overlap point the global scalar is smooth,
including the original parameter endpoints. -/
theorem contMDiffAt_originalEndToInteriorCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalCylinder (fun t p => C t p.val) (s, p)) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  obtain ⟨U, _, f, hzU, _, hf, _, _, _, hmatch⟩ :=
    exists_originalEndToInteriorCanonicalTransitionGerm
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N PE c d s w p hpoint hw hp
  obtain ⟨R, hR, hRp, hRI⟩ :=
    originalTotalCylinder_inverse_germ hδ C hboundary hzero hjoint hmix (s, p)
  let e := chartAt (Model k × ℝ) d.anchor
  let z : Parameter × Band δ (IntrinsicBoundary.Point k M) → ℝ × (Model k × ℝ) :=
    fun v => (v.1.val, e (endBandCoordinates v.2))
  have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun v : Parameter × Band δ (IntrinsicBoundary.Point k M) => v.1.val) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hband : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
      (fun v : Parameter × Band δ (IntrinsicBoundary.Point k M) => endBandCoordinates v.2) :=
    contMDiff_endBandCoordinates.comp contMDiff_snd
  have he : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) ∞ e
      (endBandCoordinates p) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := d.anchor)).contMDiffAt
      (e.open_source.mem_nhds hp.1.2)
  have hz : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ z (s, p) :=
    (ht (s, p)).prodMk_space (he.comp (s, p) (hband (s, p)))
  have hzR := hz.comp_of_eq hR hRp
  have hzx : (z ∘ R) (totalCylinder (fun t p => C t p.val) (s, p)) = z (s, p) := by
    rw [Function.comp_apply, hRp]
  have hlocal : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞ (f ∘ z ∘ R)
      (totalCylinder (fun t p => C t p.val) (s, p)) :=
    (hf.contDiffAt (U.isOpen.mem_nhds hzU)).contMDiffAt.comp_of_eq hzR hzx
  apply hlocal.congr_of_eventuallyEq
  have hnU := hzR.continuousAt.preimage_mem_nhds
    (U.isOpen.mem_nhds (hzx.symm ▸ hzU))
  have hnD := hR.continuousAt.preimage_mem_nhds
    (d.isOpen_baseDomain.mem_nhds (hRp.symm ▸ hp))
  filter_upwards [hRI, hnU, hnD] with x hx hxU hxD
  obtain ⟨v, _, _, hattach, hscalar⟩ :=
    hmatch (R x).1 (R x).2 hxD.1.2 hxU
  change originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d x =
    f (z (R x))
  exact (congrArg
    (originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d)
    (hattach.trans hx).symm).trans
      ((originalEndToInteriorCanonicalTransition_apply
        hδ C hemb hboundary hzero hjoint J N c d ((R x).1, v) (R x) hattach).trans hscalar.symm)

include hC hinv hjoint hmix in
/-- Reverse mixed smoothness is derived from the reverse real transition
germ and the literal smooth interior inverse patch. -/
theorem contMDiffAt_originalInteriorToEndCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) (s, w)) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  obtain ⟨U, _, f, hzU, _, hf, _, _, _, hmatch⟩ :=
    exists_originalInteriorToEndCanonicalTransitionGerm
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N c d s w p hpoint hw hp
  obtain ⟨R, hR, hRw, hRI⟩ :=
    originalTotalInterior_inverse_germ hδ C hboundary hzero hjoint hmix (s, w)
  let e := chartAt (Model (k + 1)) c.anchor
  let z : Parameter × IntrinsicInterior.Point k M → ℝ × Model (k + 1) :=
    fun v => (v.1.val, e v.2)
  have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun v : Parameter × IntrinsicInterior.Point k M => v.1.val) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have he : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ e w :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor)).contMDiffAt
      (e.open_source.mem_nhds hw.1.2)
  have hz : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ z (s, w) :=
    (ht (s, w)).prodMk_space (he.comp (s, w) contMDiffAt_snd)
  have hzR := hz.comp_of_eq hR hRw
  have hzx : (z ∘ R) (totalInterior (fun t p => C t p.val) (s, w)) = z (s, w) := by
    rw [Function.comp_apply, hRw]
  have hlocal : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞ (f ∘ z ∘ R)
      (totalInterior (fun t p => C t p.val) (s, w)) :=
    (hf.contDiffAt (U.isOpen.mem_nhds hzU)).contMDiffAt.comp_of_eq hzR hzx
  apply hlocal.congr_of_eventuallyEq
  have hnU := hzR.continuousAt.preimage_mem_nhds
    (U.isOpen.mem_nhds (hzx.symm ▸ hzU))
  have hnD := hR.continuousAt.preimage_mem_nhds
    (c.isOpen_baseDomain.mem_nhds (hRw.symm ▸ hw))
  filter_upwards [hRI, hnU, hnD] with x hx hxU hxD
  obtain ⟨q, _, _, hattach, hscalar⟩ :=
    hmatch (R x).1 (R x).2 hxD.1.2 hxU
  change originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d x =
    f (z (R x))
  exact (congrArg
    (originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d) hx.symm).trans
      ((originalInteriorToEndCanonicalTransition_apply
        hδ C hemb hboundary hzero hjoint J N c d (R x) ((R x).1, q) hattach).trans hscalar.symm)

include hC hinv hjoint hmix PE in
/-- Smoothness holds on the full intersection of the two image chart
domains in the original completed total base. -/
theorem contMDiffOn_originalEndToInteriorCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  intro x hx
  obtain ⟨⟨s, w⟩, hw, hix⟩ := hx.1
  obtain ⟨⟨t, p⟩, hp, hjx⟩ := hx.2
  have hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (t, p) := hix.trans hjx.symm
  have hst := (totalInterior_eq_totalCylinder_iff (fun t p => C t p.val)
    hboundary (s, w) (t, p)).mp hpoint |>.1
  dsimp only at hst
  subst t
  rw [← hjx]
  exact (contMDiffAt_originalEndToInteriorCanonicalTransition
    hδ C hemb hC hboundary hinv hzero hjoint hmix J N PE c d s w p hpoint hw hp).contMDiffWithinAt

include hC hinv hjoint hmix in
/-- The reverse transition is smooth on that same full image overlap. -/
theorem contMDiffOn_originalInteriorToEndCanonicalTransition
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  intro x hx
  obtain ⟨⟨s, w⟩, hw, hix⟩ := hx.1
  obtain ⟨⟨t, p⟩, hp, hjx⟩ := hx.2
  have hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (t, p) := hix.trans hjx.symm
  have hst := (totalInterior_eq_totalCylinder_iff (fun t p => C t p.val)
    hboundary (s, w) (t, p)).mp hpoint |>.1
  dsimp only at hst
  subst t
  rw [← hix]
  exact (contMDiffAt_originalInteriorToEndCanonicalTransition
    hδ C hemb hC hboundary hinv hzero hjoint hmix J N c d s w p hpoint hw hp).contMDiffWithinAt

/-- The mixed scalar acts on the canonical-square fiber model by complex
scalar multiplication, viewed as a real continuous linear map. -/
def originalEndToInteriorCanonicalTransitionMap
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ℂ →L[ℝ] ℂ :=
  originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d x •
    ContinuousLinearMap.id ℝ ℂ

/-- The reverse mixed transition on the same fiber model. -/
def originalInteriorToEndCanonicalTransitionMap
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ℂ →L[ℝ] ℂ :=
  originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d x •
    ContinuousLinearMap.id ℝ ℂ

include hC hinv hjoint hmix PE in
theorem contMDiffOn_originalEndToInteriorCanonicalTransitionMap
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (originalEndToInteriorCanonicalTransitionMap hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn
    (contMDiffOn_originalEndToInteriorCanonicalTransition
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N PE c d)

include hC hinv hjoint hmix in
theorem contMDiffOn_originalInteriorToEndCanonicalTransitionMap
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (originalInteriorToEndCanonicalTransitionMap hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn
    (contMDiffOn_originalInteriorToEndCanonicalTransition
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N c d)

private def patchScalar {U X : Type*} (i : U → X) (f : U → ℂ) (x : X) : ℂ := by
  classical
  exact if h : ∃ u, i u = x then f h.choose else 0

private theorem patchScalar_apply {U X : Type*} (i : U → X)
    (hi : Function.Injective i) (f : U → ℂ) (u : U) :
    patchScalar i f (i u) = f u := by
  classical
  have h : ∃ v, i v = i u := ⟨u, rfl⟩
  rw [patchScalar, dite_eq_left h]
  exact congrArg f (hi h.choose_spec)

/-- The original interior scalar transition transported to the completed
base through the unique actual interior preimage. -/
def originalInteriorCanonicalTransition
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ :=
  patchScalar (totalInterior (fun t p => C t p.val)) (c.transition (P := N) d)

/-- The original full-cylinder scalar transition on the completed base. -/
def originalEndCanonicalTransition
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ :=
  patchScalar (totalCylinder (fun t p => C t p.val)) (c.transition (N := N) d)

include hjoint in
theorem originalInteriorCanonicalTransition_apply
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M) :
    originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t p => C t p.val) u) = c.transition (P := N) d u :=
  patchScalar_apply _
    (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective _ u

include hjoint in
theorem originalEndCanonicalTransition_apply
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d
      (totalCylinder (fun t p => C t p.val) v) = c.transition (N := N) d v :=
  patchScalar_apply _
    (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective _ v

include hC hinv hjoint hmix in
/-- The same-branch interior transition is smooth on the full intersection
of the promoted base domains. -/
theorem contMDiffOn_originalInteriorCanonicalTransition
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalInterior (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  intro x hx
  obtain ⟨u, huc, hu⟩ := hx.1
  obtain ⟨v, hvd, hv⟩ := hx.2
  have hvu := (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective
    (hv.trans hu.symm)
  subst v
  obtain ⟨R, hR, hRu, hRI⟩ :=
    originalTotalInterior_inverse_germ hδ C hboundary hzero hjoint hmix u
  have hf := (c.smooth_transition (P := N) hC hinv d).contMDiffAt
    ((c.isOpen_baseDomain.inter d.isOpen_baseDomain).mem_nhds ⟨huc, hvd⟩)
  rw [← hu]
  apply ((hf.comp_of_eq hR hRu).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hRI] with y hy
  exact (congrArg (originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d)
    hy.symm).trans (originalInteriorCanonicalTransition_apply
      hδ C hemb hboundary hzero hjoint J N c d (R y))

include hC hinv hjoint hmix PE in
/-- Same-branch end smoothness retains the whole original signed cylinder. -/
theorem contMDiffOn_originalEndCanonicalTransition
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d)
      (totalCylinder (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  intro x hx
  obtain ⟨u, huc, hu⟩ := hx.1
  obtain ⟨v, hvd, hv⟩ := hx.2
  have hvu := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective
    (hv.trans hu.symm)
  subst v
  obtain ⟨R, hR, hRu, hRI⟩ :=
    originalTotalCylinder_inverse_germ hδ C hboundary hzero hjoint hmix u
  have hf := (c.smooth_transition (N := N) (P := PE) hC hinv d).contMDiffAt
    ((c.isOpen_baseDomain.inter d.isOpen_baseDomain).mem_nhds ⟨huc, hvd⟩)
  rw [← hu]
  apply ((hf.comp_of_eq hR hRu).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hRI] with y hy
  exact (congrArg (originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d)
    hy.symm).trans (originalEndCanonicalTransition_apply
      hδ C hemb hboundary hzero hjoint J N c d (R y))

/-- The same-branch interior transition on the real linear fiber model. -/
def originalInteriorCanonicalTransitionMap
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ℂ →L[ℝ] ℂ :=
  originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d x •
    ContinuousLinearMap.id ℝ ℂ

/-- The same-branch full-cylinder transition on the real linear fiber model. -/
def originalEndCanonicalTransitionMap
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    ℂ →L[ℝ] ℂ :=
  originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d x •
    ContinuousLinearMap.id ℝ ℂ

include hC hinv hjoint hmix in
theorem contMDiffOn_originalInteriorCanonicalTransitionMap
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (originalInteriorCanonicalTransitionMap hδ C hemb hboundary hzero J N c d)
      (totalInterior (fun t p => C t p.val) '' c.baseDomain ∩
        totalInterior (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn
    (contMDiffOn_originalInteriorCanonicalTransition
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N c d)

include hC hinv hjoint hmix PE in
theorem contMDiffOn_originalEndCanonicalTransitionMap
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (originalEndCanonicalTransitionMap hδ C hemb hboundary hzero J N c d)
      (totalCylinder (fun t p => C t p.val) '' c.baseDomain ∩
        totalCylinder (fun t p => C t p.val) '' d.baseDomain) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn
    (contMDiffOn_originalEndCanonicalTransition
      hδ C hemb hC hboundary hinv hzero hjoint hmix J N PE c d)

include hjoint in
theorem originalEndToInteriorCanonicalTransitionMap_apply
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M)
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) u = totalCylinder (fun t p => C t p.val) v)
    (q : ℂ) :
    originalEndToInteriorCanonicalTransitionMap hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t p => C t p.val) u) q =
        squaredCoframeTransition (c.nativeCoframe N u) (d.nativeCoframe N v) * q := by
  change originalEndToInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
    (totalInterior (fun t p => C t p.val) u) * q = _
  rw [originalEndToInteriorCanonicalTransition_apply
    hδ C hemb hboundary hzero hjoint J N c d u v hpoint]

include hjoint in
theorem originalInteriorToEndCanonicalTransitionMap_apply
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M)
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) u = totalCylinder (fun t p => C t p.val) v)
    (q : ℂ) :
    originalInteriorToEndCanonicalTransitionMap hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t p => C t p.val) u) q =
        squaredCoframeTransition (d.nativeCoframe N v) (c.nativeCoframe N u) * q := by
  change originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N c d
    (totalInterior (fun t p => C t p.val) u) * q = _
  rw [originalInteriorToEndCanonicalTransition_apply
    hδ C hemb hboundary hzero hjoint J N c d u v hpoint]

include hjoint in
theorem originalInteriorCanonicalTransitionMap_apply
    (c d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (u : Parameter × IntrinsicInterior.Point k M) :
    originalInteriorCanonicalTransitionMap hδ C hemb hboundary hzero J N c d
      (totalInterior (fun t p => C t p.val) u) = c.transitionMap (P := N) d u := by
  change originalInteriorCanonicalTransition hδ C hemb hboundary hzero J N c d
    (totalInterior (fun t p => C t p.val) u) • ContinuousLinearMap.id ℝ ℂ = _
  rw [originalInteriorCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d u]
  rfl

include hjoint in
theorem originalEndCanonicalTransitionMap_apply
    (c d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (v : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    originalEndCanonicalTransitionMap hδ C hemb hboundary hzero J N c d
      (totalCylinder (fun t p => C t p.val) v) = c.transitionMap (N := N) d v := by
  change originalEndCanonicalTransition hδ C hemb hboundary hzero J N c d
    (totalCylinder (fun t p => C t p.val) v) • ContinuousLinearMap.id ℝ ℂ = _
  rw [originalEndCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d v]
  rfl

end FsFltz.Geometry.IntrinsicCompletionGluing
