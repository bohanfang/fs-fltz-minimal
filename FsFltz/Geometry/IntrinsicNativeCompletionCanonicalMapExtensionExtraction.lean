import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalMapExtensionTransfer
import FsFltz.Geometry.IntrinsicNativeCompletionWholeSectionCorrespondence

/-!
# Extracting the supplied section from arbitrary-map extension regularity

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). The arbitrary-map condition
is specialized to the actual graph of the supplied original section. Its
last coordinate gives the original coefficient; the original tensor and
section are preserved in the native graph and grading consumers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))

/-- The actual graph map of the original section on the actual completed total base. -/
def originalTotalSectionGraph (σ : OriginalNativeCanonicalSection C J N)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N) :=
  ⟨x, originalTotalSection C J N σ x⟩

variable (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

local instance mapExtractionProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

/-- The last coordinate of a full map extension is the original interior
coefficient of the supplied section. -/
theorem originalInteriorCoefficientExtension_of_chartMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hmap : HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ))
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain) :
    c.HasSectionCoefficientExtension (P := N) σ p := by
  let cT : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n) := .inl c
  obtain ⟨U, G, hpU, hG, hU, heG⟩ := hmap cT cT p hp ⟨p, hp, rfl⟩
  refine ⟨U, fun z => (G z).2, hpU, hU, contDiff_snd.contDiffOn.comp hG (fun _ _ => mem_univ _), ?_⟩
  intro s w hw hz
  have hq : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hw⟩, hU hz⟩
  obtain ⟨hd, he⟩ := heG (s, w) hq hz
  have h := congrArg Prod.snd he
  change (G _).2 = (c.totalTensorPretrivialization N hjoint hC hinv
    ⟨totalInterior (fun t q => C t q.val) (s, w),
      originalTotalSection C J N σ (totalInterior (fun t q => C t q.val) (s, w))⟩).2 at h
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq,
    originalTotalSection_interior] at h
  exact h

/-- The same extraction retains every radius of the original signed cylinder. -/
theorem originalEndCoefficientExtension_of_chartMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hmap : HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ))
    (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain) :
    c.HasSectionCoefficientExtension (N := N) σ p := by
  let cT : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n) := .inr c
  obtain ⟨U, G, hpU, hG, hU, heG⟩ := hmap cT cT p hp ⟨p, hp, rfl⟩
  refine ⟨U, fun z => (G z).2, hpU, hU, contDiff_snd.contDiffOn.comp hG (fun _ _ => mem_univ _), ?_⟩
  intro s w hw hz
  have hq : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hw⟩, hU hz⟩
  obtain ⟨hd, he⟩ := heG (s, w) hq hz
  have h := congrArg Prod.snd he
  change (G _).2 = (c.totalTensorPretrivialization N hjoint hC hinv
    ⟨totalCylinder (fun t q => C t q.val) (s, w),
      originalTotalSection C J N σ (totalCylinder (fun t q => C t q.val) (s, w))⟩).2 at h
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq,
    originalTotalSection_end] at h
  exact h


namespace OriginalInteriorCanonicalChart

variable {hδ C hemb hboundary hzero J}

/-- The extracted original coefficient reconstructs a smooth native graph
in the independently extending original bundle. -/
theorem nativeOpenGraphExtension_of_sectionCoefficient
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M)
    (hc : c.HasSectionCoefficientExtension (P := N) σ p) :
    c.HasNativeOpenGraphExtension N σ p := by
  obtain ⟨U, q, hpU, hU, hq, heq⟩ := hc
  let b := c.nativeOpenPatch N
  let f : U → b.domain := fun z => ⟨z.val, hU z.property⟩
  let G := b.graphOfScalar f (fun z : U => q z.val)
  refine ⟨U, hU, hpU, G, ?_, ?_⟩
  · have hf : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞ f := by
      apply (ContMDiff.subtypeVal_comp_iff b.domain f).mp
      exact contMDiff_subtype_val
    have hq' : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, ℂ) ∞
        (fun z : U => q z.val) := by
      intro z
      exact contMDiffAt_subtype_iff.mpr (contMDiffAt_iff_contDiffAt.mpr
        (hq.contDiffAt (U.isOpen.mem_nhds z.property)))
    exact b.smooth_graphOfScalar 𝓘(ℝ, ℝ × Model (k + 1)) f _ hf hq'
  · intro s w hw hz
    dsimp only [G, NativeCoordinateCanonicalPatch.graphOfScalar, f,
      openGraphValue, openFiberInclusion, LinearMap.comp_apply]
    rw [heq s w hw hz]
    rfl

end OriginalInteriorCanonicalChart

namespace OriginalEndCanonicalChart

variable {hδ C hemb hboundary hzero J}

/-- The original full-cylinder coefficient reconstructs the corresponding
native graph without changing the supplied section. -/
theorem nativeOpenGraphExtension_of_sectionCoefficient
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hc : c.HasSectionCoefficientExtension (N := N) σ p) :
    c.HasNativeOpenGraphExtension N P σ p := by
  obtain ⟨U, q, hpU, hU, hq, heq⟩ := hc
  let b := c.nativeOpenPatch P
  let f : U → b.domain := fun z => ⟨z.val, hU z.property⟩
  let G := b.graphOfScalar f (fun z : U => q z.val)
  refine ⟨U, hU, hpU, G, ?_, ?_⟩
  · have hf : ContMDiff 𝓘(ℝ, ℝ × (Model k × ℝ))
        𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ f := by
      apply (ContMDiff.subtypeVal_comp_iff b.domain f).mp
      exact contMDiff_subtype_val
    have hq' : ContMDiff 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℂ) ∞
        (fun z : U => q z.val) := by
      intro z
      exact contMDiffAt_subtype_iff.mpr (contMDiffAt_iff_contDiffAt.mpr
        (hq.contDiffAt (U.isOpen.mem_nhds z.property)))
    exact b.smooth_graphOfScalar 𝓘(ℝ, ℝ × (Model k × ℝ)) f _ hf hq'
  · intro s w hw hz
    dsimp only [G, NativeCoordinateCanonicalPatch.graphOfScalar, f,
      openGraphValue, openFiberInclusion, LinearMap.comp_apply]
    rw [heq s w hw hz]
    rfl

end OriginalEndCanonicalChart

variable (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
  (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
  (hJsq : ∀ s x v, J s x (J s x v) = -v)

include hmix P in
/-- Actual chart transfer puts the arbitrary-map regularity of the section
graph into every original source and target chart. Its projection is the
identity, so the continuity premise is proved without extra regularity. -/
theorem originalTotalSectionGraph_chartMapExtensions_of_local
    (σ : OriginalNativeCanonicalSection C J N)
    (hlocal : HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ)) :
    HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ) := by
  exact originalTotalChartMapExtensions_of_localMapExtensions hδ C hemb hboundary hzero J N
    hjoint hC hinv hmix P (originalTotalSectionGraph C J N σ) continuous_id hlocal

include P hJI hJE hJsq in
/-- The full-map extension property supplies the established total-point
coefficient interface for this exact original section. -/
theorem originalTotalLocalSectionExtensions_of_chartMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hmap : HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ)) :
    HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro x
  rcases totalInterior_cylinder_cover hδ (fun t p => C t p.val) hzero x with ⟨p, hp⟩ | ⟨p, hp⟩
  · let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
    have hpc := mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
    exact Or.inl ⟨p, c, hp, hpc,
      originalInteriorCoefficientExtension_of_chartMapExtensions hδ C hemb hboundary hzero J N
        hjoint hC hinv σ hmap c p hpc⟩
  · let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
    have hpc := mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
    exact Or.inr ⟨p, c, hp, hpc,
      originalEndCoefficientExtension_of_chartMapExtensions hδ C hemb hboundary hzero J N
        hjoint hC hinv σ hmap c p hpc⟩

include hmix P hJI hJE hJsq in
/-- Arbitrary source and target chart witnesses give the old coefficient
interface only after actual chart transfer and extraction. -/
theorem originalTotalLocalSectionExtensions_of_localMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hlocal : HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ)) :
    HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero J N σ := by
  exact originalTotalLocalSectionExtensions_of_chartMapExtensions hδ C hemb hboundary hzero J N
    hjoint hC hinv P hJI hJE hJsq σ
      (originalTotalSectionGraph_chartMapExtensions_of_local hδ C hemb hboundary hzero J N
        hjoint hC hinv hmix P σ hlocal)

/-- The full-map extension property produces native graph extensions at
both parameter endpoints and reaches the existing whole-section grading
consumer with the same original tensor and the same supplied section. -/
theorem IsSmoothOriginalTotalSection.gradingSectionGerms_of_chartMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalTotalSection C J N hδ hemb hboundary hzero hjoint hC hinv
      hmix P hJI hJE hJsq σ)
    (hmap : HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ))
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) N ∧
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  apply IsSmoothOriginalTotalSection.gradingSectionGerms C J N hδ hemb hboundary hzero
    hjoint hC hinv hmix P hJI hJE hJsq σ hσ _ _ hnσ
  · intro p _
    let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
    have hp := mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
    refine ⟨c, hp, ?_⟩
    exact c.nativeOpenGraphExtension_of_sectionCoefficient N σ p
      (originalInteriorCoefficientExtension_of_chartMapExtensions hδ C hemb hboundary hzero J N
        hjoint hC hinv σ hmap c p hp)
  · intro p _
    let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
    have hp := mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
    refine ⟨c, hp, ?_⟩
    exact c.nativeOpenGraphExtension_of_sectionCoefficient N P σ p
      (originalEndCoefficientExtension_of_chartMapExtensions hδ C hemb hboundary hzero J N
        hjoint hC hinv σ hmap c p hp)

/-- The chosen-chart-independent local-map entry point for the existing
whole-section grading consumer. No endpoint graph is assumed separately. -/
theorem IsSmoothOriginalTotalSection.gradingSectionGerms_of_localMapExtensions
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalTotalSection C J N hδ hemb hboundary hzero hjoint hC hinv
      hmix P hJI hJE hJsq σ)
    (hlocal : HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv
      (originalTotalSectionGraph C J N σ))
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) N ∧
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  exact IsSmoothOriginalTotalSection.gradingSectionGerms_of_chartMapExtensions hδ C hemb hboundary
    hzero J N hjoint hC hinv hmix P hJI hJE hJsq σ hσ
      (originalTotalSectionGraph_chartMapExtensions_of_local hδ C hemb hboundary hzero J N
        hjoint hC hinv hmix P σ hlocal) hnσ

end FsFltz.Geometry.IntrinsicCompletionGluing
