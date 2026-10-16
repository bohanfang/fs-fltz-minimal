import FsFltz.Geometry.IntrinsicNativeCompletionWholeCanonicalBundle
import FsFltz.Geometry.OriginalBundleMaslovSectionGraphExtension

/-!
# Restricting sections on the original completed total family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The same section is evaluated through the
actual slice equivalence and restricted through the actual two inclusions.
Parameter-endpoint open extensions remain a separate regularity obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry

private theorem fiberCast_section {X B : Type*} [TopologicalSpace B]
    (E : B → Type*) [∀ b, AddCommMonoid (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] (f : X → B) (σ : ∀ x, E (f x))
    {x y : X} (h : x = y) (e : f x = f y) :
    continuousLinearFiberCast E e (σ x) = σ y := by
  subst y
  rfl

namespace IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ}
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))

/-- The original fiberwise section, regarded on the actual completed total base. -/
def originalTotalSection (σ : OriginalNativeCanonicalSection C J N)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    OriginalTotalCanonicalTensorSquare C J N x :=
  σ (parameter (fun t p => C t p.val) x)
    ((fiberEquiv (fun t p => C t p.val) _).symm ⟨x, rfl⟩)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Interior restriction preserves the supplied section in its actual fibers. -/
theorem originalTotalSection_interior (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M) :
    originalTotalInteriorFiberEquiv C J N p
      (originalTotalSection C J N σ (totalInterior (fun t q => C t q.val) p)) =
        originalInteriorSection C J N σ p := by
  have hi : (fiberEquiv (fun t q => C t q.val) p.1)
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2) =
      ⟨totalInterior (fun t q => C t q.val) p, rfl⟩ := by
    apply Subtype.ext
    rfl
  apply fiberCast_section (CanonicalTensorSquare (n := n))
    (fun z => N.symm.toContinuousLinearMap.comp ((J p.1 z).comp N.toContinuousLinearMap))
    (σ p.1) _
  change (fiberEquiv (fun t q => C t q.val) p.1).symm _ = _
  rw [← hi, Equiv.symm_apply_apply]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- End restriction preserves the supplied section on the full signed cylinder. -/
theorem originalTotalSection_end (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    originalTotalEndFiberEquiv C J N p
      (originalTotalSection C J N σ (totalCylinder (fun t q => C t q.val) p)) =
        originalEndSection C J N σ p := by
  have hi : (fiberEquiv (fun t q => C t q.val) p.1)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2) =
      ⟨totalCylinder (fun t q => C t q.val) p, rfl⟩ := by
    apply Subtype.ext
    exact sliceIn_cylinder _ _ _
  apply fiberCast_section (CanonicalTensorSquare (n := n))
    (fun z => N.symm.toContinuousLinearMap.comp ((J p.1 z).comp N.toContinuousLinearMap))
    (σ p.1) _
  change (fiberEquiv (fun t q => C t q.val) p.1).symm _ = _
  rw [← hi, Equiv.symm_apply_apply]

variable (hδ : 0 < δ)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
  (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
  (hJsq : ∀ s x v, J s x (J s x v) = -v)

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- Native smoothness in the independently constructed whole completed bundle. -/
def IsSmoothOriginalTotalSection (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  letI := totalFamilyChartedSpace hδ C hzero hjoint
  let a := originalTotalCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  ContMDiff (familyModel (k + 1)) ((familyModel (k + 1)).prod 𝓘(ℝ, ℂ)) ∞
    (fun x => (⟨x, originalTotalSection C J N σ x⟩ :
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N)))

set_option maxHeartbeats 800000 in
/-- Whole-bundle native smoothness implies smoothness in the original
interior bundle through the proved actual fiber identifications. -/
theorem IsSmoothOriginalTotalSection.interior
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalTotalSection C J N hδ hemb hboundary hzero hjoint hC hinv
      hmix P hJI hJE hJsq σ) :
    IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJI hJsq σ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let aT := originalTotalCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
  let := aT.totalSpaceTopology
  let := aT.toFiberBundle
  let := aT.toVectorBundle
  let := aT.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  let aI := originalInteriorCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N hC hinv hJI hJsq
  let := aI.totalSpaceTopology
  let := aI.toFiberBundle
  let := aI.toVectorBundle
  let := aI.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  intro p
  let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
  have hp := mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJI hJsq p
  let eI := aI.trivializationOfMemPretrivializationAtlas
    (show c.tensorPretrivialization (P := N) hC hinv ∈ aI.pretrivializationAtlas from ⟨c, rfl⟩)
  let : MemTrivializationAtlas eI := ⟨_, ⟨c, rfl⟩, rfl⟩
  apply (eI.contMDiffAt_section_iff hp).mpr
  let eT := aT.trivializationOfMemPretrivializationAtlas
    (show c.totalTensorPretrivialization N hjoint hC hinv ∈ aT.pretrivializationAtlas from
      ⟨Sum.inl c, rfl⟩)
  let : MemTrivializationAtlas eT := ⟨_, ⟨Sum.inl c, rfl⟩, rfl⟩
  have hpT : totalInterior (fun t q => C t q.val) p ∈ eT.baseSet := ⟨p, hp, rfl⟩
  have hs := (eT.contMDiffAt_section_iff hpT).mp
    (hσ (totalInterior (fun t q => C t q.val) p))
  have hc := hs.comp p (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix p)
  apply hc.congr_of_eventuallyEq
  filter_upwards [c.isOpen_baseDomain.mem_nhds hp] with q hq
  change (c.tensorPretrivialization (P := N) hC hinv
    ⟨q, originalInteriorSection C J N σ q⟩).2 =
    (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalInterior (fun t r => C t r.val) q,
        originalTotalSection C J N σ (totalInterior (fun t r => C t r.val) q)⟩).2
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq,
    originalTotalSection_interior]
  rfl

set_option maxHeartbeats 800000 in
/-- Whole-bundle native smoothness implies smoothness on the entire original
signed-cylinder bundle through the proved actual fiber identifications. -/
theorem IsSmoothOriginalTotalSection.end
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalTotalSection C J N hδ hemb hboundary hzero hjoint hC hinv
      hmix P hJI hJE hJsq σ) :
    IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJE hJsq σ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let aT := originalTotalCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero hjoint J N hC hinv hmix P hJI hJE hJsq
  let := aT.totalSpaceTopology
  let := aT.toFiberBundle
  let := aT.toVectorBundle
  let := aT.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  let aI := originalEndCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N P hC hinv hJE hJsq
  let := aI.totalSpaceTopology
  let := aI.toFiberBundle
  let := aI.toVectorBundle
  let := aI.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  intro p
  let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
  have hp := mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJE hJsq p
  let eI := aI.trivializationOfMemPretrivializationAtlas
    (show c.tensorPretrivialization (N := N) hC hinv ∈ aI.pretrivializationAtlas from ⟨c, rfl⟩)
  let : MemTrivializationAtlas eI := ⟨_, ⟨c, rfl⟩, rfl⟩
  apply (eI.contMDiffAt_section_iff hp).mpr
  let eT := aT.trivializationOfMemPretrivializationAtlas
    (show c.totalTensorPretrivialization N hjoint hC hinv ∈ aT.pretrivializationAtlas from
      ⟨Sum.inr c, rfl⟩)
  let : MemTrivializationAtlas eT := ⟨_, ⟨Sum.inr c, rfl⟩, rfl⟩
  have hpT : totalCylinder (fun t q => C t q.val) p ∈ eT.baseSet := ⟨p, hp, rfl⟩
  have hs := (eT.contMDiffAt_section_iff hpT).mp
    (hσ (totalCylinder (fun t q => C t q.val) p))
  have hc := hs.comp p (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix p)
  apply hc.congr_of_eventuallyEq
  filter_upwards [c.isOpen_baseDomain.mem_nhds hp] with q hq
  change (c.tensorPretrivialization (N := N) hC hinv
    ⟨q, originalEndSection C J N σ q⟩).2 =
    (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalCylinder (fun t r => C t r.val) q,
        originalTotalSection C J N σ (totalCylinder (fun t r => C t r.val) q)⟩).2
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq,
    originalTotalSection_end]
  rfl

/-- The whole original section reaches both full-tensor grading consumers.
Only endpoint graph extensions remain explicit; branch smoothness is proved
by restriction from the whole native bundle. -/
theorem IsSmoothOriginalTotalSection.gradingSectionGerms
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalTotalSection C J N hδ hemb hboundary hzero hjoint hC hinv
      hmix P hJI hJE hJsq σ)
    (hendI : ∀ (p : Parameter × IntrinsicInterior.Point k M),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N σ p)
    (hendE : ∀ (p : Parameter × Band δ (IntrinsicBoundary.Point k M)),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N P σ p)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) N ∧
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  constructor
  · exact originalNativeInteriorGradingSectionGerms_of_nativeSmooth_and_endpointGraphs
      N hC hinv hJI hJsq σ
      (hσ.interior C J N hδ hemb hboundary hzero hjoint hC hinv hmix P hJI hJE hJsq σ)
      hendI hnσ
  · exact originalNativeEndGradingSectionGerms_of_nativeSmooth_and_endpointGraphs
      N P hC hinv hJE hJsq σ
      (hσ.end C J N hδ hemb hboundary hzero hjoint hC hinv hmix P hJI hJE hJsq σ)
      hendE hnσ

end IntrinsicCompletionGluing
end FsFltz.Geometry
