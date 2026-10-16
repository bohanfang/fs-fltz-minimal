import FsFltz.Geometry.IntrinsicNativeCompletionInteriorSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionEndSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionMixedCanonicalTransition
import FsFltz.Geometry.IntrinsicNativeCompletionReverseMixedCanonicalTransition

/-!
# The same original section in mixed canonical coordinates

Source: `geoemtric-part-fsf.tex`, lines 119–122 (smooth open extension),
`def:maslov`, lines 212–232, and `sec:lean`, lines 788–814. Mixed scalar
coordinates evaluate the independent canonical tensor square of one original
native section at a literally equal completion point. Their equality follows
from natural square multiplication and coframe reconstruction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

local instance mixedSectionProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

omit hδ hemb hboundary hzero J N hC hinv [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Equality in the actual total family gives literal equality of the native
slice points, rather than an abstract identification of their fibers. -/
theorem originalMixedNativePoint_eq_of_total_eq
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t q => C t q.val) (s, w) =
      totalCylinder (fun t q => C t q.val) (s, p)) :
    interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) w =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) p := by
  apply sliceIn_injective (fun t q => C t q.val) s
  simpa only [interiorIn, sliceIn_original, sliceIn_cylinder, totalInterior] using hpoint

include hC hinv in
/-- At an equal native completion point, the two tensor-square coordinates
evaluate the same original section, with the actual mixed coframe ratio. -/
theorem originalMixedSectionCoefficient
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) w =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) p)
    (hw : (s, w) ∈ c.baseDomain) :
    d.tensorCoordinateLinearMap (N := N) (s, p) (originalEndSection C J N σ (s, p)) =
      squaredCoframeTransition (c.nativeCoframe N (s, w)) (d.nativeCoframe N (s, p)) *
        c.tensorCoordinateLinearMap (P := N) (s, w) (originalInteriorSection C J N σ (s, w)) := by
  have hform :
      (canonicalSquareMap (originalInteriorComplex C J N (s, w))
        (originalInteriorSection C J N σ (s, w))).val =
      (canonicalSquareMap (originalEndComplex C J N (s, p))
        (originalEndSection C J N σ (s, p))).val := by
    exact congrArg (fun x => (canonicalSquareMap
      (N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap))
      (σ s x)).val) hpoint
  have hr := c.reconstruction (P := N) hC hinv hw
    (canonicalSquareMap _ (originalInteriorSection C J N σ (s, w)))
  rw [c.coefficient_squareMap] at hr
  rw [← d.coefficient_squareMap, ← hform, hr]
  change _ * squaredCoframeCoefficient (d.nativeCoframe N (s, p))
    (coframeSquaredGenerator (c.nativeCoframe N (s, w))) = _
  exact mul_comm _ _

include hC hinv in
/-- The reverse coefficient law evaluates the same independent tensor square. -/
theorem originalMixedSectionCoefficient_reverse
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) w =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C s q.val) p)
    (hp : (s, p) ∈ d.baseDomain) :
    c.tensorCoordinateLinearMap (P := N) (s, w) (originalInteriorSection C J N σ (s, w)) =
      squaredCoframeTransition (d.nativeCoframe N (s, p)) (c.nativeCoframe N (s, w)) *
        d.tensorCoordinateLinearMap (N := N) (s, p) (originalEndSection C J N σ (s, p)) := by
  have hform :
      (canonicalSquareMap (originalInteriorComplex C J N (s, w))
        (originalInteriorSection C J N σ (s, w))).val =
      (canonicalSquareMap (originalEndComplex C J N (s, p))
        (originalEndSection C J N σ (s, p))).val := by
    exact congrArg (fun x => (canonicalSquareMap
      (N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap))
      (σ s x)).val) hpoint
  have hr := d.reconstruction (N := N) hC hinv hp
    (canonicalSquareMap _ (originalEndSection C J N σ (s, p)))
  rw [d.coefficient_squareMap] at hr
  rw [← c.coefficient_squareMap, hform, hr]
  change _ * squaredCoframeCoefficient (c.nativeCoframe N (s, w))
    (coframeSquaredGenerator (d.nativeCoframe N (s, p))) = _
  exact mul_comm _ _

include hC hinv in
/-- A local coefficient extension transfers from the interior to the full
cylinder by the actual real mixed germ, also at parameter endpoints. -/
theorem originalSectionCoefficientExtension_interiorToEnd
    (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t q => C t q.val) (s, w) =
      totalCylinder (fun t q => C t q.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain)
    (hσ : c.HasSectionCoefficientExtension (P := N) σ (s, w)) :
    d.HasSectionCoefficientExtension (N := N) σ (s, p) := by
  obtain ⟨U, q, hwU, hUc, hq, heq⟩ := hσ
  obtain ⟨V, g, f, hpV, hg, hf, hg₀, hVd, _, hmatch⟩ :=
    exists_originalEndToInteriorCanonicalTransitionGerm hδ C hemb hC hboundary hinv hzero
      hjoint hmix J N PE c d s w p hpoint hw hp
  let G := fun z : ℝ × (Model k × ℝ) => (z.1, g z)
  have hG : ContDiffOn ℝ ∞ G V := contDiffOn_fst.prodMk hg
  let W : TopologicalSpace.Opens (ℝ × (Model k × ℝ)) :=
    ⟨(V : Set _) ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage V.isOpen U.isOpen⟩
  have hpW : (s.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates p)) ∈ W := by
    refine ⟨hpV, ?_⟩
    change (s.val, g (s.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates p))) ∈ U
    rwa [hg₀]
  refine ⟨W, fun z => f z * q (G z), hpW, (fun _ hz => hVd hz.1),
    (hf.mono inter_subset_left).mul
      (hq.comp (hG.mono inter_subset_left) (fun _ hz => hz.2)), ?_⟩
  intro t a ha hz
  obtain ⟨v, hv, hvg, hequal, hscalar⟩ := hmatch t a ha hz.1
  have hvU : (t.val, chartAt (Model (k + 1)) c.anchor v) ∈ U := by
    rw [hvg]
    exact hz.2
  have hvc : (t, v) ∈ c.baseDomain := ⟨⟨mem_univ _, hv⟩, hUc hvU⟩
  change f (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates a)) *
    q (t.val, g (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates a))) = _
  rw [hscalar, ← hvg, heq t v hv hvU]
  exact (originalMixedSectionCoefficient hδ C hemb hboundary hzero J N hC hinv c d σ
    t v a (originalMixedNativePoint_eq_of_total_eq C t v a hequal) hvc).symm

include hC hinv in
/-- A local coefficient extension transfers back to the interior using the
inverse real mixed germ and the reverse ratio of the same native section. -/
theorem originalSectionCoefficientExtension_endToInterior
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N)
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t q => C t q.val) (s, w) =
      totalCylinder (fun t q => C t q.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain)
    (hσ : d.HasSectionCoefficientExtension (N := N) σ (s, p)) :
    c.HasSectionCoefficientExtension (P := N) σ (s, w) := by
  obtain ⟨U, q, hpU, hUd, hq, heq⟩ := hσ
  obtain ⟨V, g, f, hwV, hg, hf, hg₀, hVc, _, hmatch⟩ :=
    exists_originalInteriorToEndCanonicalTransitionGerm hδ C hemb hC hboundary hinv hzero
      hjoint hmix J N c d s w p hpoint hw hp
  let G := fun z : ℝ × Model (k + 1) => (z.1, g z)
  have hG : ContDiffOn ℝ ∞ G V := contDiffOn_fst.prodMk hg
  let W : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
    ⟨(V : Set _) ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage V.isOpen U.isOpen⟩
  have hwW : (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ W := by
    refine ⟨hwV, ?_⟩
    change (s.val, g (s.val, chartAt (Model (k + 1)) c.anchor w)) ∈ U
    rwa [hg₀]
  refine ⟨W, fun z => f z * q (G z), hwW, (fun _ hz => hVc hz.1),
    (hf.mono inter_subset_left).mul
      (hq.comp (hG.mono inter_subset_left) (fun _ hz => hz.2)), ?_⟩
  intro t v hv hz
  obtain ⟨a, ha, hag, hequal, hscalar⟩ := hmatch t v hv hz.1
  have haU : (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates a)) ∈ U := by
    rw [hag]
    exact hz.2
  have had : (t, a) ∈ d.baseDomain := ⟨⟨mem_univ _, ha⟩, hUd haU⟩
  change f (t.val, chartAt (Model (k + 1)) c.anchor v) *
    q (t.val, g (t.val, chartAt (Model (k + 1)) c.anchor v)) = _
  rw [hscalar, ← hag, heq t a ha haU]
  exact (originalMixedSectionCoefficient_reverse hδ C hemb hboundary hzero J N hC hinv c d σ
    t v a (originalMixedNativePoint_eq_of_total_eq C t v a hequal) had).symm

end FsFltz.Geometry.IntrinsicCompletionGluing
