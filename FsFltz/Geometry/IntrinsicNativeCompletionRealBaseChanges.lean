import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingDerivative
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas

/-!
# Real base changes for the intrinsic completion atlas

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). The forward and inverse
changes are real-open representatives of the actual native collar changes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section RealCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold 𝓘(ℝ, E) ∞ X]

/-- An original spatial chart is an actual real partial diffeomorphism:
its spatial model has no boundary. -/
def realSpatialChart (a : X) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X E ∞ where
  __ := chartAt E a
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace F Y]

/-- Extend a spatial change by the unchanged real parameter, before
restricting that parameter to the original interval. -/
def realParameterProduct
    (A : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) X Y ∞) :
    PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) (ℝ × X) (ℝ × Y) ∞ where
  toPartialEquiv := (PartialEquiv.refl ℝ).prod A.toPartialEquiv
  open_source := isOpen_univ.prod A.open_source
  open_target := isOpen_univ.prod A.open_target
  contMDiffOn_toFun := contMDiff_fst.contMDiffOn.prodMk
    (A.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk
    (A.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))

end RealCharts

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)

local instance extensionProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance extensionProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

section BaseChanges

local instance nativeParameterCharts {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] : ChartedSpace (ℝ × E) (ℝ × X) :=
  prodChartedSpace ℝ ℝ E X

local instance realParameterModelCharts {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ChartedSpace (ℝ × E) (ℝ × E) := chartedSpaceSelf _

/-- Real parameter times the original spatial chart, in the full real model. -/
def realParameterChart {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] (a : X) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × X) (ℝ × E) ∞ where
  __ := (realParameterProduct (realSpatialChart (E := E) a)).toOpenPartialHomeomorph
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod]
    convert (realParameterProduct (realSpatialChart (E := E) a)).contMDiffOn_toFun using 1 <;>
      first | rfl | exact chartedSpaceSelf_prod.symm
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod]
    convert (realParameterProduct (realSpatialChart (E := E) a)).contMDiffOn_invFun using 1 <;>
      first | rfl | exact chartedSpaceSelf_prod.symm


/-- Change between two original charts of the same spatial manifold,
with the real parameter unchanged. -/
def realParameterChartChange {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] (a b : X) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞ :=
  (realParameterChart (E := E) a).symm.trans (realParameterChart (E := E) b)

/-- Same-spatial-chart changes retain both coordinate directions at every
point belonging to the two original spatial chart sources. -/
theorem exists_realParameterChartChange {E X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ, E) ∞ X] (a b w : X) (s : ℝ)
    (ha : w ∈ (chartAt E a).source) (hb : w ∈ (chartAt E b).source) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞,
      (s, chartAt E a w) ∈ B.source ∧
      B (s, chartAt E a w) = (s, chartAt E b w) ∧
      (∀ (t : ℝ) (v : X), v ∈ (chartAt E a).source → v ∈ (chartAt E b).source →
        B (t, chartAt E a v) = (t, chartAt E b v)) ∧
      (∀ (t : ℝ) (v : X), v ∈ (chartAt E a).source → v ∈ (chartAt E b).source →
        B.symm (t, chartAt E b v) = (t, chartAt E a v)) := by
  let B := realParameterChartChange (E := E) a b
  have hsource : (s, chartAt E a w) ∈ B.source := by
    change (s, chartAt E a w) ∈ univ ×ˢ (chartAt E a).target ∧
      (s, (chartAt E a).symm (chartAt E a w)) ∈ univ ×ˢ (chartAt E b).source
    refine ⟨⟨mem_univ _, (chartAt E a).map_source ha⟩, mem_univ _, ?_⟩
    rwa [(chartAt E a).left_inv ha]
  have hf : ∀ (t : ℝ) (v : X), v ∈ (chartAt E a).source →
      v ∈ (chartAt E b).source → B (t, chartAt E a v) = (t, chartAt E b v) := by
    intro t v hva _
    change (t, chartAt E b ((chartAt E a).symm (chartAt E a v))) = _
    rw [(chartAt E a).left_inv hva]
  have hi : ∀ (t : ℝ) (v : X), v ∈ (chartAt E a).source →
      v ∈ (chartAt E b).source → B.symm (t, chartAt E b v) = (t, chartAt E a v) := by
    intro t v _ hvb
    change (t, chartAt E a ((chartAt E b).symm (chartAt E b v))) = _
    rw [(chartAt E b).left_inv hvb]
  exact ⟨B, hsource, hf s w ha hb, hf, hi⟩

end BaseChanges

local instance boundaryParameterProductCharts :
    ChartedSpace (ℝ × (Model k × ℝ)) (ℝ × (IntrinsicBoundary.Point k M × ℝ)) :=
  prodChartedSpace ℝ ℝ (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ)
local instance boundaryCollarCharts :
    ChartedSpace (ℝ × Model k) (ℝ × IntrinsicBoundary.Point k M) :=
  prodChartedSpace ℝ ℝ (Model k) (IntrinsicBoundary.Point k M)
local instance collarParameterProductCharts :
    ChartedSpace (ℝ × (ℝ × Model k)) (ℝ × (ℝ × IntrinsicBoundary.Point k M)) :=
  prodChartedSpace ℝ ℝ (ℝ × Model k) (ℝ × IntrinsicBoundary.Point k M)
local instance interiorParameterProductCharts :
    ChartedSpace (ℝ × Model (k + 1)) (ℝ × IntrinsicInterior.Point k M) :=
  prodChartedSpace ℝ ℝ (Model (k + 1)) (IntrinsicInterior.Point k M)

/-- The cylinder's outward radius is the negative inward collar coordinate. -/
def realEndParameterSignSwap :
    PartialDiffeomorph 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ × (ℝ × Model k))
      (ℝ × (IntrinsicBoundary.Point k M × ℝ))
      (ℝ × (ℝ × IntrinsicBoundary.Point k M)) ∞ where
  toFun z := (z.1, (-z.2.2, z.2.1))
  invFun z := (z.1, (z.2.2, -z.2.1))
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' z _ := by simp
  right_inv' z _ := by simp
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    have h : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k))) ∞
        (fun z : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (z.1, (-z.2.2, z.2.1))) :=
      contMDiff_fst.prodMk
      ((contMDiff_snd.comp contMDiff_snd).neg.prodMk
        (contMDiff_fst.comp contMDiff_snd))
    simpa only [modelWithCornersSelf_prod, boundaryParameterProductCharts,
      collarParameterProductCharts, boundaryCollarCharts, extensionProductCharts]
      using h.contMDiffOn
  contMDiffOn_invFun := by
    have h : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞
        (fun z : ℝ × (ℝ × IntrinsicBoundary.Point k M) => (z.1, (z.2.2, -z.2.1))) :=
      contMDiff_fst.prodMk
      ((contMDiff_snd.comp contMDiff_snd).prodMk
        (contMDiff_fst.comp contMDiff_snd).neg)
    simpa only [modelWithCornersSelf_prod, boundaryParameterProductCharts,
      collarParameterProductCharts, boundaryCollarCharts, extensionProductCharts]
      using h.contMDiffOn

/-- Re-express the smooth fields of the real collar change with self models,
keeping its partial homeomorphism and its maps literally unchanged. -/
def realMixedTransitionSelf (A : RealMixedTransition (k := k) (M := M)) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × (ℝ × Model k)) 𝓘(ℝ, ℝ × Model (k + 1))
      (ℝ × (ℝ × IntrinsicBoundary.Point k M)) (ℝ × IntrinsicInterior.Point k M) ∞ where
  __ := A.toOpenPartialHomeomorph
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact A.contMDiffOn_toFun
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact A.contMDiffOn_invFun

/-- Conjugation of the actual mixed collar diffeomorphism by the original
real charts. Its inverse is the inverse of that same collar germ. -/
def realMixedChartChange
    (A : RealMixedTransition (k := k) (M := M))
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ × Model (k + 1))
      (ℝ × (Model k × ℝ)) (ℝ × Model (k + 1)) ∞ :=
  ((realParameterChart b).symm.trans (realEndParameterSignSwap (k := k) (M := M))).trans
    ((realMixedTransitionSelf A).trans (realParameterChart a))

variable (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)

include hδ hboundary hzero hjoint hmix in
/-- The real base change is a conjugate of the source-produced collar
diffeomorphism, and agrees with the actual original inclusions. -/
theorem exists_realMixedChartChange
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ)
    (s : Parameter) (w : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (hw : w ∈ (chartAt (Model (k + 1)) a).source)
    (hp : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (s, p)) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, ℝ × Model (k + 1))
        (ℝ × (Model k × ℝ)) (ℝ × Model (k + 1)) ∞,
      (s.val, chartAt (Model k × ℝ) b (endBandCoordinates p)) ∈ B.source ∧
      B (s.val, chartAt (Model k × ℝ) b (endBandCoordinates p)) =
        (s.val, chartAt (Model (k + 1)) a w) ∧
      (∀ (t : Parameter) (v : IntrinsicInterior.Point k M) (q : Band δ (IntrinsicBoundary.Point k M)),
        v ∈ (chartAt (Model (k + 1)) a).source →
        endBandCoordinates q ∈ (chartAt (Model k × ℝ) b).source →
        totalInterior (fun t p => C t p.val) (t, v) =
          totalCylinder (fun t p => C t p.val) (t, q) →
        (t.val, chartAt (Model k × ℝ) b (endBandCoordinates q)) ∈ B.source →
        B (t.val, chartAt (Model k × ℝ) b (endBandCoordinates q)) =
          (t.val, chartAt (Model (k + 1)) a v)) ∧
      (∀ (t : Parameter) (v : IntrinsicInterior.Point k M) (q : Band δ (IntrinsicBoundary.Point k M)),
        v ∈ (chartAt (Model (k + 1)) a).source →
        endBandCoordinates q ∈ (chartAt (Model k × ℝ) b).source →
        totalInterior (fun t p => C t p.val) (t, v) =
          totalCylinder (fun t p => C t p.val) (t, q) →
        (t.val, chartAt (Model (k + 1)) a v) ∈ B.target →
        B.symm (t.val, chartAt (Model (k + 1)) a v) =
          (t.val, chartAt (Model k × ℝ) b (endBandCoordinates q))) := by
  let ei := chartAt (Model (k + 1)) a
  let ee := chartAt (Model k × ℝ) b
  obtain ⟨_, hpos, _⟩ := (totalInterior_eq_totalCylinder_iff
    (fun t p => C t p.val) hboundary (s, w) (s, p)).mp hpoint
  obtain ⟨A, hpA, _, hparam, _, hforward, hback⟩ := hmix s p.val ⟨hpos, p.property.1⟩
  have hAw : (A (s.val, p.val)).2 = w := by
    have h := (hforward s p hpA).trans hpoint.symm
    exact congrArg Prod.snd
      ((isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective h)
  let B := realMixedChartChange A a b
  have hR : ∀ (t : Parameter) (q : Band δ (IntrinsicBoundary.Point k M)),
      endBandCoordinates q ∈ ee.source →
      (t.val, (-(ee.symm (ee (endBandCoordinates q))).2,
        (ee.symm (ee (endBandCoordinates q))).1)) = (t.val, q.val) := by
    intro t q hq
    rw [ee.left_inv hq]
    simp only [endBandCoordinates, neg_neg, Prod.mk.eta]
  have hsource : (s.val, ee (endBandCoordinates p)) ∈ B.source := by
    change ((s.val, ee (endBandCoordinates p)) ∈ (realParameterChart b).target ∧
      (realParameterChart b).symm (s.val, ee (endBandCoordinates p)) ∈
        (realEndParameterSignSwap (k := k) (M := M)).source) ∧
      (realEndParameterSignSwap (k := k) (M := M))
        ((realParameterChart b).symm (s.val, ee (endBandCoordinates p))) ∈ A.source ∧
      A ((realEndParameterSignSwap (k := k) (M := M))
        ((realParameterChart b).symm (s.val, ee (endBandCoordinates p)))) ∈
          (realParameterChart a).source
    refine ⟨⟨⟨mem_univ _, ee.map_source hp⟩, mem_univ _⟩, ?_, ?_⟩
    · change (s.val, (-(ee.symm (ee (endBandCoordinates p))).2,
        (ee.symm (ee (endBandCoordinates p))).1)) ∈ A.source
      rw [hR s p hp]; exact hpA
    · change A (s.val, (-(ee.symm (ee (endBandCoordinates p))).2,
        (ee.symm (ee (endBandCoordinates p))).1)) ∈ univ ×ˢ ei.source
      rw [hR s p hp]
      exact ⟨mem_univ _, hAw ▸ hw⟩
  have hret : ∀ (t : Parameter) (v : IntrinsicInterior.Point k M)
      (q : Band δ (IntrinsicBoundary.Point k M)), v ∈ ei.source →
      endBandCoordinates q ∈ ee.source →
      totalInterior (fun t p => C t p.val) (t, v) =
        totalCylinder (fun t p => C t p.val) (t, q) →
      (t.val, ee (endBandCoordinates q)) ∈ B.source →
      B (t.val, ee (endBandCoordinates q)) = (t.val, ei v) := by
    intro t v q _ hq hmatch hqB
    have hqA : (t.val, q.val) ∈ A.source := by
      have h := hqB.2.1
      change (t.val, (-(ee.symm (ee (endBandCoordinates q))).2,
        (ee.symm (ee (endBandCoordinates q))).1)) ∈ A.source at h
      rwa [hR t q hq] at h
    have hAv : (A (t.val, q.val)).2 = v := by
      have h := (hforward t q hqA).trans hmatch.symm
      exact congrArg Prod.snd
        ((isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective h)
    change ((A (t.val, (-(ee.symm (ee (endBandCoordinates q))).2,
      (ee.symm (ee (endBandCoordinates q))).1))).1,
      ei (A (t.val, (-(ee.symm (ee (endBandCoordinates q))).2,
        (ee.symm (ee (endBandCoordinates q))).1))).2) = _
    rw [hR t q hq, hparam _ hqA, hAv]
  have hinv : ∀ (t : Parameter) (v : IntrinsicInterior.Point k M)
      (q : Band δ (IntrinsicBoundary.Point k M)), v ∈ ei.source →
      endBandCoordinates q ∈ ee.source →
      totalInterior (fun t p => C t p.val) (t, v) =
        totalCylinder (fun t p => C t p.val) (t, q) →
      (t.val, ei v) ∈ B.target →
      B.symm (t.val, ei v) = (t.val, ee (endBandCoordinates q)) := by
    intro t v q hv _ hmatch hvB
    have hvA : (t.val, v) ∈ A.target := by
      have h := hvB.1.2
      change (t.val, ei.symm (ei v)) ∈ A.target at h
      rwa [ei.left_inv hv] at h
    obtain ⟨q', hAq', hq'⟩ := hback t v hvA
    have hqeq : q' = q := by
      have h := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective
        (hq'.trans hmatch)
      exact congrArg Prod.snd h
    have hAq : A.symm (t.val, v) = (t.val, q.val) := hqeq ▸ hAq'
    change ((A.symm (t.val, ei.symm (ei v))).1,
      ee ((A.symm (t.val, ei.symm (ei v))).2.2,
        -(A.symm (t.val, ei.symm (ei v))).2.1)) = _
    rw [ei.left_inv hv, hAq]
    rfl
  exact ⟨B, hsource, hret s w p hw hp hpoint hsource, hret, hinv⟩

end FsFltz.Geometry.IntrinsicCompletionGluing
