import FsFltz.Geometry.OriginalBundleMaslovSectionExtraction
import FsFltz.Geometry.NativeCanonicalSectionGraphExtension

/-!
# Native graph extensions in independently constructed original charts

Source: `geoemtric-part-fsf.tex`, smooth extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 788–814.
The original coframe determines a canonical-square bundle on a genuine
real-open chart, before a section is chosen. Original fibers map into it by
their independently constructed line coordinates. Natural square multiplication
recovers the full original spatial-chart tensor through its actual differential.
Smooth native graph extensions of this constructed inclusion produce scalar
extension germs. Existence of those graph extensions from bare boundary
`ContMDiff`, and the whole original mixed bundle, are separate foundations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.NativeCoordinateCanonicalPatch

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {P : Model (2 * n) ≃L[ℝ] F} {K : E → F →L[ℝ] F} {A : Set E}
  (c : NativeCoordinateCanonicalPatch P K A)

/-- The given coframe is an atlas chart on the independently extending bundle. -/
def openCoframeChart : VerticalCanonicalChart 𝓘(ℝ, E) c.complex where
  domain := univ
  isOpen_domain := isOpen_univ
  coframe := fun z => c.normalizedCoframe z.val
  smooth_coframe := by
    intro z _
    exact (contMDiffAt_subtype_iff.mpr (contMDiffAt_iff_contDiffAt.mpr
      (c.smooth_normalizedCoframe.contDiffAt
        (c.domain.isOpen.mem_nhds z.property)))).contMDiffWithinAt
  invertible_coframe := fun z _ => c.invertible_normalizedCoframe z.property
  intertwines_coframe := fun z _ => coframeComplexStructure_intertwines _
    (c.invertible_normalizedCoframe z.property)

open scoped Classical in
/-- A native graph map yields its scalar in the original extending coframe. -/
def graphCoefficient (U : TopologicalSpace.Opens E)
    (G : U → Bundle.TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (z : E) : ℂ :=
  if hz : z ∈ U then squaredCoframeCoefficient (c.normalizedCoframe z)
    (canonicalSquareMap (c.complex (G ⟨z, hz⟩).proj) (G ⟨z, hz⟩).snd).val else 0

theorem graphCoefficient_apply (U : TopologicalSpace.Opens E)
    (G : U → Bundle.TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    {z : E} (hz : z ∈ U) : c.graphCoefficient U G z =
      squaredCoframeCoefficient (c.normalizedCoframe z)
        (canonicalSquareMap (c.complex (G ⟨z, hz⟩).proj) (G ⟨z, hz⟩).snd).val := by
  simp only [graphCoefficient, hz, ↓reduceDIte]

/-- Scalar regularity follows from native graph smoothness; it is not an input. -/
theorem smooth_graphCoefficient (U : TopologicalSpace.Opens E)
    (hU : (U : Set E) ⊆ c.domain)
    (G : U → Bundle.TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (hG : let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
      letI := a.totalSpaceTopology
      letI := a.toFiberBundle
      ContMDiff 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞ G) :
    ContDiffOn ℝ ∞ (c.graphCoefficient U G) U := by
  have hT := verticalCanonicalTensorSquareMap_smooth c.smooth_complex c.complex_sq G hG
  let C : U → Model (2 * n) →L[ℝ] TangentCoordinates n :=
    fun z => c.normalizedCoframe z.val
  have hC : ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ, Model (2 * n) →L[ℝ] TangentCoordinates n) ∞ C := by
    intro z
    exact contMDiffAt_subtype_iff.mpr (contMDiffAt_iff_contDiffAt.mpr
      ((c.smooth_normalizedCoframe.mono hU).contDiffAt (U.isOpen.mem_nhds z.property)))
  let W : Set ((Model (2 * n) →L[ℝ] TangentCoordinates n) × SquaredCanonicalTensor n) :=
    {p | p.1.IsInvertible}
  have hW : IsOpen W := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage continuous_fst
  have hq : ContDiffOn ℝ ∞ (fun p => squaredCoframeCoefficient p.1 p.2) W :=
    contDiffOn_squaredCoframeCoefficient contDiffOn_fst (fun _ hp => hp) contDiffOn_snd
  intro z hz
  have hs := (hq.contDiffAt (hW.mem_nhds
    (c.invertible_normalizedCoframe (hU hz)))).comp_contMDiffAt
      ((hC ⟨z, hz⟩).prodMk_space (hT ⟨z, hz⟩))
  have he : (fun w : U => c.graphCoefficient U G w.val) =
      (fun w : U => squaredCoframeCoefficient (C w)
        (canonicalSquareMap (c.complex (G w).proj) (G w).snd).val) :=
    funext (fun w => c.graphCoefficient_apply U G w.property)
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞
    (fun w : U => squaredCoframeCoefficient (C w)
      (canonicalSquareMap (c.complex (G w).proj) (G w).snd).val) ⟨z, hz⟩ at hs
  rw [← he] at hs
  exact ((contMDiffAt_subtype_iff.mp hs).contDiffAt).contDiffWithinAt

/-- Smoothness of a bundle map follows from its base map and natural tensor
image. The source may be an independent manifold, including an interval base. -/
theorem smooth_bundleMap_of_base_tensor
    {D HD X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace HD] [TopologicalSpace X] [ChartedSpace HD X]
    (IX : ModelWithCorners ℝ D HD)
    (G : X → Bundle.TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (hb : ContMDiff IX 𝓘(ℝ, E) ∞ (fun x => (G x).proj))
    (hT : ContMDiff IX 𝓘(ℝ, SquaredCanonicalTensor n) ∞
      (fun x => (canonicalSquareMap (c.complex (G x).proj) (G x).snd).val)) :
    let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff IX ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞ G := by
  let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  dsimp only
  intro x
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb x, ?_⟩
  let d := verticalCanonicalChartAt c.smooth_complex c.complex_sq (G x).proj
  have hx : (G x).proj ∈ d.domain := mem_verticalCanonicalChartAt_domain _ _ _
  have hC := (d.smooth_coframe.contMDiffAt (d.isOpen_domain.mem_nhds hx)).comp x (hb x)
  let W : Set ((Model (2 * n) →L[ℝ] TangentCoordinates n) × SquaredCanonicalTensor n) :=
    {p | p.1.IsInvertible}
  have hW : IsOpen W := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage continuous_fst
  have hq : ContDiffOn ℝ ∞ (fun p => squaredCoframeCoefficient p.1 p.2) W :=
    contDiffOn_squaredCoframeCoefficient contDiffOn_fst (fun _ hp => hp) contDiffOn_snd
  have hs := (hq.contDiffAt (hW.mem_nhds (d.invertible_coframe _ hx))).comp_contMDiffAt
    (hC.prodMk_space (hT x))
  change ContMDiffAt IX 𝓘(ℝ, ℂ) ∞
    (fun z => squaredCoframeCoefficient (d.coframe (G z).proj)
      (canonicalSquareMap (c.complex (G z).proj) (G z).snd).val) x at hs
  simp_rw [d.coefficient_squareMap] at hs
  exact hs

/-- A scalar reconstructs an actual fiber of the independently extending bundle. -/
def graphOfScalar {X : Type*} (f : X → c.domain) (q : X → ℂ) (x : X) :
    Bundle.TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)) :=
  ⟨f x, (c.openCoframeChart.tensorCoordinateEquiv (f x) (mem_univ _)).symm (q x)⟩

theorem smooth_graphOfScalar
    {D HD X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace HD] [TopologicalSpace X] [ChartedSpace HD X]
    (IX : ModelWithCorners ℝ D HD) (f : X → c.domain) (q : X → ℂ)
    (hf : ContMDiff IX 𝓘(ℝ, E) ∞ f) (hq : ContMDiff IX 𝓘(ℝ, ℂ) ∞ q) :
    let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff IX ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞ (c.graphOfScalar f q) := by
  apply c.smooth_bundleMap_of_base_tensor IX _ hf
  have hg := (contMDiffOn_univ.mp c.openCoframeChart.smooth_squaredGenerator).comp hf
  have hm : ContDiff ℝ ∞ (fun p : ℂ × SquaredCanonicalTensor n => p.1 • p.2) :=
    contDiff_fst.smul contDiff_snd
  have hs := hm.contMDiff.comp (hq.prodMk_space hg)
  apply hs.congr
  intro x
  have hr := c.openCoframeChart.reconstruction (mem_univ _)
    (canonicalSquareMap _ (c.graphOfScalar f q x).snd)
  rw [c.openCoframeChart.coefficient_squareMap] at hr
  change _ = c.openCoframeChart.tensorCoordinateEquiv (f x) (mem_univ _)
    ((c.openCoframeChart.tensorCoordinateEquiv (f x) (mem_univ _)).symm (q x)) • _ at hr
  rw [LinearEquiv.apply_symm_apply] at hr
  exact hr

end FsFltz.Geometry.NativeCoordinateCanonicalPatch

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} {hδ : 0 < δ}
  {C : Parameter → ℝ × IntrinsicBoundary.Point k M → M}
  {hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)}
  {hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0}
  {hzero : ∀ t b, C t (0, b) = b.val}
  {J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1)}
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

namespace OriginalInteriorCanonicalChart

variable (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- This bundle extension is fixed by the original coframe, before any section. -/
def nativeOpenPatch : NativeCoordinateCanonicalPatch N (c.correctedField N)
    (parameterInterval ×ˢ (univ : Set (Model (k + 1)))) where
  domain := c.domain
  coframe := c.coframe
  smooth_coframe := c.smooth_coframe
  invertible_coframe := c.invertible_coframe
  intertwines := by
    intro z hz v
    have h := coframeComplexStructure_intertwines ((c.coframe z).comp N.toContinuousLinearMap)
      ((c.invertible_coframe z hz.1).comp ⟨N, rfl⟩) (N.symm v)
    simpa only [correctedField, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The original fiber enters its independently extending bundle through the
two original line coordinates and the extending coframe's inverse coordinate. -/
def openFiberInclusion (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain) :
    CanonicalTensorSquare (originalInteriorComplex C J N p) →ₗ[ℂ]
      CanonicalTensorSquare ((c.nativeOpenPatch N).complex
        ⟨(p.1.val, chartAt (Model (k + 1)) c.anchor p.2), hp.2⟩) :=
  (((c.nativeOpenPatch N).openCoframeChart.tensorCoordinateEquiv _ (mem_univ _)).symm.toLinearMap).comp
    (c.tensorCoordinateLinearMap (P := N) p)

theorem openFiberInclusion_coefficient (p : Parameter × IntrinsicInterior.Point k M)
    (hp : p ∈ c.baseDomain) (τ : CanonicalTensorSquare (originalInteriorComplex C J N p)) :
    squaredCoframeCoefficient ((c.coframe (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)).comp
      N.toContinuousLinearMap)
      (canonicalSquareMap _ (c.openFiberInclusion N p hp τ)).val =
      c.tensorCoordinateLinearMap (P := N) p τ := by
  change squaredCoframeCoefficient ((c.nativeOpenPatch N).openCoframeChart.coframe
    ⟨(p.1.val, chartAt (Model (k + 1)) c.anchor p.2), hp.2⟩)
    (canonicalSquareMap _ (c.openFiberInclusion N p hp τ)).val = _
  rw [((c.nativeOpenPatch N).openCoframeChart).coefficient_squareMap]
  exact ((c.nativeOpenPatch N).openCoframeChart.tensorCoordinateEquiv _ (mem_univ _)).apply_symm_apply _

include hC hinv in
/-- Every full tensor slot recovers the actual original spatial differential. -/
theorem canonicalSquareMap_openFiberInclusion
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain) :
    (canonicalSquareMap _ (c.openFiberInclusion N p hp (originalInteriorSection C J N σ p))).val =
      ((originalNativeSectionTensor C J N σ p.1
        (interiorIn (fun z : Half δ (IntrinsicBoundary.Point k M) => C p.1 z.val) p.2)).compContinuousLinearMap
        (fun _ => (originalInteriorCanonicalDifferential hδ (C p.1) (hemb p.1)
          (hboundary p.1) (hzero p.1) c.anchor p.2).inverse)).compContinuousLinearMap
        (fun _ => N.toContinuousLinearMap) := by
  have hr := (c.nativeOpenPatch N).openCoframeChart.reconstruction (mem_univ _)
    (canonicalSquareMap _ (c.openFiberInclusion N p hp (originalInteriorSection C J N σ p)))
  change (canonicalSquareMap _ (c.openFiberInclusion N p hp (originalInteriorSection C J N σ p))).val =
    squaredCoframeCoefficient ((c.coframe (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)).comp
      N.toContinuousLinearMap)
      (canonicalSquareMap _ (c.openFiberInclusion N p hp (originalInteriorSection C J N σ p))).val •
      coframeSquaredGenerator ((c.coframe (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)).comp
        N.toContinuousLinearMap) at hr
  rw [c.openFiberInclusion_coefficient N p hp] at hr
  exact hr.trans (c.coordinate_reconstruction N hC hinv σ p.1 p.2 hp _ rfl)

/-- The original section graph in the independently extending native bundle. -/
def openGraphValue (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain) :
    Bundle.TotalSpace ℂ (fun z : (c.nativeOpenPatch N).domain =>
      CanonicalTensorSquare ((c.nativeOpenPatch N).complex z)) :=
  ⟨⟨(p.1.val, chartAt (Model (k + 1)) c.anchor p.2), hp.2⟩,
    c.openFiberInclusion N p hp (originalInteriorSection C J N σ p)⟩

/-- Native original section smoothness gives a smooth map of its graph into
the extending bundle on the retained parameter locus. -/
theorem smooth_openGraphValue
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ) :
    let U : TopologicalSpace.Opens (Parameter × IntrinsicInterior.Point k M) :=
      ⟨c.baseDomain, c.isOpen_baseDomain⟩
    let b := c.nativeOpenPatch N
    let a := verticalCanonicalTensorSquareVectorPrebundle b.smooth_complex b.complex_sq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ × Model (k + 1))).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : U => c.openGraphValue N σ p.val p.property) := by
  let U : TopologicalSpace.Opens (Parameter × IntrinsicInterior.Point k M) :=
    ⟨c.baseDomain, c.isOpen_baseDomain⟩
  let b := c.nativeOpenPatch N
  let f : U → b.domain := fun p =>
    ⟨(p.val.1.val, chartAt (Model (k + 1)) c.anchor p.val.2), p.property.2⟩
  let q : U → ℂ := fun p => c.tensorCoordinateLinearMap (P := N) p.val
    (originalInteriorSection C J N σ p.val)
  have hf : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff b.domain f).mp
    intro p
    have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : Parameter × IntrinsicInterior.Point k M => p.1.val) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_fst
    have hx : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
        (chartAt (Model (k + 1)) c.anchor) p.val.2 :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor)).contMDiffAt
      ((chartAt (Model (k + 1)) c.anchor).open_source.mem_nhds p.property.1.2)
    exact contMDiffAt_subtype_iff.mpr
      ((ht p.val).prodMk_space (hx.comp p.val contMDiffAt_snd))
  have hq : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞ q := by
    intro p
    exact contMDiffAt_subtype_iff.mpr
      ((c.smooth_sectionCoefficient hJ hJsq σ hσ).contMDiffAt
        (c.isOpen_baseDomain.mem_nhds p.property))
  exact b.smooth_graphOfScalar (familyModel (k + 1)) f q hf hq

/-- The source's local extension convention expressed in a native extending
bundle. Neither a scalar germ nor a tensor matching formula is supplied. -/
def HasNativeOpenGraphExtension (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M) : Prop :=
  ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1)))
    (hU : (U : Set (ℝ × Model (k + 1))) ⊆ c.domain),
    (p.1.val, chartAt (Model (k + 1)) c.anchor p.2) ∈ U ∧
    ∃ G : U → Bundle.TotalSpace ℂ (fun z : (c.nativeOpenPatch N).domain =>
      CanonicalTensorSquare ((c.nativeOpenPatch N).complex z)),
      (let b := c.nativeOpenPatch N
       let a := verticalCanonicalTensorSquareVectorPrebundle b.smooth_complex b.complex_sq
       letI := a.totalSpaceTopology
       letI := a.toFiberBundle
       ContMDiff 𝓘(ℝ, ℝ × Model (k + 1))
         ((𝓘(ℝ, ℝ × Model (k + 1))).prod 𝓘(ℝ, ℂ)) ∞ G) ∧
      ∀ (s : Parameter) (w : IntrinsicInterior.Point k M)
        (hw : w ∈ (chartAt (Model (k + 1)) c.anchor).source)
        (hz : (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ U),
        G ⟨_, hz⟩ = c.openGraphValue N σ (s, w) ⟨⟨mem_univ _, hw⟩, hU hz⟩

/-- The native graph extension supplies the existing original scalar-germ
consumer, with agreement proved through the constructed fiber inclusion. -/
theorem sectionCoefficientExtension_of_nativeOpenGraph
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × IntrinsicInterior.Point k M)
    (hσ : c.HasNativeOpenGraphExtension N σ p) :
    c.HasSectionCoefficientExtension (P := N) σ p := by
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hσ
  refine ⟨U, (c.nativeOpenPatch N).graphCoefficient U G, hpU, hU,
    (c.nativeOpenPatch N).smooth_graphCoefficient U hU G hG, ?_⟩
  intro s w hw hz
  rw [(c.nativeOpenPatch N).graphCoefficient_apply U G hz, heG s w hw hz]
  exact c.openFiberInclusion_coefficient N (s, w) ⟨⟨mem_univ _, hw⟩, hU hz⟩ _

end OriginalInteriorCanonicalChart
namespace OriginalEndCanonicalChart

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- This bundle extension is fixed by the original coframe, before any section. -/
def nativeOpenPatch : NativeCoordinateCanonicalPatch P (c.correctedField P)
    (parameterInterval ×ˢ (univ : Set ((Model k × ℝ)))) where
  domain := c.domain
  coframe := c.coframe
  smooth_coframe := c.smooth_coframe
  invertible_coframe := c.invertible_coframe
  intertwines := by
    intro z hz v
    have h := coframeComplexStructure_intertwines ((c.coframe z).comp P.toContinuousLinearMap)
      ((c.invertible_coframe z hz.1).comp ⟨P, rfl⟩) (P.symm v)
    simpa only [correctedField, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

/-- The original fiber enters its independently extending bundle through the
two original line coordinates and the extending coframe's inverse coordinate. -/
def openFiberInclusion (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain) :
    CanonicalTensorSquare (originalEndComplex C J N p) →ₗ[ℂ]
      CanonicalTensorSquare ((c.nativeOpenPatch P).complex
        ⟨(p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2)), hp.2⟩) :=
  (((c.nativeOpenPatch P).openCoframeChart.tensorCoordinateEquiv _ (mem_univ _)).symm.toLinearMap).comp
    (c.tensorCoordinateLinearMap (N := N) p)

theorem openFiberInclusion_coefficient (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hp : p ∈ c.baseDomain) (τ : CanonicalTensorSquare (originalEndComplex C J N p)) :
    squaredCoframeCoefficient ((c.coframe (p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2))).comp
      P.toContinuousLinearMap)
      (canonicalSquareMap _ (c.openFiberInclusion N P p hp τ)).val =
      c.tensorCoordinateLinearMap (N := N) p τ := by
  change squaredCoframeCoefficient ((c.nativeOpenPatch P).openCoframeChart.coframe
    ⟨(p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2)), hp.2⟩)
    (canonicalSquareMap _ (c.openFiberInclusion N P p hp τ)).val = _
  rw [((c.nativeOpenPatch P).openCoframeChart).coefficient_squareMap]
  exact ((c.nativeOpenPatch P).openCoframeChart.tensorCoordinateEquiv _ (mem_univ _)).apply_symm_apply _

include hC hinv in
/-- Every full tensor slot recovers the actual original spatial differential. -/
theorem canonicalSquareMap_openFiberInclusion
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain) :
    (canonicalSquareMap _ (c.openFiberInclusion N P p hp (originalEndSection C J N σ p))).val =
      ((originalNativeSectionTensor C J N σ p.1
        (cylinder (fun z : Half δ (IntrinsicBoundary.Point k M) => C p.1 z.val) p.2)).compContinuousLinearMap
        (fun _ => (originalEndCanonicalDifferential hδ (C p.1) (hemb p.1)
          (hboundary p.1) (hzero p.1) c.anchor p.2).inverse)).compContinuousLinearMap
        (fun _ => P.toContinuousLinearMap) := by
  have hr := (c.nativeOpenPatch P).openCoframeChart.reconstruction (mem_univ _)
    (canonicalSquareMap _ (c.openFiberInclusion N P p hp (originalEndSection C J N σ p)))
  change (canonicalSquareMap _ (c.openFiberInclusion N P p hp (originalEndSection C J N σ p))).val =
    squaredCoframeCoefficient ((c.coframe (p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2))).comp
      P.toContinuousLinearMap)
      (canonicalSquareMap _ (c.openFiberInclusion N P p hp (originalEndSection C J N σ p))).val •
      coframeSquaredGenerator ((c.coframe (p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2))).comp
        P.toContinuousLinearMap) at hr
  rw [c.openFiberInclusion_coefficient N P p hp] at hr
  exact hr.trans (c.coordinate_reconstruction N P hC hinv σ p.1 p.2 hp _ rfl)

/-- The original section graph in the independently extending native bundle. -/
def openGraphValue (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain) :
    Bundle.TotalSpace ℂ (fun z : (c.nativeOpenPatch P).domain =>
      CanonicalTensorSquare ((c.nativeOpenPatch P).complex z)) :=
  ⟨⟨(p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2)), hp.2⟩,
    c.openFiberInclusion N P p hp (originalEndSection C J N σ p)⟩

/-- Native original section smoothness gives a smooth graph map on the
retained full signed cylinder, including its seam. -/
theorem smooth_openGraphValue
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ) :
    let U : TopologicalSpace.Opens (Parameter × Band δ (IntrinsicBoundary.Point k M)) :=
      ⟨c.baseDomain, c.isOpen_baseDomain⟩
    let b := c.nativeOpenPatch P
    let a := verticalCanonicalTensorSquareVectorPrebundle b.smooth_complex b.complex_sq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ × (Model k × ℝ))).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : U => c.openGraphValue N P σ p.val p.property) := by
  let U : TopologicalSpace.Opens (Parameter × Band δ (IntrinsicBoundary.Point k M)) :=
    ⟨c.baseDomain, c.isOpen_baseDomain⟩
  let b := c.nativeOpenPatch P
  let f : U → b.domain := fun p =>
    ⟨(p.val.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.val.2)), p.property.2⟩
  let q : U → ℂ := fun p => c.tensorCoordinateLinearMap (N := N) p.val
    (originalEndSection C J N σ p.val)
  have hf : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff b.domain f).mp
    intro p
    have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => p.1.val) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_fst
    have hx : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) ∞
        (chartAt (Model k × ℝ) c.anchor) (endBandCoordinates p.val.2) :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := c.anchor)).contMDiffAt
        ((chartAt (Model k × ℝ) c.anchor).open_source.mem_nhds p.property.1.2)
    have he : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
        (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => endBandCoordinates p.2)
        p.val := (contMDiff_endBandCoordinates.comp contMDiff_snd) p.val
    exact contMDiffAt_subtype_iff.mpr ((ht p.val).prodMk_space (hx.comp p.val he))
  have hq : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞ q := by
    intro p
    exact contMDiffAt_subtype_iff.mpr
      ((c.smooth_sectionCoefficient hJ hJsq σ hσ).contMDiffAt
        (c.isOpen_baseDomain.mem_nhds p.property))
  exact b.smooth_graphOfScalar (familyModel (k + 1)) f q hf hq

/-- The source's local extension convention expressed in a native extending
bundle. Neither a scalar germ nor a tensor matching formula is supplied. -/
def HasNativeOpenGraphExtension (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) : Prop :=
  ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)))
    (hU : (U : Set (ℝ × (Model k × ℝ))) ⊆ c.domain),
    (p.1.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates p.2)) ∈ U ∧
    ∃ G : U → Bundle.TotalSpace ℂ (fun z : (c.nativeOpenPatch P).domain =>
      CanonicalTensorSquare ((c.nativeOpenPatch P).complex z)),
      (let b := c.nativeOpenPatch P
       let a := verticalCanonicalTensorSquareVectorPrebundle b.smooth_complex b.complex_sq
       letI := a.totalSpaceTopology
       letI := a.toFiberBundle
       ContMDiff 𝓘(ℝ, ℝ × (Model k × ℝ))
         ((𝓘(ℝ, ℝ × (Model k × ℝ))).prod 𝓘(ℝ, ℂ)) ∞ G) ∧
      ∀ (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M))
        (hw : endBandCoordinates w ∈ (chartAt ((Model k × ℝ)) c.anchor).source)
        (hz : (s.val, chartAt ((Model k × ℝ)) c.anchor (endBandCoordinates w)) ∈ U),
        G ⟨_, hz⟩ = c.openGraphValue N P σ (s, w) ⟨⟨mem_univ _, hw⟩, hU hz⟩

/-- The native graph extension supplies the existing original scalar-germ
consumer, with agreement proved through the constructed fiber inclusion. -/
theorem sectionCoefficientExtension_of_nativeOpenGraph
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hσ : c.HasNativeOpenGraphExtension N P σ p) :
    c.HasSectionCoefficientExtension (N := N) σ p := by
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hσ
  refine ⟨U, (c.nativeOpenPatch P).graphCoefficient U G, hpU, hU,
    (c.nativeOpenPatch P).smooth_graphCoefficient U hU G hG, ?_⟩
  intro s w hw hz
  rw [(c.nativeOpenPatch P).graphCoefficient_apply U G hz, heG s w hw hz]
  exact c.openFiberInclusion_coefficient N P (s, w) ⟨⟨mem_univ _, hw⟩, hU hz⟩ _

end OriginalEndCanonicalChart

/-- Native original interior smoothness and native graph extensions only at
the two time endpoints supply every original coefficient-extension consumer. -/
theorem originalInteriorSectionExtensions_of_nativeSmooth_and_endpointGraphs
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ)
    (hend : ∀ (p : Parameter × IntrinsicInterior.Point k M),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N σ p) :
    HasOriginalInteriorSectionExtensions hδ C hemb hboundary hzero J N σ := by
  apply originalInteriorSectionExtensions_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ hσ
  intro d p hpd ht
  obtain ⟨c, hpc, hc⟩ := hend p ht
  exact OriginalInteriorCanonicalChart.HasSectionCoefficientExtension.changeChart
    N hC hinv c (c.sectionCoefficientExtension_of_nativeOpenGraph N σ p hc) hpc d hpd

/-- The corresponding producer retains the entire original signed cylinder. -/
theorem originalEndSectionExtensions_of_nativeSmooth_and_endpointGraphs
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ)
    (hend : ∀ (p : Parameter × Band δ (IntrinsicBoundary.Point k M)),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N P σ p) :
    HasOriginalEndSectionExtensions hδ C hemb hboundary hzero J N σ := by
  apply originalEndSectionExtensions_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ hσ
  intro d p hpd ht
  obtain ⟨c, hpc, hc⟩ := hend p ht
  exact OriginalEndCanonicalChart.HasSectionCoefficientExtension.changeChart
    N P hC hinv c (c.sectionCoefficientExtension_of_nativeOpenGraph N P σ p hc) hpc d hpd

/-- The graph-derived endpoint coefficients reach the existing grading
consumer, with the full tensor of the same original section. -/
theorem originalNativeInteriorGradingSectionGerms_of_nativeSmooth_and_endpointGraphs
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ)
    (hend : ∀ (p : Parameter × IntrinsicInterior.Point k M),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N σ p)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) N := by
  apply originalNativeInteriorGradingSectionGerms_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ hσ _ hnσ
  intro d p hpd ht
  obtain ⟨c, hpc, hc⟩ := hend p ht
  exact OriginalInteriorCanonicalChart.HasSectionCoefficientExtension.changeChart
    N hC hinv c (c.sectionCoefficientExtension_of_nativeOpenGraph N σ p hc) hpc d hpd

/-- Native graph extensions at time zero and one reach the existing
full signed-cylinder grading consumer for the same original section. -/
theorem originalNativeEndGradingSectionGerms_of_nativeSmooth_and_endpointGraphs
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ)
    (hend : ∀ (p : Parameter × Band δ (IntrinsicBoundary.Point k M)),
      p.1.val = 0 ∨ p.1.val = 1 →
      ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
        p ∈ c.baseDomain ∧ c.HasNativeOpenGraphExtension N P σ p)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  apply originalNativeEndGradingSectionGerms_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ hσ _ hnσ
  intro d p hpd ht
  obtain ⟨c, hpc, hc⟩ := hend p ht
  exact OriginalEndCanonicalChart.HasSectionCoefficientExtension.changeChart
    N P hC hinv c (c.sectionCoefficientExtension_of_nativeOpenGraph N P σ p hc) hpc d hpd

end FsFltz.Geometry.IntrinsicCompletionGluing
