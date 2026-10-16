import FsFltz.Geometry.CompatibleComplexExtension
import FsFltz.Geometry.IntrinsicVerticalCanonicalBundle
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Native canonical tensor squares on the prescribed parameter interval

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 794–814.

The base is the actual smooth manifold with boundary `[0,1] × M`. Local
projected coframes are invertible on open neighborhoods of interval points
and intertwine the original complex structure on the interval. Their tensor
coordinates construct the native squared canonical bundle. Smoothness of
overlap maps comes from genuine open coframe extensions and the spatial chart
differentials. No global extension of the complex structure is supplied.

The original Maslov family supplies a smooth nowhere-zero section in this
bundle, with every interval value recovered by natural tensor multiplication.
Only this forward bridge is asserted; a converse producing one open C∞
extension from arbitrary boundary-manifold smooth data is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

def intervalParameterInclusion {d : ℕ} (M : SmoothManifold d) :
    Parameter × M.Point → ℝ × M.Point := fun p => (p.1.val, p.2)

theorem contMDiff_intervalParameterInclusion {d : ℕ} (M : SmoothManifold d) :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞ (intervalParameterInclusion M) :=
  contMDiff_subtypeVal_Icc.prodMap contMDiff_id

/-- A coframe with an open smooth extension, canonical only where the
prescribed family is complex: on the closed parameter interval. -/
structure IntervalCanonicalChart {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M) where
  domain : Set (ℝ × M.Point)
  isOpen_domain : IsOpen domain
  coframe : (ℝ × M.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n
  smooth_coframe : IsSmoothVerticalCoframeOn M coframe domain
  invertible_coframe : ∀ p ∈ domain, (coframe p).IsInvertible
  intertwines_coframe : ∀ p ∈ domain, p.1 ∈ parameterInterval → ∀ v,
    coframe p (J p.1 p.2 v) = coordinateComplexStructure n (coframe p v)

namespace MaslovFamily

/-- The local endpoint coframe producer covers the actual interval base.
No complex field on a larger parameter interval is assumed. -/
theorem exists_intervalCanonicalChart {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : ℝ → M.Form 2} (f : MaslovFamily M eta) (p : Parameter × M.Point) :
    ∃ c : IntervalCanonicalChart M f.J, intervalParameterInclusion M p ∈ c.domain := by
  let a := p.2
  let e := chartAt (Model (2 * n)) a
  have hp : (p.1.val, e a) ∈ parameterInterval ×ˢ e.target :=
    ⟨p.1.property, e.map_source (mem_chart_source _ a)⟩
  obtain ⟨C₀, V, hVsub, hVo, hpV, hC, hinv, hCJ⟩ :=
    f.exists_local_prescribedComplexCoframe a hp
  let C := fun q : ℝ × Model (2 * n) =>
    projectedComplexCoframe C₀ (almostComplexInChart M a (f.J q.1) q.2)
  refine ⟨⟨intrinsicParameterChartDomain M a V,
    isOpen_intrinsicParameterChartDomain M a hVo, localVerticalCoframe M a C,
    isSmoothVerticalCoframeOn_local M a hC, ?_, ?_⟩, ?_⟩
  · intro q hq
    exact (hinv _ hq.2).comp (chartTangentMap_isInvertible M a q.2 hq.1.2)
  · intro q hq ht v
    exact localCanonicalCoframe_intertwines M a (f.J q.1) (fun y => C (q.1, y))
      q.2 hq.1.2 (hCJ _ ⟨hq.2, ⟨ht, e.map_source hq.1.2⟩⟩) v
  · exact ⟨⟨mem_univ _, mem_chart_source _ a⟩, hpV⟩

def intervalCanonicalChartAt {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : ℝ → M.Form 2} (f : MaslovFamily M eta) (p : Parameter × M.Point) :=
  (f.exists_intervalCanonicalChart p).choose

theorem mem_intervalCanonicalChartAt_domain {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : ℝ → M.Form 2} (f : MaslovFamily M eta) (p : Parameter × M.Point) :
    intervalParameterInclusion M p ∈ (f.intervalCanonicalChartAt p).domain :=
  (f.exists_intervalCanonicalChart p).choose_spec

end MaslovFamily

namespace IntervalCanonicalChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
variable (c : IntervalCanonicalChart M J)

def intervalDomain : Set (Parameter × M.Point) := intervalParameterInclusion M ⁻¹' c.domain

theorem isOpen_intervalDomain : IsOpen c.intervalDomain :=
  c.isOpen_domain.preimage (contMDiff_intervalParameterInclusion M).continuous

def lineCoordinateLinearMap (x : Parameter × M.Point) : canonicalSubmodule (J x.1.val x.2) →ₗ[ℂ] ℂ where
  toFun s := canonicalCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : Parameter × M.Point) (hx : x ∈ c.intervalDomain) :
    canonicalSubmodule (J x.1.val x.2) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap x
  invFun q := q • (⟨coframeCanonicalGenerator (c.coframe (intervalParameterInclusion M x)),
    coframeCanonicalGenerator_canonical _ (c.invertible_coframe _ hx) _
      (c.intertwines_coframe _ hx x.1.property)⟩ : canonicalSubmodule (J x.1.val x.2))
  left_inv s := Subtype.ext (canonicalCoframe_reconstruction _
    (c.invertible_coframe _ hx) _ (c.intertwines_coframe _ hx x.1.property) _ s.property).symm
  right_inv q := by
    change q * canonicalCoframeCoefficient (c.coframe (intervalParameterInclusion M x))
      (coframeCanonicalGenerator (c.coframe (intervalParameterInclusion M x))) = q
    rw [coframeCanonicalGenerator_frame _ (c.invertible_coframe _ hx), mul_one]

/-- The coordinate is the tensor product of two unsquared line
coordinates, independently of natural square multiplication. -/
def tensorCoordinateLinearMap (x : Parameter × M.Point) : CanonicalTensorSquare (J x.1.val x.2) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap x) (c.lineCoordinateLinearMap x))

def tensorCoordinateEquiv (x : Parameter × M.Point) (hx : x ∈ c.intervalDomain) :
    CanonicalTensorSquare (J x.1.val x.2) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv x hx) (c.lineCoordinateEquiv x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : Parameter × M.Point) (hx : x ∈ c.intervalDomain) :
    (c.tensorCoordinateEquiv x hx).toLinearMap = c.tensorCoordinateLinearMap x := rfl

def tensorCoordinateContinuousEquiv (x : Parameter × M.Point) (hx : x ∈ c.intervalDomain) :
    CanonicalTensorSquare (J x.1.val x.2) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- The bridge is an equality of the independently constructed scalar
coordinates, proved on pure tensors and extended by tensor linearity. -/
theorem coefficient_squareMap (x : Parameter × M.Point) (t : CanonicalTensorSquare (J x.1.val x.2)) :
    squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) (canonicalSquareMap (J x.1.val x.2) t).val =
      c.tensorCoordinateLinearMap x t := by
  let L : squaredCanonicalSubmodule (J x.1.val x.2) →ₗ[ℂ] ℂ :=
    { toFun s := squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) s.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : L.comp (canonicalSquareMap (J x.1.val x.2)) = c.tensorCoordinateLinearMap x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M x))
      (canonicalSquareMap (J x.1.val x.2) (s ⊗ₜ[ℂ] u)).val =
      canonicalCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) s.val *
        canonicalCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) u.val
    rw [canonicalSquareMap_tmul]
    simp only [squaredCoframeCoefficient, canonicalTensorProduct_apply,
      canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun f => f t) h

open scoped Classical in
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : (Parameter × M.Point) => CanonicalTensorSquare (J x.1.val x.2))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.intervalDomain then
    ⟨p.1, (c.tensorCoordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : (Parameter × M.Point) => CanonicalTensorSquare (J x.1.val x.2))) ⁻¹' c.intervalDomain
  target := c.intervalDomain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.intervalDomain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : CanonicalTensorSquare (J x.1.val x.2) =>
      (⟨x, t⟩ : TotalSpace ℂ (fun x => CanonicalTensorSquare (J x.1.val x.2))))
      ((c.tensorCoordinateEquiv x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.tensorCoordinateEquiv p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_intervalDomain.prod isOpen_univ
  baseSet := c.intervalDomain
  open_baseSet := c.isOpen_intervalDomain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance tensorPretrivialization_complexLinear : c.tensorPretrivialization.IsLinear ℂ where
  linear x _ := (c.tensorCoordinateLinearMap x).isLinear

instance tensorPretrivialization_realLinear : c.tensorPretrivialization.IsLinear ℝ where
  linear x _ := ((c.tensorCoordinateLinearMap x).restrictScalars ℝ).isLinear

theorem tensorPretrivialization_symm {x : (Parameter × M.Point)} (hx : x ∈ c.intervalDomain) (q : ℂ) :
    c.tensorPretrivialization.symm x q = (c.tensorCoordinateEquiv x hx).symm q := by
  apply (c.tensorCoordinateEquiv x hx).injective
  rw [(c.tensorCoordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization.apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : (Parameter × M.Point)} (hx : x ∈ c.intervalDomain) :
    Topology.IsInducing (c.tensorPretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

def squaredGenerator (x : ℝ × M.Point) : SquaredCanonicalTensor n :=
  coframeSquaredGenerator (c.coframe x)

theorem smooth_squaredGenerator :
    IsSmoothVerticalSquaredTensorOn M c.squaredGenerator c.domain := by
  intro b
  apply (contDiffOn_coframeSquaredGenerator (c.smooth_coframe b)).congr
  intro p _
  ext v
  rfl

/-- Evaluation in inverse coframes gives a native smooth scalar function
on every open part of a coframe domain. -/
theorem smooth_coefficient {U : Set (ℝ × M.Point)} (hU : IsOpen U)
    (hUc : U ⊆ c.domain) (s : (ℝ × M.Point) → SquaredCanonicalTensor n)
    (hs : IsSmoothVerticalSquaredTensorOn M s U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
      (fun p => squaredCoframeCoefficient (c.coframe p) (s p)) U := by
  apply contMDiffOn_parameterCoordinates M hU
  intro b
  have hsub : intrinsicParameterCoordinateDomain M b U ⊆
      intrinsicParameterCoordinateDomain M b c.domain :=
    fun p hp => ⟨hp.1, hUc hp.2⟩
  have hinv : ∀ p ∈ intrinsicParameterCoordinateDomain M b U,
      ((c.coframe (p.1, (chartAt (Model (2 * n)) b).symm p.2)).comp
        (M.inverseChartTangentMap b p.2)).IsInvertible := by
    intro p hp
    exact (c.invertible_coframe _ (hUc hp.2)).comp
      (inverseChartTangentMap_isInvertible M b p.2 hp.1.2)
  apply (contDiffOn_squaredCoframeCoefficient
    ((c.smooth_coframe b).mono hsub) hinv (hs b)).congr
  intro p hp
  exact (squaredCoframeCoefficient_comp _ _
    (inverseChartTangentMap_isInvertible M b p.2 hp.1.2) _).symm

theorem reconstruction {x : Parameter × M.Point} (hx : x ∈ c.intervalDomain)
    (s : squaredCanonicalSubmodule (J x.1.val x.2)) :
    s.val = squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M x)) s.val •
      c.squaredGenerator (intervalParameterInclusion M x) :=
  squaredCoframe_reconstruction _ (c.invertible_coframe _ hx) _
    (c.intertwines_coframe _ hx x.1.property) _ s.property

def transitionExtension (d : IntervalCanonicalChart M J) (x : ℝ × M.Point) : ℂ :=
  squaredCoframeTransition (c.coframe x) (d.coframe x)

theorem smooth_transitionExtension (d : IntervalCanonicalChart M J) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
      (c.transitionExtension d) (c.domain ∩ d.domain) :=
  d.smooth_coefficient (c.isOpen_domain.inter d.isOpen_domain) inter_subset_right
    c.squaredGenerator (fun b => (c.smooth_squaredGenerator b).mono
      (fun _ hp => ⟨hp.1, hp.2.1⟩))

def transition (d : IntervalCanonicalChart M J) (x : Parameter × M.Point) : ℂ :=
  c.transitionExtension d (intervalParameterInclusion M x)

theorem smooth_transition (d : IntervalCanonicalChart M J) :
    ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
      (c.transition d) (c.intervalDomain ∩ d.intervalDomain) :=
  (c.smooth_transitionExtension d).comp (contMDiff_intervalParameterInclusion M).contMDiffOn
    (fun _ hx => hx)

theorem tensorTransition_apply (d : IntervalCanonicalChart M J) {x : (Parameter × M.Point)}
    (hx : x ∈ c.intervalDomain ∩ d.intervalDomain) (q : ℂ) :
    (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 =
      c.transition d x * q := by
  rw [c.tensorPretrivialization_symm hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap]
  have hr := c.reconstruction hx.1
    (canonicalSquareMap (J x.1.val x.2) ((c.tensorCoordinateEquiv x hx.1).symm q))
  have hq : squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M x))
      (canonicalSquareMap (J x.1.val x.2) ((c.tensorCoordinateEquiv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * squaredCoframeCoefficient (d.coframe (intervalParameterInclusion M x)) (c.squaredGenerator (intervalParameterInclusion M x)) = _
  exact mul_comm _ _

def transitionMap (d : IntervalCanonicalChart M J) (x : (Parameter × M.Point)) : ℂ →L[ℝ] ℂ :=
  c.transition d x • ContinuousLinearMap.id ℝ ℂ

theorem smooth_transitionMap (d : IntervalCanonicalChart M J) :
    ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap d) (c.intervalDomain ∩ d.intervalDomain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition d)

theorem transitionMap_apply (d : IntervalCanonicalChart M J) {x : (Parameter × M.Point)}
    (hx : x ∈ c.intervalDomain ∩ d.intervalDomain) (q : ℂ) :
    c.transitionMap d x q =
      (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 :=
  (c.tensorTransition_apply d hx q).symm

end IntervalCanonicalChart

/-- Native tensor-square bundle for a smooth vertical complex field.
The coframe cover is independent of any canonical section; the base includes
only the prescribed time interval and spatial points. -/
def intervalCanonicalTensorSquareVectorPrebundleOfCharts
    {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (charts : (p : Parameter × M.Point) → IntervalCanonicalChart M J)
    (hcharts : ∀ p, intervalParameterInclusion M p ∈ (charts p).domain) :
    VectorPrebundle ℝ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (J x.1.val x.2)) where
  pretrivializationAtlas := Set.range IntervalCanonicalChart.tensorPretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (charts a).tensorPretrivialization
  mem_base_pretrivializationAt := hcharts
  pretrivialization_mem_atlas a := ⟨charts a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, (c.smooth_transitionMap d).continuousOn,
      fun _ hx q => c.transitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (charts a).tensorPretrivialization_isInducing
      (hcharts a)

instance intervalCanonicalTensorSquareVectorPrebundleOfCharts_isContMDiff
    {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (charts : (p : Parameter × M.Point) → IntervalCanonicalChart M J)
    (hcharts : ∀ p, intervalParameterInclusion M p ∈ (charts p).domain) :
    (intervalCanonicalTensorSquareVectorPrebundleOfCharts charts hcharts).IsContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, c.smooth_transitionMap d,
      fun _ hx q => c.transitionMap_apply d hx q⟩

theorem intervalCanonicalTensorSquareVectorBundleOfCharts_smooth
    {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (charts : (p : Parameter × M.Point) → IntervalCanonicalChart M J)
    (hcharts : ∀ p, intervalParameterInclusion M p ∈ (charts p).domain) :
    let a := intervalCanonicalTensorSquareVectorPrebundleOfCharts charts hcharts
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (J x.1.val x.2)) ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) :=
  (intervalCanonicalTensorSquareVectorPrebundleOfCharts charts hcharts).contMDiffVectorBundle ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n)))

/-- The independently constructed atlas has complex-linear transitions,
so the native smooth real bundle is also a complex line bundle. -/
theorem intervalCanonicalTensorSquareVectorBundleOfCharts_complex
    {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (charts : (p : Parameter × M.Point) → IntervalCanonicalChart M J)
    (hcharts : ∀ p, intervalParameterInclusion M p ∈ (charts p).domain) :
    let a := intervalCanonicalTensorSquareVectorPrebundleOfCharts charts hcharts
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (J x.1.val x.2)) := by
  dsimp only
  let a := intervalCanonicalTensorSquareVectorPrebundleOfCharts charts hcharts
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    exact ⟨fun x _ => (c.tensorCoordinateLinearMap x).isLinear⟩
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨c, rfl⟩ := he
    obtain ⟨d, rfl⟩ := he'
    let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
      ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ ℂ)
    have hc : ContinuousOn (fun x => L (c.transition d x)) (c.intervalDomain ∩ d.intervalDomain) :=
      L.continuous.comp_continuousOn (c.smooth_transition d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (c.transitionMap_apply d hx q).symm
    · exact hx

theorem intervalCanonicalTensorSquareVectorBundleOfCharts_finrank
    {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
    (charts : (p : Parameter × M.Point) → IntervalCanonicalChart M J)
    (hcharts : ∀ p, intervalParameterInclusion M p ∈ (charts p).domain) (x : Parameter × M.Point) :
    Module.finrank ℂ (CanonicalTensorSquare (J x.1.val x.2)) = 1 := by
  let c := charts x
  rw [(c.tensorCoordinateEquiv x (hcharts x)).finrank_eq]
  exact Module.finrank_self ℂ

/-- The Maslov-family API uses the same section-independent atlas constructor. -/
def intervalCanonicalTensorSquareVectorPrebundle
    {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) :
    VectorPrebundle ℝ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (f.J x.1.val x.2)) :=
  intervalCanonicalTensorSquareVectorPrebundleOfCharts f.intervalCanonicalChartAt
    f.mem_intervalCanonicalChartAt_domain

instance intervalCanonicalTensorSquareVectorPrebundle_isContMDiff
    {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) :
    (intervalCanonicalTensorSquareVectorPrebundle f).IsContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) ∞ :=
  intervalCanonicalTensorSquareVectorPrebundleOfCharts_isContMDiff
    f.intervalCanonicalChartAt f.mem_intervalCanonicalChartAt_domain

theorem intervalCanonicalTensorSquareVectorBundle_smooth
    {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) :
    let a := intervalCanonicalTensorSquareVectorPrebundle f
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (f.J x.1.val x.2)) ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) :=
  (intervalCanonicalTensorSquareVectorPrebundle f).contMDiffVectorBundle ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n)))

/-- The independently constructed atlas has complex-linear transitions,
so the native smooth real bundle is also a complex line bundle. -/
theorem intervalCanonicalTensorSquareVectorBundle_complex
    {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) :
    let a := intervalCanonicalTensorSquareVectorPrebundle f
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : Parameter × M.Point => CanonicalTensorSquare (f.J x.1.val x.2)) :=
  intervalCanonicalTensorSquareVectorBundleOfCharts_complex
    f.intervalCanonicalChartAt f.mem_intervalCanonicalChartAt_domain

theorem intervalCanonicalTensorSquareVectorBundle_finrank
    {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}
    (f : MaslovFamily M eta) (x : Parameter × M.Point) :
    Module.finrank ℂ (CanonicalTensorSquare (f.J x.1.val x.2)) = 1 :=
  intervalCanonicalTensorSquareVectorBundleOfCharts_finrank
    f.intervalCanonicalChartAt f.mem_intervalCanonicalChartAt_domain x

namespace IntervalCanonicalChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}

/-- A genuinely smooth chartwise tensor extension gives native smooth
coframe coefficients at every interval point. -/
theorem contMDiffAt_coefficient (c : IntervalCanonicalChart M J)
    (s : ℝ → M.Point → SquaredCanonicalTensor n)
    (hs : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => squaredTensorInChart M a (s z.1) z.2))
    {x : Parameter × M.Point} (hx : x ∈ c.intervalDomain) :
    ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞
      (fun z => squaredCoframeCoefficient (c.coframe (intervalParameterInclusion M z))
        (s z.1.val z.2)) x := by
  let b := x.2
  let e := chartAt (Model (2 * n)) b
  let D := intrinsicParameterCoordinateDomain M b c.domain
  let C := fun p : ℝ × Model (2 * n) =>
    (c.coframe (p.1, e.symm p.2)).comp (M.inverseChartTangentMap b p.2)
  obtain ⟨S, hSo, hSsub, hsS⟩ := hs b
  let W := D ∩ S
  have hDo : IsOpen D := isOpen_intrinsicParameterCoordinateDomain M b c.isOpen_domain
  have hWo : IsOpen W := hDo.inter hSo
  have hinv : ∀ p ∈ W, (C p).IsInvertible := by
    intro p hp
    exact (c.invertible_coframe _ hp.1.2).comp
      (inverseChartTangentMap_isInvertible M b p.2 hp.1.1.2)
  have hscalar : ContDiffOn ℝ ∞
      (fun p : ℝ × Model (2 * n) =>
        squaredCoframeCoefficient (C p) (squaredTensorInChart M b (s p.1) p.2)) W :=
    contDiffOn_squaredCoframeCoefficient ((c.smooth_coframe b).mono inter_subset_left)
      hinv (hsS.mono inter_subset_right)
  have hxb : x.2 ∈ e.source := mem_chart_source _ x.2
  have hpx : (x.1.val, e x.2) ∈ W := by
    refine ⟨⟨⟨mem_univ _, e.map_source hxb⟩, ?_⟩,
      hSsub ⟨x.1.property, e.map_source hxb⟩⟩
    change (x.1.val, e.symm (e x.2)) ∈ c.domain
    rwa [e.left_inv hxb]
  have hchart : ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × Model (2 * n)) ∞
      (fun z : Parameter × M.Point => (z.1.val, e z.2)) x := by
    have ht : ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, ℝ) ∞ (fun z : Parameter × M.Point => z.1.val) x :=
      (contMDiff_subtypeVal_Icc (n := ∞)).contMDiffAt.comp x
        (contMDiffAt_fst (I := 𝓡∂ 1) (J := 𝓘(ℝ, Model (2 * n))))
    have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e x.2 :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
        (e.open_source.mem_nhds hxb)
    exact ht.prodMk_space (he.comp x contMDiffAt_snd)
  have hq := (contMDiffAt_iff_contDiffAt.mpr
    (hscalar.contDiffAt (hWo.mem_nhds hpx))).comp x hchart
  apply hq.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (e.open_source.mem_nhds hxb)] with z hz
  dsimp only [Function.comp_def, C, squaredTensorInChart]
  rw [e.left_inv hz]
  exact (squaredCoframeCoefficient_comp _ _
    (inverseChartTangentMap_isInvertible M b (e z.2) (e.map_source hz)) _).symm

end IntervalCanonicalChart

namespace MaslovFamily

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}

/-- The section uses the original complex structure and original tensor
at their original interval parameters. -/
def intervalTensorSection (f : MaslovFamily M eta) (p : Parameter × M.Point) :
    CanonicalTensorSquare (f.J p.1.val p.2) :=
  (canonicalSquareEquivOfComplexStructure _ ((f.compatible p.1.val p.1.property).2.1 p.2)).symm
    ⟨f.tensor p.1.val p.2, f.canonical p.1.val p.1.property p.2⟩

theorem canonicalSquareMap_intervalTensorSection (f : MaslovFamily M eta)
    (p : Parameter × M.Point) :
    canonicalSquareMap (f.J p.1.val p.2) (f.intervalTensorSection p) =
      ⟨f.tensor p.1.val p.2, f.canonical p.1.val p.1.property p.2⟩ :=
  (canonicalSquareEquivOfComplexStructure _
    ((f.compatible p.1.val p.1.property).2.1 p.2)).apply_symm_apply _

/-- The actual prescribed grading family is a native smooth section over
the full interval–spatial base, including both time boundary faces. -/
theorem contMDiff_intervalTensorSection (f : MaslovFamily M eta) :
    let a := intervalCanonicalTensorSquareVectorPrebundle f
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    let I := (𝓡∂ 1).prod 𝓘(ℝ, Model (2 * n))
    ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, f.intervalTensorSection p⟩ : TotalSpace ℂ
        (fun p : Parameter × M.Point => CanonicalTensorSquare (f.J p.1.val p.2)))) := by
  dsimp only
  let a := intervalCanonicalTensorSquareVectorPrebundle f
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  intro x
  rw [Bundle.contMDiffAt_section]
  let c := f.intervalCanonicalChartAt x
  have hx : x ∈ c.intervalDomain := f.mem_intervalCanonicalChartAt_domain x
  have hq := c.contMDiffAt_coefficient f.tensor f.smoothSection hx
  apply hq.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => by
    change c.tensorCoordinateLinearMap z (f.intervalTensorSection z) = _
    rw [← c.coefficient_squareMap, f.canonicalSquareMap_intervalTensorSection]

theorem intervalTensorSection_ne_zero (f : MaslovFamily M eta) (p : Parameter × M.Point) :
    f.intervalTensorSection p ≠ 0 := by
  intro hz
  have he := f.canonicalSquareMap_intervalTensorSection p
  rw [hz, map_zero] at he
  exact f.nowhereZero p.1.val p.1.property p.2 (congrArg Subtype.val he.symm)

end MaslovFamily

end FsFltz.Geometry
