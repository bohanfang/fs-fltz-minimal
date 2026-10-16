import FsFltz.Geometry.VerticalMaslovFamily

/-!
# Intrinsic vertical canonical squares on a parameter family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 794–814. The base is `ℝ × M`; the canonical fibers use
only the spatial tangent. Coframe coordinates are transported by actual
spatial chart derivatives, and their smooth overlap maps construct the
global native tensor-square bundle. Its topology is constructed from
unsquared coframe tensor coordinates, independently of square multiplication.

Whole-time complex structures supply this atlas. Extending the original
prescribed varying-form family without changing its parameter remains a
separate foundation; the geometric target is not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

def parameterSpatialCoordinates {d : ℕ} (M : SmoothManifold d) (a : M.Point) :
    OpenPartialHomeomorph (ℝ × M.Point) (ℝ × Model d) :=
  (OpenPartialHomeomorph.refl ℝ).prod (chartAt (Model d) a)

def intrinsicParameterChartDomain {d : ℕ} (M : SmoothManifold d) (a : M.Point)
    (V : Set (ℝ × Model d)) : Set (ℝ × M.Point) :=
  (parameterSpatialCoordinates M a).source ∩ parameterSpatialCoordinates M a ⁻¹' V

theorem isOpen_intrinsicParameterChartDomain {d : ℕ} (M : SmoothManifold d)
    (a : M.Point) {V : Set (ℝ × Model d)} (hV : IsOpen V) :
    IsOpen (intrinsicParameterChartDomain M a V) :=
  (parameterSpatialCoordinates M a).continuousOn.isOpen_inter_preimage
    (parameterSpatialCoordinates M a).open_source hV

def intrinsicParameterCoordinateDomain {d : ℕ} (M : SmoothManifold d)
    (b : M.Point) (U : Set (ℝ × M.Point)) : Set (ℝ × Model d) :=
  (parameterSpatialCoordinates M b).target ∩
    (parameterSpatialCoordinates M b).symm ⁻¹' U

theorem isOpen_intrinsicParameterCoordinateDomain {d : ℕ} (M : SmoothManifold d)
    (b : M.Point) {U : Set (ℝ × M.Point)} (hU : IsOpen U) :
    IsOpen (intrinsicParameterCoordinateDomain M b U) :=
  (parameterSpatialCoordinates M b).continuousOn_symm.isOpen_inter_preimage
    (parameterSpatialCoordinates M b).open_target hU

def IsSmoothVerticalCoframeOn {n : ℕ} (M : SmoothManifold (2 * n))
    (C : (ℝ × M.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (U : Set (ℝ × M.Point)) : Prop :=
  ∀ b, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
    (C (p.1, (chartAt (Model (2 * n)) b).symm p.2)).comp
      (M.inverseChartTangentMap b p.2)) (intrinsicParameterCoordinateDomain M b U)

def IsSmoothVerticalSquaredTensorOn {n : ℕ} (M : SmoothManifold (2 * n))
    (s : (ℝ × M.Point) → SquaredCanonicalTensor n) (U : Set (ℝ × M.Point)) : Prop :=
  ∀ b, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
    squaredTensorInChart M b (fun x => s (p.1, x)) p.2)
      (intrinsicParameterCoordinateDomain M b U)

/-- Smooth coordinate expressions on every parameter–spatial chart give
native smoothness on an open part of the intrinsic parameter base. -/
theorem contMDiffOn_parameterCoordinates {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : SmoothManifold d) {U : Set (ℝ × M.Point)} (hU : IsOpen U)
    (q : (ℝ × M.Point) → F)
    (hq : ∀ b, ContDiffOn ℝ ∞ (q ∘ (parameterSpatialCoordinates M b).symm)
      (intrinsicParameterCoordinateDomain M b U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, F) ∞ q U := by
  intro x hx
  let c := parameterSpatialCoordinates M x.2
  have hc : x ∈ c.source := ⟨mem_univ _, mem_chart_source _ x.2⟩
  have hD := isOpen_intrinsicParameterCoordinateDomain M x.2 hU
  have hcx : c x ∈ intrinsicParameterCoordinateDomain M x.2 U :=
    ⟨c.map_source hc, by change c.symm (c x) ∈ U; rwa [c.left_inv hc]⟩
  have hs := (hq x.2).contDiffAt (hD.mem_nhds hcx)
  have hsM : ContMDiffAt 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, F) ∞ (q ∘ c.symm) (c x) :=
    contMDiffAt_iff_contDiffAt.mpr hs
  have hchart : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ c x := by
    have ht := (contMDiffAt_fst (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, Model d))
      (p := x) (n := ∞))
    have hxchart : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
        (chartAt (Model d) x.2) x.2 :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := x.2)).contMDiffAt
      ((chartAt (Model d) x.2).open_source.mem_nhds (mem_chart_source _ x.2))
    exact ht.prodMk_space (hxchart.comp x contMDiffAt_snd)
  apply ((hsM.comp x hchart).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [c.open_source.mem_nhds hc] with z hz
  exact (congrArg q (c.left_inv hz)).symm

def localVerticalCoframe {n : ℕ} (M : SmoothManifold (2 * n)) (a : M.Point)
    (C : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] TangentCoordinates n)
    (p : ℝ × M.Point) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (C (p.1, chartAt (Model (2 * n)) a p.2)).comp (M.chartTangentMap a p.2)

theorem isSmoothVerticalCoframeOn_local {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) {V : Set (ℝ × Model (2 * n))}
    {C : (ℝ × Model (2 * n)) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C V) :
    IsSmoothVerticalCoframeOn M (localVerticalCoframe M a C)
      (intrinsicParameterChartDomain M a V) := by
  intro b
  let c := chartAt (Model (2 * n)) a
  let d := chartAt (Model (2 * n)) b
  let O := d.target ∩ d.symm ⁻¹' c.source
  let D := intrinsicParameterCoordinateDomain M b (intrinsicParameterChartDomain M a V)
  let g := c ∘ d.symm
  have hO : IsOpen O :=
    d.continuousOn_symm.isOpen_inter_preimage d.open_target c.open_source
  have hg : ContDiffOn ℝ ∞ g O := by
    intro y hy
    have hA : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ d.symm y :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
      (d.open_target.mem_nhds hy.1)
    have hB : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c (d.symm y) :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).contMDiffAt
      (c.open_source.mem_nhds hy.2)
    exact (hB.comp y hA).contDiffAt.contDiffWithinAt
  have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ g) O := hg.fderiv_of_isOpen hO (by simp)
  have hsub : ∀ p ∈ D, p.2 ∈ O := fun p hp => ⟨hp.1.2, hp.2.1.2⟩
  have hderiv' := hderiv.comp contDiffOn_snd hsub
  have hparam : ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) => (p.1, g p.2)) D :=
    contDiffOn_fst.prodMk (hg.comp contDiffOn_snd hsub)
  have hc := hC.comp hparam (fun p hp => hp.2.2)
  apply (hc.clm_comp hderiv').congr
  intro p hp
  exact localCanonicalCoframe_inChart M a b (fun y => C (p.1, y)) p.2 hp.1.2 hp.2.1.2

/-- A coframe chart on the intrinsic parameter base. Smoothness is the
usual chartwise smoothness of the actual spatial tangent coframe. -/
structure IntrinsicVerticalCanonicalChart {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M) where
  domain : Set (ℝ × M.Point)
  isOpen_domain : IsOpen domain
  coframe : (ℝ × M.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n
  smooth_coframe : IsSmoothVerticalCoframeOn M coframe domain
  invertible_coframe : ∀ p ∈ domain, (coframe p).IsInvertible
  intertwines_coframe : ∀ p ∈ domain, ∀ v,
    coframe p (J p.1 p.2 v) = coordinateComplexStructure n (coframe p v)

theorem exists_intrinsicVerticalCanonicalChart {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) (p : ℝ × M.Point) :
    ∃ c : IntrinsicVerticalCanonicalChart M J, p ∈ c.domain := by
  let a := p.2
  let e := chartAt (Model (2 * n)) a
  have hp : (p.1, e a) ∈ univ ×ˢ e.target :=
    ⟨mem_univ _, e.map_source (mem_chart_source _ a)⟩
  obtain ⟨C₀, V, _, hV, hpV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_complexCoframe (isOpen_univ.prod e.open_target) hp (hJ a)
      (fun q hq => almostComplexInChart_sq M a (J q.1) (hJsq q.1) q.2 hq.2)
  let C := fun q : ℝ × Model (2 * n) =>
    projectedComplexCoframe C₀ (almostComplexInChart M a (J q.1) q.2)
  refine ⟨⟨intrinsicParameterChartDomain M a V,
    isOpen_intrinsicParameterChartDomain M a hV, localVerticalCoframe M a C,
    isSmoothVerticalCoframeOn_local M a hC, ?_, ?_⟩, ?_⟩
  · intro q hq
    exact (hinv _ hq.2).comp (chartTangentMap_isInvertible M a q.2 hq.1.2)
  · intro q hq v
    exact localCanonicalCoframe_intertwines M a (J q.1) (fun y => C (q.1, y))
      q.2 hq.1.2 (hCJ _ hq.2) v
  · exact ⟨⟨mem_univ _, mem_chart_source _ a⟩, hpV⟩

def intrinsicVerticalCanonicalChartAt {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) (p : ℝ × M.Point) :=
  (exists_intrinsicVerticalCanonicalChart M J hJ hJsq p).choose

theorem mem_intrinsicVerticalCanonicalChartAt_domain {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) (p : ℝ × M.Point) :
    p ∈ (intrinsicVerticalCanonicalChartAt M J hJ hJsq p).domain :=
  (exists_intrinsicVerticalCanonicalChart M J hJ hJsq p).choose_spec

namespace IntrinsicVerticalCanonicalChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : ℝ → AlmostComplexField M}
variable (c : IntrinsicVerticalCanonicalChart M J)

def lineCoordinateLinearMap (x : ℝ × M.Point) : canonicalSubmodule (J x.1 x.2) →ₗ[ℂ] ℂ where
  toFun s := canonicalCoframeCoefficient (c.coframe x) s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : ℝ × M.Point) (hx : x ∈ c.domain) :
    canonicalSubmodule (J x.1 x.2) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap x
  invFun q := q • (⟨coframeCanonicalGenerator (c.coframe x),
    coframeCanonicalGenerator_canonical _ (c.invertible_coframe x hx) _
      (c.intertwines_coframe x hx)⟩ : canonicalSubmodule (J x.1 x.2))
  left_inv s := Subtype.ext (canonicalCoframe_reconstruction _
    (c.invertible_coframe x hx) _ (c.intertwines_coframe x hx) _ s.property).symm
  right_inv q := by
    change q * canonicalCoframeCoefficient (c.coframe x)
      (coframeCanonicalGenerator (c.coframe x)) = q
    rw [coframeCanonicalGenerator_frame _ (c.invertible_coframe x hx), mul_one]

/-- The coordinate is the tensor product of two unsquared line
coordinates, independently of natural square multiplication. -/
def tensorCoordinateLinearMap (x : ℝ × M.Point) : CanonicalTensorSquare (J x.1 x.2) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap x) (c.lineCoordinateLinearMap x))

def tensorCoordinateEquiv (x : ℝ × M.Point) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x.1 x.2) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv x hx) (c.lineCoordinateEquiv x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : ℝ × M.Point) (hx : x ∈ c.domain) :
    (c.tensorCoordinateEquiv x hx).toLinearMap = c.tensorCoordinateLinearMap x := rfl

def tensorCoordinateContinuousEquiv (x : ℝ × M.Point) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x.1 x.2) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- The bridge is an equality of the independently constructed scalar
coordinates, proved on pure tensors and extended by tensor linearity. -/
theorem coefficient_squareMap (x : ℝ × M.Point) (t : CanonicalTensorSquare (J x.1 x.2)) :
    squaredCoframeCoefficient (c.coframe x) (canonicalSquareMap (J x.1 x.2) t).val =
      c.tensorCoordinateLinearMap x t := by
  let L : squaredCanonicalSubmodule (J x.1 x.2) →ₗ[ℂ] ℂ :=
    { toFun s := squaredCoframeCoefficient (c.coframe x) s.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : L.comp (canonicalSquareMap (J x.1 x.2)) = c.tensorCoordinateLinearMap x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change squaredCoframeCoefficient (c.coframe x)
      (canonicalSquareMap (J x.1 x.2) (s ⊗ₜ[ℂ] u)).val =
      canonicalCoframeCoefficient (c.coframe x) s.val *
        canonicalCoframeCoefficient (c.coframe x) u.val
    rw [canonicalSquareMap_tmul]
    simp only [squaredCoframeCoefficient, canonicalTensorProduct_apply,
      canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun f => f t) h

def squaredGenerator (x : ℝ × M.Point) : SquaredCanonicalTensor n :=
  coframeSquaredGenerator (c.coframe x)

theorem reconstruction {x : ℝ × M.Point} (hx : x ∈ c.domain)
    (s : squaredCanonicalSubmodule (J x.1 x.2)) :
    s.val = squaredCoframeCoefficient (c.coframe x) s.val • c.squaredGenerator x :=
  squaredCoframe_reconstruction _ (c.invertible_coframe x hx) _
    (c.intertwines_coframe x hx) _ s.property

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

open scoped Classical in
/-- The fiber topology is the canonical tensor-product module topology.
Only coframe tensor coordinates enter the pretrivialization. -/
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : (ℝ × M.Point) => CanonicalTensorSquare (J x.1 x.2))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.domain then
    ⟨p.1, (c.tensorCoordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : (ℝ × M.Point) => CanonicalTensorSquare (J x.1 x.2))) ⁻¹' c.domain
  target := c.domain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.domain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : CanonicalTensorSquare (J x.1 x.2) =>
      (⟨x, t⟩ : TotalSpace ℂ (fun x => CanonicalTensorSquare (J x.1 x.2))))
      ((c.tensorCoordinateEquiv x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.tensorCoordinateEquiv p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_domain.prod isOpen_univ
  baseSet := c.domain
  open_baseSet := c.isOpen_domain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance tensorPretrivialization_complexLinear : c.tensorPretrivialization.IsLinear ℂ where
  linear x _ := (c.tensorCoordinateLinearMap x).isLinear

instance tensorPretrivialization_realLinear : c.tensorPretrivialization.IsLinear ℝ where
  linear x _ := ((c.tensorCoordinateLinearMap x).restrictScalars ℝ).isLinear

theorem tensorPretrivialization_symm {x : (ℝ × M.Point)} (hx : x ∈ c.domain) (q : ℂ) :
    c.tensorPretrivialization.symm x q = (c.tensorCoordinateEquiv x hx).symm q := by
  apply (c.tensorCoordinateEquiv x hx).injective
  rw [(c.tensorCoordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization.apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : (ℝ × M.Point)} (hx : x ∈ c.domain) :
    Topology.IsInducing (c.tensorPretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

def transition (d : IntrinsicVerticalCanonicalChart M J) (x : (ℝ × M.Point)) : ℂ :=
  squaredCoframeTransition (c.coframe x) (d.coframe x)

theorem smooth_transition (d : IntrinsicVerticalCanonicalChart M J) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞ (c.transition d) (c.domain ∩ d.domain) :=
  d.smooth_coefficient (c.isOpen_domain.inter d.isOpen_domain) inter_subset_right
    c.squaredGenerator (fun b => (c.smooth_squaredGenerator b).mono
      (fun _ hp => ⟨hp.1, hp.2.1⟩))

theorem tensorTransition_apply (d : IntrinsicVerticalCanonicalChart M J) {x : (ℝ × M.Point)}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 =
      c.transition d x * q := by
  rw [c.tensorPretrivialization_symm hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap]
  have hr := c.reconstruction hx.1
    (canonicalSquareMap (J x.1 x.2) ((c.tensorCoordinateEquiv x hx.1).symm q))
  have hq : squaredCoframeCoefficient (c.coframe x)
      (canonicalSquareMap (J x.1 x.2) ((c.tensorCoordinateEquiv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * squaredCoframeCoefficient (d.coframe x) (c.squaredGenerator x) = _
  exact mul_comm _ _

def transitionMap (d : IntrinsicVerticalCanonicalChart M J) (x : (ℝ × M.Point)) : ℂ →L[ℝ] ℂ :=
  c.transition d x • ContinuousLinearMap.id ℝ ℂ

theorem smooth_transitionMap (d : IntrinsicVerticalCanonicalChart M J) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap d) (c.domain ∩ d.domain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition d)

theorem transitionMap_apply (d : IntrinsicVerticalCanonicalChart M J) {x : (ℝ × M.Point)}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    c.transitionMap d x q =
      (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 :=
  (c.tensorTransition_apply d hx q).symm

end IntrinsicVerticalCanonicalChart

/-- Native tensor-square bundle for a smooth vertical complex field.
The arbitrary base may include independent parameter directions. -/
def intrinsicVerticalCanonicalTensorSquareVectorPrebundle
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : ℝ × M.Point => CanonicalTensorSquare (J x.1 x.2)) where
  pretrivializationAtlas := Set.range IntrinsicVerticalCanonicalChart.tensorPretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (intrinsicVerticalCanonicalChartAt M J hJ hJsq a).tensorPretrivialization
  mem_base_pretrivializationAt := mem_intrinsicVerticalCanonicalChartAt_domain M J hJ hJsq
  pretrivialization_mem_atlas a := ⟨intrinsicVerticalCanonicalChartAt M J hJ hJsq a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, (c.smooth_transitionMap d).continuousOn,
      fun _ hx q => c.transitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (intrinsicVerticalCanonicalChartAt M J hJ hJsq a).tensorPretrivialization_isInducing
      (mem_intrinsicVerticalCanonicalChartAt_domain M J hJ hJsq a)

instance intrinsicVerticalCanonicalTensorSquareVectorPrebundle_isContMDiff
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) :
    (intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq).IsContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, c.smooth_transitionMap d,
      fun _ hx q => c.transitionMap_apply d hx q⟩

theorem intrinsicVerticalCanonicalTensorSquareVectorBundle_smooth
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) :
    let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : ℝ × M.Point => CanonicalTensorSquare (J x.1 x.2)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) :=
  (intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq).contMDiffVectorBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))

/-- The independently constructed atlas has complex-linear transitions,
so the native smooth real bundle is also a complex line bundle. -/
theorem intrinsicVerticalCanonicalTensorSquareVectorBundle_complex
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) :
    let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : ℝ × M.Point => CanonicalTensorSquare (J x.1 x.2)) := by
  dsimp only
  let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq
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
    have hc : ContinuousOn (fun x => L (c.transition d x)) (c.domain ∩ d.domain) :=
      L.continuous.comp_continuousOn (c.smooth_transition d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (c.transitionMap_apply d hx q).symm
    · exact hx

theorem intrinsicVerticalCanonicalTensorSquareVectorBundle_finrank
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2) (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v) (x : ℝ × M.Point) :
    Module.finrank ℂ (CanonicalTensorSquare (J x.1 x.2)) = 1 := by
  let c := intrinsicVerticalCanonicalChartAt M J hJ hJsq x
  rw [(c.tensorCoordinateEquiv x (mem_intrinsicVerticalCanonicalChartAt_domain M J hJ hJsq x)).finrank_eq]
  exact Module.finrank_self ℂ


set_option maxHeartbeats 800000 in
/-- Native smoothness on the global vertical tensor-square bundle is
equivalent to joint smoothness of its actual spatial two-block tensor.
The reverse direction reconstructs that tensor in every spatial chart. -/
theorem intrinsicVerticalCanonicalTensorSquareSection_smooth_iff
    {n : ℕ} (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ a, ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
      almostComplexInChart M a (J p.1) p.2)
        (univ ×ˢ (chartAt (Model (2 * n)) a).target))
    (hJsq : ∀ t x v, J t x (J t x v) = -v)
    (s : (p : ℝ × M.Point) → CanonicalTensorSquare (J p.1 p.2)) :
    let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    let I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))
    ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, s p⟩ : TotalSpace ℂ
        (fun p : ℝ × M.Point => CanonicalTensorSquare (J p.1 p.2)))) ↔
      IsSmoothVerticalSquaredTensorOn M
        (fun p => (canonicalSquareMap (J p.1 p.2) (s p)).val) univ := by
  dsimp only
  let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M J hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  let S := fun p => (canonicalSquareMap (J p.1 p.2) (s p)).val
  constructor
  · intro hn b p hp
    let e := parameterSpatialCoordinates M b
    let x := e.symm p
    let c := intrinsicVerticalCanonicalChartAt M J hJ hJsq x
    have hx : x ∈ c.domain := mem_intrinsicVerticalCanonicalChartAt_domain M J hJ hJsq x
    have hq : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, ℂ) ∞ (fun z => c.tensorCoordinateLinearMap z (s z)) x :=
      (Bundle.contMDiffAt_section x).mp (hn x)
    simp_rw [← c.coefficient_squareMap] at hq
    have hspatial : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞
        (chartAt (Model (2 * n)) b).symm p.2 :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
        ((chartAt (Model (2 * n)) b).open_target.mem_nhds hp.1.2)
    have he : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ e.symm p := by
      have ht : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ) ∞ Prod.fst p :=
        contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst
      have hv : ContMDiffAt 𝓘(ℝ, ℝ × Model (2 * n))
          𝓘(ℝ, Model (2 * n)) ∞ Prod.snd p :=
        contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd
      exact ht.prodMk (hspatial.comp p hv)
    have hscalar := (hq.comp p he).contDiffAt
    have hD := isOpen_intrinsicParameterCoordinateDomain M b c.isOpen_domain
    have hpD : p ∈ intrinsicParameterCoordinateDomain M b c.domain := ⟨hp.1, hx⟩
    have hg := (c.smooth_squaredGenerator b).contDiffAt (hD.mem_nhds hpD)
    apply ((hscalar.smul hg).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hD.mem_nhds hpD] with z hz
    have hr := c.reconstruction hz.2 (canonicalSquareMap (J (e.symm z).1 (e.symm z).2)
      (s (e.symm z)))
    ext v
    exact congrArg (fun t : SquaredCanonicalTensor n =>
      t (fun i => M.inverseChartTangentMap b z.2 (v i))) hr
  · intro hs x
    rw [Bundle.contMDiffAt_section]
    let c := intrinsicVerticalCanonicalChartAt M J hJ hJsq x
    have hx : x ∈ c.domain := mem_intrinsicVerticalCanonicalChartAt_domain M J hJ hJsq x
    have hsOn : IsSmoothVerticalSquaredTensorOn M S c.domain :=
      fun b => (hs b).mono (fun p hp => ⟨hp.1, mem_univ _⟩)
    have hq := (c.smooth_coefficient c.isOpen_domain subset_rfl S hsOn).contMDiffAt
      (c.isOpen_domain.mem_nhds hx)
    exact hq.congr_of_eventuallyEq (Eventually.of_forall
      (fun z => (c.coefficient_squareMap z (s z)).symm))

namespace NativeChartedMaslovFamily

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}

set_option maxHeartbeats 600000 in
/-- A native charted Maslov family supplies a native smooth section of
the globally glued intrinsic vertical tensor-square bundle. No global
bundle, overlap smoothness, or section correspondence is assumed. -/
theorem contMDiff_intrinsicTensorSection (f : NativeChartedMaslovFamily M eta) :
    let a := intrinsicVerticalCanonicalTensorSquareVectorPrebundle M f.J
      (f.smoothJ) f.complex
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    let I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))
    ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, f.tensorSection p.1 p.2⟩ : TotalSpace ℂ
        (fun p : ℝ × M.Point => CanonicalTensorSquare (f.J p.1 p.2)))) := by
  apply (intrinsicVerticalCanonicalTensorSquareSection_smooth_iff M f.J
    f.smoothJ f.complex (fun p => f.tensorSection p.1 p.2)).mpr
  intro b
  exact (f.smooth_squaredTensor b).mono (fun _ hp => hp.1)

end NativeChartedMaslovFamily

end FsFltz.Geometry
