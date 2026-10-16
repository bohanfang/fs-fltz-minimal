import FsFltz.Geometry.CanonicalSquareBundle

/-!
# Canonical squares for vertical complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 794–814. The base manifold and the vertical real rank
are independent. In particular a one-parameter family has base dimension
`2n + 1` and vertical rank `2n`; its canonical line is the determinant of
the vertical complex tangent, not of the tangent to the parameter base.

At a base point, finite-dimensional complex linear algebra constructs a
coframe. Projecting that coframe against the varying complex structure
gives a smooth complex coframe near the point: it is invertible there by
openness of invertibility. Inverse-frame evaluation and determinant
reconstruction give scalar coordinates on the genuine canonical fibers.
Their overlap maps are smooth and complex linear. Tensoring the two line
coordinates gives coordinates on the actual tensor square, with its
canonical module topology. The scalar coordinate of natural tensor
multiplication equals direct two-block inverse-frame evaluation. This
identifies native smoothness of a section with smoothness of its actual
tensor image.

This module treats a trivialized vertical real bundle over an arbitrary
base. Applying it on parameter–spatial coordinate domains proves a local
family bridge. `IntrinsicVerticalCanonicalBundle` glues those domains through
the actual spatial tangent transition maps for whole-time complex fields.
The direct interval-bundle route uses locally extending coframes instead;
it does not require a whole-time complex extension. The reverse bridge
from native interval smoothness to smooth extension witnesses is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

section Base

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  (I : ModelWithCorners ℝ E H) {n : ℕ}

/-- A coframe chart for a vertical complex structure. The base dimension
is unrestricted, and the fibers have real dimension `2n`. -/
structure VerticalCanonicalChart (J : B → Model (2 * n) →L[ℝ] Model (2 * n)) where
  domain : Set B
  isOpen_domain : IsOpen domain
  coframe : B → Model (2 * n) →L[ℝ] TangentCoordinates n
  smooth_coframe : ContMDiffOn I 𝓘(ℝ, Model (2 * n) →L[ℝ] TangentCoordinates n)
    ∞ coframe domain
  invertible_coframe : ∀ x ∈ domain, (coframe x).IsInvertible
  intertwines_coframe : ∀ x ∈ domain, ∀ v,
    coframe x (J x v) = coordinateComplexStructure n (coframe x v)

variable {I} {J : B → Model (2 * n) →L[ℝ] Model (2 * n)}

/-- Finite-dimensional algebra supplies the seed coframe; projection and
openness supply its smooth invertible neighborhood on any base. -/
theorem exists_verticalCanonicalChart
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : B) :
    ∃ c : VerticalCanonicalChart I J, a ∈ c.domain := by
  obtain ⟨C, hC⟩ := exists_complexCoframe (J a) (hJsq a)
  let F := fun x => projectedComplexCoframe C (J x)
  have hs : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] TangentCoordinates n) ∞ F := by
    have hp : ContDiff ℝ ∞ (projectedComplexCoframe C) :=
      contDiffOn_univ.mp (contDiffOn_projectedComplexCoframe C contDiffOn_id)
    exact hp.contMDiff.comp hJ
  have ht := hs.continuous.continuousAt.tendsto (x := a)
  have he : F a = C.toContinuousLinearMap := projectedComplexCoframe_eq C (J a) hC
  rw [he] at ht
  have hi : ∀ᶠ x in 𝓝 a, (F x).IsInvertible := ht C.nhds
  obtain ⟨U, hU, hUo, haU⟩ := mem_nhds_iff.mp hi
  exact ⟨⟨U, hUo, F, hs.contMDiffOn, fun x hx => hU hx,
    fun x _ => projectedComplexCoframe_intertwines C (J x) (hJsq x)⟩, haU⟩

def verticalCanonicalChartAt
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : B) : VerticalCanonicalChart I J :=
  (exists_verticalCanonicalChart hJ hJsq a).choose

theorem mem_verticalCanonicalChartAt_domain
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : B) :
    a ∈ (verticalCanonicalChartAt hJ hJsq a).domain :=
  (exists_verticalCanonicalChart hJ hJsq a).choose_spec

namespace VerticalCanonicalChart

variable (c : VerticalCanonicalChart I J)

def lineCoordinateLinearMap (x : B) : canonicalSubmodule (J x) →ₗ[ℂ] ℂ where
  toFun s := canonicalCoframeCoefficient (c.coframe x) s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : B) (hx : x ∈ c.domain) :
    canonicalSubmodule (J x) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap x
  invFun q := q • (⟨coframeCanonicalGenerator (c.coframe x),
    coframeCanonicalGenerator_canonical _ (c.invertible_coframe x hx) _
      (c.intertwines_coframe x hx)⟩ : canonicalSubmodule (J x))
  left_inv s := Subtype.ext (canonicalCoframe_reconstruction _
    (c.invertible_coframe x hx) _ (c.intertwines_coframe x hx) _ s.property).symm
  right_inv q := by
    change q * canonicalCoframeCoefficient (c.coframe x)
      (coframeCanonicalGenerator (c.coframe x)) = q
    rw [coframeCanonicalGenerator_frame _ (c.invertible_coframe x hx), mul_one]

/-- The coordinate is the tensor product of two unsquared line
coordinates, independently of natural square multiplication. -/
def tensorCoordinateLinearMap (x : B) : CanonicalTensorSquare (J x) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap x) (c.lineCoordinateLinearMap x))

def tensorCoordinateEquiv (x : B) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv x hx) (c.lineCoordinateEquiv x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : B) (hx : x ∈ c.domain) :
    (c.tensorCoordinateEquiv x hx).toLinearMap = c.tensorCoordinateLinearMap x := rfl

def tensorCoordinateContinuousEquiv (x : B) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- The bridge is an equality of the independently constructed scalar
coordinates, proved on pure tensors and extended by tensor linearity. -/
theorem coefficient_squareMap (x : B) (t : CanonicalTensorSquare (J x)) :
    squaredCoframeCoefficient (c.coframe x) (canonicalSquareMap (J x) t).val =
      c.tensorCoordinateLinearMap x t := by
  let L : squaredCanonicalSubmodule (J x) →ₗ[ℂ] ℂ :=
    { toFun s := squaredCoframeCoefficient (c.coframe x) s.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : L.comp (canonicalSquareMap (J x)) = c.tensorCoordinateLinearMap x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change squaredCoframeCoefficient (c.coframe x)
      (canonicalSquareMap (J x) (s ⊗ₜ[ℂ] u)).val =
      canonicalCoframeCoefficient (c.coframe x) s.val *
        canonicalCoframeCoefficient (c.coframe x) u.val
    rw [canonicalSquareMap_tmul]
    simp only [squaredCoframeCoefficient, canonicalTensorProduct_apply,
      canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun f => f t) h

def squaredGenerator (x : B) : SquaredCanonicalTensor n :=
  coframeSquaredGenerator (c.coframe x)

theorem reconstruction {x : B} (hx : x ∈ c.domain)
    (s : squaredCanonicalSubmodule (J x)) :
    s.val = squaredCoframeCoefficient (c.coframe x) s.val • c.squaredGenerator x :=
  squaredCoframe_reconstruction _ (c.invertible_coframe x hx) _
    (c.intertwines_coframe x hx) _ s.property

theorem smooth_squaredGenerator :
    ContMDiffOn I 𝓘(ℝ, SquaredCanonicalTensor n) ∞ c.squaredGenerator c.domain := by
  have hs : ContDiff ℝ ∞
      (coframeSquaredGenerator : (Model (2 * n) →L[ℝ] TangentCoordinates n) →
        SquaredCanonicalTensor n) :=
    contDiffOn_univ.mp (contDiffOn_coframeSquaredGenerator contDiffOn_id)
  exact hs.contMDiff.comp_contMDiffOn c.smooth_coframe

/-- Inverse-frame evaluation is jointly smooth on every actual coframe
domain, including on bases of odd dimension. -/
theorem smooth_coefficient {U : Set B} (hU : IsOpen U) (hUc : U ⊆ c.domain)
    (s : B → SquaredCanonicalTensor n)
    (hs : ContMDiffOn I 𝓘(ℝ, SquaredCanonicalTensor n) ∞ s U) :
    ContMDiffOn I 𝓘(ℝ, ℂ) ∞
      (fun x => squaredCoframeCoefficient (c.coframe x) (s x)) U := by
  intro x hx
  have hC := (c.smooth_coframe.mono hUc).contMDiffAt (hU.mem_nhds hx)
  let W : Set ((Model (2 * n) →L[ℝ] TangentCoordinates n) × SquaredCanonicalTensor n) :=
    {p | p.1.IsInvertible}
  have hWo : IsOpen W :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage continuous_fst
  have he : ContDiffOn ℝ ∞
      (fun p => squaredCoframeCoefficient p.1 p.2) W :=
    contDiffOn_squaredCoframeCoefficient contDiffOn_fst (fun _ hp => hp) contDiffOn_snd
  have hmem : (c.coframe x, s x) ∈ W := c.invertible_coframe x (hUc hx)
  exact ((he.contDiffAt (hWo.mem_nhds hmem)).comp_contMDiffAt
    (f := fun z => (c.coframe z, s z))
    (hC.prodMk_space (hs.contMDiffAt (hU.mem_nhds hx)))).contMDiffWithinAt

open scoped Classical in
/-- The fiber topology is the canonical tensor-product module topology.
Only coframe tensor coordinates enter the pretrivialization. -/
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : B => CanonicalTensorSquare (J x))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.domain then
    ⟨p.1, (c.tensorCoordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : B => CanonicalTensorSquare (J x))) ⁻¹' c.domain
  target := c.domain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.domain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : CanonicalTensorSquare (J x) =>
      (⟨x, t⟩ : TotalSpace ℂ (fun x => CanonicalTensorSquare (J x))))
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

theorem tensorPretrivialization_symm {x : B} (hx : x ∈ c.domain) (q : ℂ) :
    c.tensorPretrivialization.symm x q = (c.tensorCoordinateEquiv x hx).symm q := by
  apply (c.tensorCoordinateEquiv x hx).injective
  rw [(c.tensorCoordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization.apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : B} (hx : x ∈ c.domain) :
    Topology.IsInducing (c.tensorPretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

def transition (d : VerticalCanonicalChart I J) (x : B) : ℂ :=
  squaredCoframeTransition (c.coframe x) (d.coframe x)

theorem smooth_transition (d : VerticalCanonicalChart I J) :
    ContMDiffOn I 𝓘(ℝ, ℂ) ∞ (c.transition d) (c.domain ∩ d.domain) :=
  d.smooth_coefficient (c.isOpen_domain.inter d.isOpen_domain) inter_subset_right
    c.squaredGenerator (c.smooth_squaredGenerator.mono inter_subset_left)

theorem tensorTransition_apply (d : VerticalCanonicalChart I J) {x : B}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 =
      c.transition d x * q := by
  rw [c.tensorPretrivialization_symm hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap]
  have hr := c.reconstruction hx.1
    (canonicalSquareMap (J x) ((c.tensorCoordinateEquiv x hx.1).symm q))
  have hq : squaredCoframeCoefficient (c.coframe x)
      (canonicalSquareMap (J x) ((c.tensorCoordinateEquiv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * squaredCoframeCoefficient (d.coframe x) (c.squaredGenerator x) = _
  exact mul_comm _ _

def transitionMap (d : VerticalCanonicalChart I J) (x : B) : ℂ →L[ℝ] ℂ :=
  c.transition d x • ContinuousLinearMap.id ℝ ℂ

theorem smooth_transitionMap (d : VerticalCanonicalChart I J) :
    ContMDiffOn I 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap d) (c.domain ∩ d.domain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition d)

theorem transitionMap_apply (d : VerticalCanonicalChart I J) {x : B}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    c.transitionMap d x q =
      (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 :=
  (c.tensorTransition_apply d hx q).symm

end VerticalCanonicalChart

/-- Native tensor-square bundle for a smooth vertical complex field.
The arbitrary base may include independent parameter directions. -/
def verticalCanonicalTensorSquareVectorPrebundle
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : B => CanonicalTensorSquare (J x)) where
  pretrivializationAtlas := Set.range VerticalCanonicalChart.tensorPretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (verticalCanonicalChartAt hJ hJsq a).tensorPretrivialization
  mem_base_pretrivializationAt := mem_verticalCanonicalChartAt_domain hJ hJsq
  pretrivialization_mem_atlas a := ⟨verticalCanonicalChartAt hJ hJsq a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, (c.smooth_transitionMap d).continuousOn,
      fun _ hx q => c.transitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (verticalCanonicalChartAt hJ hJsq a).tensorPretrivialization_isInducing
      (mem_verticalCanonicalChartAt_domain hJ hJsq a)

instance verticalCanonicalTensorSquareVectorPrebundle_isContMDiff
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    (verticalCanonicalTensorSquareVectorPrebundle hJ hJsq).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, c.smooth_transitionMap d,
      fun _ hx q => c.transitionMap_apply d hx q⟩

theorem verticalCanonicalTensorSquareVectorBundle_smooth
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : B => CanonicalTensorSquare (J x)) I :=
  (verticalCanonicalTensorSquareVectorPrebundle hJ hJsq).contMDiffVectorBundle I

/-- The independently constructed atlas has complex-linear transitions,
so the native smooth real bundle is also a complex line bundle. -/
theorem verticalCanonicalTensorSquareVectorBundle_complex
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : B => CanonicalTensorSquare (J x)) := by
  dsimp only
  let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
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

theorem verticalCanonicalTensorSquareVectorBundle_finrank
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v) (x : B) :
    Module.finrank ℂ (CanonicalTensorSquare (J x)) = 1 := by
  let c := verticalCanonicalChartAt hJ hJsq x
  rw [(c.tensorCoordinateEquiv x (mem_verticalCanonicalChartAt_domain hJ hJsq x)).finrank_eq]
  exact Module.finrank_self ℂ

/-- A section of the genuine vertical tensor square is smooth exactly
when its image by natural multiplication is a smooth actual two-block
canonical tensor. Neither implication is a certificate field. -/
theorem verticalCanonicalTensorSquareSection_smooth_iff
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v)
    (s : (x : B) → CanonicalTensorSquare (J x)) :
    let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff I (I.prod 𝓘(ℝ, ℂ)) ∞
      (fun x => (⟨x, s x⟩ : TotalSpace ℂ (fun x : B => CanonicalTensorSquare (J x)))) ↔
      ContMDiff I 𝓘(ℝ, SquaredCanonicalTensor n) ∞
        (fun x => (canonicalSquareMap (J x) (s x)).val) := by
  dsimp only
  let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  constructor
  · intro hs x
    let c := verticalCanonicalChartAt hJ hJsq x
    have hx : x ∈ c.domain := mem_verticalCanonicalChartAt_domain hJ hJsq x
    have hq : ContMDiffAt I 𝓘(ℝ, ℂ) ∞
        (fun z => c.tensorCoordinateLinearMap z (s z)) x :=
      (Bundle.contMDiffAt_section x).mp (hs x)
    have hg := c.smooth_squaredGenerator.contMDiffAt (c.isOpen_domain.mem_nhds hx)
    have hm : ContDiff ℝ ∞
        (fun p : ℂ × SquaredCanonicalTensor n => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    apply (hm.contDiffAt.comp_contMDiffAt (hq.prodMk_space hg)).congr_of_eventuallyEq
    filter_upwards [c.isOpen_domain.mem_nhds hx] with z hz
    have hr := c.reconstruction hz (canonicalSquareMap (J z) (s z))
    rw [c.coefficient_squareMap] at hr
    exact hr
  · intro hs x
    rw [Bundle.contMDiffAt_section]
    let c := verticalCanonicalChartAt hJ hJsq x
    have hx : x ∈ c.domain := mem_verticalCanonicalChartAt_domain hJ hJsq x
    have hq := (c.smooth_coefficient c.isOpen_domain (Subset.refl _)
      (fun z => (canonicalSquareMap (J z) (s z)).val) hs.contMDiffOn).contMDiffAt
        (c.isOpen_domain.mem_nhds hx)
    simp_rw [c.coefficient_squareMap] at hq
    exact hq

end Base

end FsFltz.Geometry
