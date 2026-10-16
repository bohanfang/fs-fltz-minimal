import FsFltz.Geometry.CanonicalLineAtlas

/-!
# The natural smooth tensor square of the canonical line

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. Tensor-square coordinates are the tensor product
of the native unsquared determinant coordinates. Their fiber topology is
the canonical module topology, independent of the natural multiplication
map. The natural map to two-block canonical tensors is compared to these
coordinates by a proved identity. This gives a smooth equivalence of total
spaces with smooth inverse. Pulling an actual Maslov representative back
through that inverse produces a native smooth nonvanishing tensor-square
section whose natural image is exactly the original representative.

This module supplies the fixed-almost-complex-structure bundle. Compatible
change-of-structure transport, a smooth compatible path, and invariance of
the fixed-structure section classes are proved in `CompatibleComplexTransport`,
`CompatibleComplexPath`, and `FixedComplexMaslov`. `VerticalCanonicalBundle`
separates vertical rank from parameter-base dimension, and
`VerticalMaslovFamily` proves the native parameter–spatial chart bridge and
its fixed-ambient-form homotopy consumer. `IntrinsicVerticalCanonicalBundle`
glues the native vertical-family atlas for whole-time complex fields.
The original-family endpoint bridge remains pending; the geometric target
is not asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

abbrev CanonicalTensorSquare {n : ℕ} (J : Model (2 * n) →L[ℝ] Model (2 * n)) :=
  TensorProduct ℂ (canonicalSubmodule J) (canonicalSubmodule J)

/-- The actual tensor product carries the canonical module topology,
without using the desired square multiplication equivalence. -/
instance canonicalTensorSquare_topology {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    TopologicalSpace (CanonicalTensorSquare J) := moduleTopology ℂ _

instance canonicalTensorSquare_continuousAdd {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    ContinuousAdd (CanonicalTensorSquare J) := ModuleTopology.continuousAdd ℂ _

instance canonicalTensorSquare_continuousSMul {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    ContinuousSMul ℂ (CanonicalTensorSquare J) := ModuleTopology.continuousSMul ℂ _

section

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : AlmostComplexField M}

local instance tensorSquareField_topology (x : M.Point) :
    TopologicalSpace (CanonicalTensorSquare (J x)) :=
  canonicalTensorSquare_topology (J x)

namespace CanonicalSquaredChart
variable (c : CanonicalSquaredChart M J)

/-- The tensor coordinate is induced by the two unsquared line coordinates. -/
def tensorCoordinateLinearMap (x : M.Point) : CanonicalTensorSquare (J x) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap x) (c.lineCoordinateLinearMap x))

def tensorCoordinateEquiv (x : M.Point) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv x hx) (c.lineCoordinateEquiv x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : M.Point) (hx : x ∈ c.domain) :
    (c.tensorCoordinateEquiv x hx).toLinearMap = c.tensorCoordinateLinearMap x := rfl

def tensorCoordinateContinuousEquiv (x : M.Point) (hx : x ∈ c.domain) :
    CanonicalTensorSquare (J x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- Natural multiplication preserves the tensor-product scalar coordinate. -/
theorem coefficient_squareMap (x : M.Point) (t : CanonicalTensorSquare (J x)) :
    c.coefficient x (canonicalSquareMap (J x) t).val = c.tensorCoordinateLinearMap x t := by
  have h : (c.coordinateLinearMap x).comp (canonicalSquareMap (J x)) =
      c.tensorCoordinateLinearMap x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change c.coefficient x (canonicalSquareMap (J x) (s ⊗ₜ[ℂ] u)).val =
      c.lineCoefficient x s.val * c.lineCoefficient x u.val
    rw [canonicalSquareMap_tmul]
    simp only [coefficient, squaredCoframeCoefficient, canonicalTensorProduct_apply,
      lineCoefficient, canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun L => L t) h

theorem tensorCoordinate_squareEquiv_symm (x : M.Point)
    (hJsq : ∀ v, J x (J x v) = -v) (s : squaredCanonicalSubmodule (J x)) :
    c.tensorCoordinateLinearMap x
      ((canonicalSquareEquivOfComplexStructure (J x) hJsq).symm s) =
      c.coefficient x s.val := by
  rw [← c.coefficient_squareMap]
  have h := (canonicalSquareEquivOfComplexStructure (J x) hJsq).apply_symm_apply s
  change canonicalSquareMap (J x)
    ((canonicalSquareEquivOfComplexStructure (J x) hJsq).symm s) = s at h
  rw [h]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : M.Point => CanonicalTensorSquare (J x))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.domain then
    ⟨p.1, (c.tensorCoordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : M.Point => CanonicalTensorSquare (J x))) ⁻¹' c.domain
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

theorem tensorPretrivialization_symm {x : M.Point} (hx : x ∈ c.domain) (q : ℂ) :
    c.tensorPretrivialization.symm x q = (c.tensorCoordinateEquiv x hx).symm q := by
  apply (c.tensorCoordinateEquiv x hx).injective
  rw [(c.tensorCoordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization.apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : M.Point} (hx : x ∈ c.domain) :
    Topology.IsInducing (c.tensorPretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

theorem tensorTransition_apply (d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 =
      c.lineTransition d x ^ 2 * q := by
  rw [c.tensorPretrivialization_symm hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap, ← c.transition_eq_lineTransition_sq d x]
  have hr := c.reconstruction hx.1
    (canonicalSquareMap (J x) ((c.tensorCoordinateEquiv x hx.1).symm q))
  have hq : c.coefficient x
      (canonicalSquareMap (J x) ((c.tensorCoordinateEquiv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * d.coefficient x (c.generator x) = c.transition d x * q
  exact mul_comm _ _

def tensorTransitionMap (d : CanonicalSquaredChart M J) (x : M.Point) : ℂ →L[ℝ] ℂ :=
  c.lineTransition d x ^ 2 • ContinuousLinearMap.id ℝ ℂ

theorem smooth_tensorTransitionMap (d : CanonicalSquaredChart M J) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.tensorTransitionMap d) (c.domain ∩ d.domain) := by
  have he : c.tensorTransitionMap d = c.transitionMap d := by
    funext x
    dsimp only [tensorTransitionMap, transitionMap]
    rw [c.transition_eq_lineTransition_sq]
  rw [he]
  exact c.smooth_transitionMap d

theorem tensorTransitionMap_apply (d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    c.tensorTransitionMap d x q =
      (d.tensorPretrivialization ⟨x, c.tensorPretrivialization.symm x q⟩).2 :=
  (c.tensorTransition_apply d hx q).symm

end CanonicalSquaredChart

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor-product fibers form a native smooth bundle, with
coordinates constructed from the two unsquared determinant coordinates. -/
def canonicalTensorSquareVectorPrebundle {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : M.Point => CanonicalTensorSquare (J x)) where
  pretrivializationAtlas := Set.range CanonicalSquaredChart.tensorPretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (canonicalSquaredChartAt M J hJ hJsq a).tensorPretrivialization
  mem_base_pretrivializationAt := mem_canonicalSquaredChartAt_domain M J hJ hJsq
  pretrivialization_mem_atlas a := ⟨canonicalSquaredChartAt M J hJ hJsq a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.tensorTransitionMap d, (c.smooth_tensorTransitionMap d).continuousOn,
      fun _ hx q => c.tensorTransitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (canonicalSquaredChartAt M J hJ hJsq a).tensorPretrivialization_isInducing
      (mem_canonicalSquaredChartAt_domain M J hJ hJsq a)

instance canonicalTensorSquareVectorPrebundle_isContMDiff {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    (canonicalTensorSquareVectorPrebundle M J hJ hJsq).IsContMDiff
      𝓘(ℝ, Model (2 * n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.tensorTransitionMap d, c.smooth_tensorTransitionMap d,
      fun _ hx q => c.tensorTransitionMap_apply d hx q⟩

/-- The native tensor-product bundle is smooth for the independently
constructed tensor-coordinate topology and atlas. -/
theorem canonicalTensorSquareVectorBundle_smooth {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := canonicalTensorSquareVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : M.Point => CanonicalTensorSquare (J x))
      𝓘(ℝ, Model (2 * n)) :=
  (canonicalTensorSquareVectorPrebundle M J hJ hJsq).contMDiffVectorBundle
    𝓘(ℝ, Model (2 * n))

set_option backward.isDefEq.respectTransparency false in
/-- The same native atlas is a complex vector bundle. Smoothness is still
real smoothness because the base is a real manifold. -/
theorem canonicalTensorSquareVectorBundle_complex {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := canonicalTensorSquareVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : M.Point => CanonicalTensorSquare (J x)) := by
  dsimp only
  let a := canonicalTensorSquareVectorPrebundle M J hJ hJsq
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
    · rw [c.transition_eq_lineTransition_sq]
      exact (c.tensorTransitionMap_apply d hx q).symm
    · exact hx

/-- The global equivalence is the natural multiplication map on every
fiber. The pointwise algebraic theorem supplies its inverse. -/
def canonicalSquareBundleEquiv {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJsq : ∀ x v, J x (J x v) = -v) :
    TotalSpace ℂ (fun x : M.Point => CanonicalTensorSquare (J x)) ≃
      TotalSpace ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x)) where
  toFun p := ⟨p.proj, canonicalSquareEquivOfComplexStructure (J p.proj)
    (hJsq p.proj) p.snd⟩
  invFun p := ⟨p.proj, (canonicalSquareEquivOfComplexStructure (J p.proj)
    (hJsq p.proj)).symm p.snd⟩
  left_inv p := by
    rcases p with ⟨x, t⟩
    exact congrArg (fun t => (⟨x, t⟩ : TotalSpace ℂ
      (fun x : M.Point => CanonicalTensorSquare (J x))))
      ((canonicalSquareEquivOfComplexStructure (J x) (hJsq x)).symm_apply_apply t)
  right_inv p := by
    rcases p with ⟨x, s⟩
    exact congrArg (fun s => (⟨x, s⟩ : TotalSpace ℂ
      (fun x : M.Point => squaredCanonicalSubmodule (J x))))
      ((canonicalSquareEquivOfComplexStructure (J x) (hJsq x)).apply_symm_apply s)

@[simp] theorem canonicalSquareBundleEquiv_apply {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJsq : ∀ x v, J x (J x v) = -v)
    (p : TotalSpace ℂ (fun x : M.Point => CanonicalTensorSquare (J x))) :
    canonicalSquareBundleEquiv M J hJsq p = ⟨p.proj, canonicalSquareMap (J p.proj) p.snd⟩ := rfl

/-- Both directions of the natural total-space equivalence are smooth.
The tensor-coordinate and two-block atlases are constructed independently;
the multiplication-coordinate identity is the bridge between them. -/
theorem canonicalSquareBundleEquiv_contMDiff {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := canonicalTensorSquareVectorPrebundle M J hJ hJsq
    let b := squaredCanonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := b.totalSpaceTopology
    letI := b.toFiberBundle
    let I := (𝓘(ℝ, Model (2 * n))).prod 𝓘(ℝ, ℂ)
    ContMDiff I I ∞ (canonicalSquareBundleEquiv M J hJsq) ∧
      ContMDiff I I ∞ (canonicalSquareBundleEquiv M J hJsq).symm := by
  dsimp only
  let a := canonicalTensorSquareVectorPrebundle M J hJ hJsq
  let b := squaredCanonicalVectorPrebundle M J hJ hJsq
  let aTopology := a.totalSpaceTopology
  let aBundle := a.toFiberBundle
  let bTopology := b.totalSpaceTopology
  let bBundle := b.toFiberBundle
  constructor
  · intro p
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨Bundle.contMDiffAt_proj (fun x : M.Point => CanonicalTensorSquare (J x)), ?_⟩
    dsimp only [aBundle, bBundle, a, b, id, trivializationAt, FiberBundle.trivializationAt', VectorPrebundle.toFiberBundle,
      VectorPrebundle.toFiberPrebundle, FiberPrebundle.toFiberBundle,
      FiberPrebundle.trivializationOfMemPretrivializationAtlas, canonicalSquareBundleEquiv,
      Equiv.coe_fn_mk, Equiv.symm_mk, canonicalTensorSquareVectorPrebundle,
      squaredCanonicalVectorPrebundle, CanonicalSquaredChart.pretrivialization,
      CanonicalSquaredChart.tensorPretrivialization]
    simp only [Trivialization.coe_mk, OpenPartialHomeomorph.coe_mk,
      canonicalSquareEquivOfComplexStructure, LinearEquiv.ofBijective_apply]
    simp_rw [CanonicalSquaredChart.coefficient_squareMap]
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := (𝓘(ℝ, Model (2 * n))).prod 𝓘(ℝ, ℂ))
        (x := p) (n := ∞))).2
    dsimp only [aBundle, bBundle, a, b, id, trivializationAt, FiberBundle.trivializationAt', VectorPrebundle.toFiberBundle,
      VectorPrebundle.toFiberPrebundle, FiberPrebundle.toFiberBundle,
      FiberPrebundle.trivializationOfMemPretrivializationAtlas, canonicalTensorSquareVectorPrebundle,
      CanonicalSquaredChart.tensorPretrivialization] at hc
    simpa only [Trivialization.coe_mk, OpenPartialHomeomorph.coe_mk] using hc
  · intro p
    rw [Bundle.contMDiffAt_totalSpace]
    refine ⟨Bundle.contMDiffAt_proj (fun x : M.Point => squaredCanonicalSubmodule (J x)), ?_⟩
    dsimp only [aBundle, bBundle, a, b, id, trivializationAt, FiberBundle.trivializationAt', VectorPrebundle.toFiberBundle,
      VectorPrebundle.toFiberPrebundle, FiberPrebundle.toFiberBundle,
      FiberPrebundle.trivializationOfMemPretrivializationAtlas, canonicalSquareBundleEquiv,
      Equiv.coe_fn_mk, Equiv.symm_mk, canonicalTensorSquareVectorPrebundle,
      CanonicalSquaredChart.tensorPretrivialization]
    simp only [Trivialization.coe_mk, OpenPartialHomeomorph.coe_mk]
    simp_rw [CanonicalSquaredChart.tensorCoordinate_squareEquiv_symm]
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id (I := (𝓘(ℝ, Model (2 * n))).prod 𝓘(ℝ, ℂ))
        (x := p) (n := ∞))).2
    dsimp only [aBundle, bBundle, a, b, id, trivializationAt, FiberBundle.trivializationAt', VectorPrebundle.toFiberBundle,
      VectorPrebundle.toFiberPrebundle, FiberPrebundle.toFiberBundle,
      FiberPrebundle.trivializationOfMemPretrivializationAtlas, squaredCanonicalVectorPrebundle,
      CanonicalSquaredChart.pretrivialization] at hc
    simpa only [Trivialization.coe_mk, OpenPartialHomeomorph.coe_mk] using hc

namespace MaslovRepresentative

/-- The actual section of the tensor square corresponding to a Maslov
representative. No tensor-square section equivalence is assumed. -/
def canonicalTensorSquareSection {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (x : M.Point) :
    CanonicalTensorSquare (s.J x) :=
  (canonicalSquareEquivOfComplexStructure (s.J x) (s.compatible.2.1 x)).symm
    ⟨s.tensor x, s.canonical x⟩

/-- Natural multiplication recovers the original actual Maslov tensor. -/
theorem canonicalSquareMap_tensorSquareSection {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (x : M.Point) :
    canonicalSquareMap (s.J x) (s.canonicalTensorSquareSection x) =
      ⟨s.tensor x, s.canonical x⟩ :=
  (canonicalSquareEquivOfComplexStructure (s.J x)
    (s.compatible.2.1 x)).apply_symm_apply _

theorem canonicalTensorSquareSection_ne_zero {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (x : M.Point) :
    s.canonicalTensorSquareSection x ≠ 0 := by
  intro hz
  have h := s.canonicalSquareMap_tensorSquareSection x
  rw [hz, map_zero] at h
  exact s.nowhereZero x (congrArg Subtype.val h).symm

/-- The smooth total-space inverse transports the representative to an
actual native smooth section of the canonical tensor-square bundle. -/
theorem contMDiff_canonicalTensorSquareBundleSection {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s : MaslovRepresentative M eta) :
    let a := canonicalTensorSquareVectorPrebundle M s.J s.compatible.1 s.compatible.2.1
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff 𝓘(ℝ, Model (2 * n)) ((𝓘(ℝ, Model (2 * n))).prod 𝓘(ℝ, ℂ)) ∞
      (fun x => (⟨x, s.canonicalTensorSquareSection x⟩ :
        TotalSpace ℂ (fun x : M.Point => CanonicalTensorSquare (s.J x)))) := by
  dsimp only
  let a := canonicalTensorSquareVectorPrebundle M s.J s.compatible.1 s.compatible.2.1
  let b := squaredCanonicalVectorPrebundle M s.J s.compatible.1 s.compatible.2.1
  let aTopology := a.totalSpaceTopology
  let aBundle := a.toFiberBundle
  let bTopology := b.totalSpaceTopology
  let bBundle := b.toFiberBundle
  exact (canonicalSquareBundleEquiv_contMDiff M s.J s.compatible.1
    s.compatible.2.1).2.comp s.contMDiff_canonicalSquaredBundleSection

end MaslovRepresentative

end
end FsFltz.Geometry
