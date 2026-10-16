import FsFltz.Geometry.CanonicalAtlas

/-!
# Native atlas of the canonical line

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The coframe charts constructed for the squared
canonical line also give unsquared determinant coordinates. The fibers are
the actual alternating complex-canonical tensor subspaces. Their topology
is the existing subspace topology; coframes and overlap smoothness are
proved from the smooth almost complex field.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry

/-- The determinant generator for a possibly noninvertible real coframe. -/
def coframeCanonicalGenerator {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) : CanonicalTensor n :=
  (coordinateVolumeTensor n).compContinuousLinearMap C

def canonicalCoframeCoefficient {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (s : CanonicalTensor n) : ℂ :=
  s (fun i => C.inverse (verticalFrame n i))

theorem coframeCanonicalGenerator_canonical {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    IsCanonicalTensor J (coframeCanonicalGenerator C) := by
  obtain ⟨e, rfl⟩ := hinv
  exact coframeVolumeTensor_canonical e J hCJ

theorem coframeCanonicalGenerator_frame {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible) :
    canonicalCoframeCoefficient C (coframeCanonicalGenerator C) = 1 := by
  simp only [canonicalCoframeCoefficient, coframeCanonicalGenerator,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    hinv.self_apply_inverse]
  exact coordinateVolumeValue_verticalFrame n

theorem canonicalCoframe_reconstruction {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : CanonicalTensor n) (hs : IsCanonicalTensor J s) :
    s = canonicalCoframeCoefficient C s • coframeCanonicalGenerator C := by
  obtain ⟨e, rfl⟩ := hinv
  ext v
  simpa [canonicalCoframeCoefficient, coframeCanonicalGenerator, smul_eq_mul, Function.comp_def] using
    canonicalTensor_reconstruction e J hCJ ⟨s, hs⟩ v

theorem canonicalCoframeCoefficient_comp {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (A : Model (2 * n) →L[ℝ] Model (2 * n)) (hA : A.IsInvertible)
    (s : CanonicalTensor n) :
    canonicalCoframeCoefficient (C.comp A) (s.compContinuousLinearMap A) =
      canonicalCoframeCoefficient C s := by
  simp only [canonicalCoframeCoefficient, hA.inverse_comp_of_right,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply, hA.self_apply_inverse]

namespace CanonicalSquaredChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : AlmostComplexField M}
variable (c : CanonicalSquaredChart M J)

def lineGenerator (x : M.Point) : CanonicalTensor n :=
  coframeCanonicalGenerator (c.tangentCoframe x)

def lineCoefficient (x : M.Point) (s : CanonicalTensor n) : ℂ :=
  canonicalCoframeCoefficient (c.tangentCoframe x) s

theorem lineGenerator_canonical {x : M.Point} (hx : x ∈ c.domain) :
    IsCanonicalTensor (J x) (c.lineGenerator x) :=
  coframeCanonicalGenerator_canonical _ (c.tangentCoframe_invertible hx) _
    (c.tangentCoframe_intertwines hx)

theorem lineCoefficient_generator {x : M.Point} (hx : x ∈ c.domain) :
    c.lineCoefficient x (c.lineGenerator x) = 1 :=
  coframeCanonicalGenerator_frame _ (c.tangentCoframe_invertible hx)

theorem lineReconstruction {x : M.Point} (hx : x ∈ c.domain)
    (s : canonicalSubmodule (J x)) :
    s.val = c.lineCoefficient x s.val • c.lineGenerator x :=
  canonicalCoframe_reconstruction _ (c.tangentCoframe_invertible hx) _
    (c.tangentCoframe_intertwines hx) _ s.property

def lineCoordinateLinearMap (x : M.Point) : canonicalSubmodule (J x) →ₗ[ℂ] ℂ where
  toFun s := c.lineCoefficient x s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : M.Point) (hx : x ∈ c.domain) :
    canonicalSubmodule (J x) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap x
  invFun q := q • (⟨c.lineGenerator x, c.lineGenerator_canonical hx⟩ : canonicalSubmodule (J x))
  left_inv s := Subtype.ext (c.lineReconstruction hx s).symm
  right_inv q := by
    change q * c.lineCoefficient x (c.lineGenerator x) = q
    rw [c.lineCoefficient_generator hx, mul_one]

set_option backward.isDefEq.respectTransparency false in
def lineCoordinateContinuousEquiv (x : M.Point) (hx : x ∈ c.domain) :
    canonicalSubmodule (J x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.lineCoordinateEquiv x hx
  continuous_toFun := by
    change Continuous (fun s : canonicalSubmodule (J x) =>
      s.val (fun i => (c.tangentCoframe x).inverse (verticalFrame n i)))
    fun_prop
  continuous_invFun := by
    change Continuous (fun q : ℂ =>
      q • (⟨c.lineGenerator x, c.lineGenerator_canonical hx⟩ : canonicalSubmodule (J x)))
    exact continuous_id.smul continuous_const

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
def linePretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : M.Point => canonicalSubmodule (J x))) where
  toFun p := (p.proj, c.lineCoefficient p.proj p.snd.val)
  invFun p := if hp : p.1 ∈ c.domain then
    ⟨p.1, (c.lineCoordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : M.Point => canonicalSubmodule (J x))) ⁻¹' c.domain
  target := c.domain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.domain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : canonicalSubmodule (J x) =>
      (⟨x, t⟩ : TotalSpace ℂ (fun x => canonicalSubmodule (J x))))
      ((c.lineCoordinateEquiv x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.lineCoordinateEquiv p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_domain.prod isOpen_univ
  baseSet := c.domain
  open_baseSet := c.isOpen_domain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance linePretrivialization_complexLinear : c.linePretrivialization.IsLinear ℂ where
  linear x _ := (c.lineCoordinateLinearMap x).isLinear

instance linePretrivialization_realLinear : c.linePretrivialization.IsLinear ℝ where
  linear x _ := ((c.lineCoordinateLinearMap x).restrictScalars ℝ).isLinear

theorem linePretrivialization_symm {x : M.Point} (hx : x ∈ c.domain) (q : ℂ) :
    c.linePretrivialization.symm x q = (c.lineCoordinateEquiv x hx).symm q := by
  apply (c.lineCoordinateEquiv x hx).injective
  rw [(c.lineCoordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.linePretrivialization.apply_mk_symm hx q)

theorem linePretrivialization_isInducing {x : M.Point} (hx : x ∈ c.domain) :
    Topology.IsInducing (c.linePretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.lineCoordinateContinuousEquiv x hx).toHomeomorph.isInducing
  have hc : Continuous (c.linePretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk (c.lineCoordinateContinuousEquiv x hx).continuous
  exact Topology.IsInducing.of_comp hc continuous_snd h

def lineTransition (d : CanonicalSquaredChart M J) (x : M.Point) : ℂ :=
  d.lineCoefficient x (c.lineGenerator x)

set_option backward.isDefEq.respectTransparency false in
theorem smooth_lineTransition (d : CanonicalSquaredChart M J) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (c.lineTransition d) (c.domain ∩ d.domain) := by
  intro x hx
  let b := chartAt (Model (2 * n)) x
  let U := b.target ∩ b.symm ⁻¹' (c.domain ∩ d.domain)
  have hU : IsOpen U := b.continuousOn_symm.isOpen_inter_preimage b.open_target
    (c.isOpen_domain.inter d.isOpen_domain)
  have hsubC : U ⊆ b.target ∩ b.symm ⁻¹' c.domain :=
    fun _ hy => ⟨hy.1, hy.2.1⟩
  have hsubD : U ⊆ b.target ∩ b.symm ⁻¹' d.domain :=
    fun _ hy => ⟨hy.1, hy.2.2⟩
  have hC : ContDiffOn ℝ ∞ (fun y =>
      ((c.tangentCoframe (b.symm y)).comp (M.inverseChartTangentMap x y) :
        Model (2 * n) →L[ℝ] TangentCoordinates n)) U :=
    (contDiffOn_localCanonicalCoframe_inChart M c.anchor x
    c.isOpen_coordinates c.smooth_coframe).mono hsubC
  have hD : ContDiffOn ℝ ∞ (fun y =>
      ((d.tangentCoframe (b.symm y)).comp (M.inverseChartTangentMap x y) :
        Model (2 * n) →L[ℝ] TangentCoordinates n)) U :=
    (contDiffOn_localCanonicalCoframe_inChart M d.anchor x
    d.isOpen_coordinates d.smooth_coframe).mono hsubD
  have hinv : ∀ y ∈ U,
      ((d.tangentCoframe (b.symm y)).comp (M.inverseChartTangentMap x y)).IsInvertible :=
    fun y hy => (d.tangentCoframe_invertible hy.2.2).comp
      (inverseChartTangentMap_isInvertible M x y hy.1)
  have ht := contDiffOn_canonicalCoframeTransition hC hD hinv
  have ht' : ContDiffOn ℝ ∞ (c.lineTransition d ∘ b.symm) U := by
    apply ht.congr
    intro y hy
    change d.lineCoefficient (b.symm y) (c.lineGenerator (b.symm y)) = _
    simpa only [canonicalCoframeTransition, canonicalCoframeCoefficient,
      lineGenerator, lineCoefficient, ContinuousLinearMap.comp_apply,
      coframeCanonicalGenerator, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      coordinateVolumeTensor_apply, Function.comp_def] using
      (canonicalCoframeCoefficient_comp (d.tangentCoframe (b.symm y))
        (M.inverseChartTangentMap x y)
        (inverseChartTangentMap_isInvertible M x y hy.1)
        (c.lineGenerator (b.symm y))).symm
  have hbx : b x ∈ U := ⟨b.map_source (mem_chart_source _ x), by
    simpa only [mem_preimage, b.left_inv (mem_chart_source _ x)] using hx⟩
  have htM : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (c.lineTransition d ∘ b.symm) (b x) :=
    contMDiffAt_iff_contDiffAt.mpr (ht'.contDiffAt (hU.mem_nhds hbx))
  have hb : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ b x :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := x)).contMDiffAt
      (b.open_source.mem_nhds (mem_chart_source _ x))
  apply ((htM.comp x hb).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [b.open_source.mem_nhds (mem_chart_source _ x)] with z hz
  exact (congrArg (c.lineTransition d) (b.left_inv hz)).symm

theorem lineTransition_apply (d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    (d.linePretrivialization ⟨x, c.linePretrivialization.symm x q⟩).2 =
      c.lineTransition d x * q := by
  rw [c.linePretrivialization_symm hx.1]
  change q * d.lineCoefficient x (c.lineGenerator x) = _
  exact mul_comm _ _

def lineTransitionMap (d : CanonicalSquaredChart M J) (x : M.Point) : ℂ →L[ℝ] ℂ :=
  c.lineTransition d x • ContinuousLinearMap.id ℝ ℂ

theorem smooth_lineTransitionMap (d : CanonicalSquaredChart M J) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.lineTransitionMap d) (c.domain ∩ d.domain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_lineTransition d)

theorem lineTransitionMap_apply (d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    c.lineTransitionMap d x q =
      (d.linePretrivialization ⟨x, c.linePretrivialization.symm x q⟩).2 :=
  (c.lineTransition_apply d hx q).symm

/-- The existing squared atlas is literally the square of the determinant
transition of the unsquared canonical line. -/
theorem transition_eq_lineTransition_sq (d : CanonicalSquaredChart M J) (x : M.Point) :
    c.transition d x = c.lineTransition d x ^ 2 := by
  simpa only [transition, coefficient, generator, localCanonicalSquaredSection,
    squaredCoframeTransition, canonicalCoframeTransition, tangentCoframe,
    lineTransition, lineCoefficient, lineGenerator, canonicalCoframeCoefficient,
    coframeCanonicalGenerator, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    coordinateVolumeTensor_apply, Function.comp_def] using
    squaredCoframeTransition_eq_square (c.tangentCoframe x) (d.tangentCoframe x)

end CanonicalSquaredChart

set_option backward.isDefEq.respectTransparency false in
/-- The native canonical-line atlas consists of the determinant coordinates
of all coframes. The almost complex field supplies its covering charts. -/
def canonicalVectorPrebundle {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : M.Point => canonicalSubmodule (J x)) where
  pretrivializationAtlas := Set.range CanonicalSquaredChart.linePretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (canonicalSquaredChartAt M J hJ hJsq a).linePretrivialization
  mem_base_pretrivializationAt := mem_canonicalSquaredChartAt_domain M J hJ hJsq
  pretrivialization_mem_atlas a := ⟨canonicalSquaredChartAt M J hJ hJsq a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.lineTransitionMap d, (c.smooth_lineTransitionMap d).continuousOn,
      fun _ hx q => c.lineTransitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (canonicalSquaredChartAt M J hJ hJsq a).linePretrivialization_isInducing
      (mem_canonicalSquaredChartAt_domain M J hJ hJsq a)

instance canonicalVectorPrebundle_isContMDiff {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    (canonicalVectorPrebundle M J hJ hJsq).IsContMDiff
      𝓘(ℝ, Model (2 * n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.lineTransitionMap d, c.smooth_lineTransitionMap d,
      fun _ hx q => c.lineTransitionMap_apply d hx q⟩

/-- All native smooth-bundle properties are proved from the field, with
the actual complex canonical tensor subspaces as fibers. -/
theorem canonicalVectorBundle_smooth {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := canonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : M.Point => canonicalSubmodule (J x))
      𝓘(ℝ, Model (2 * n)) :=
  (canonicalVectorPrebundle M J hJ hJsq).contMDiffVectorBundle
    𝓘(ℝ, Model (2 * n))

theorem canonicalVectorBundle_finrank {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJsq : ∀ x v, J x (J x v) = -v) (x : M.Point) :
    Module.finrank ℂ (canonicalSubmodule (J x)) = 1 :=
  canonicalFiber_finrank_of_complexStructure (J x) (hJsq x)

set_option backward.isDefEq.respectTransparency false in
/-- The same native atlas is a complex vector bundle. Smoothness is still
real smoothness because the base is a real manifold. -/
theorem canonicalVectorBundle_complex {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := canonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : M.Point => canonicalSubmodule (J x)) := by
  dsimp only
  let a := canonicalVectorPrebundle M J hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    exact ⟨fun x _ => (c.lineCoordinateLinearMap x).isLinear⟩
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨c, rfl⟩ := he
    obtain ⟨d, rfl⟩ := he'
    let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
      ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ ℂ)
    have hc : ContinuousOn (fun x => L (c.lineTransition d x)) (c.domain ∩ d.domain) :=
      L.continuous.comp_continuousOn (c.smooth_lineTransition d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (c.lineTransitionMap_apply d hx q).symm
    · exact hx

end FsFltz.Geometry
