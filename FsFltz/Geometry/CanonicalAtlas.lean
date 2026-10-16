import FsFltz.Geometry.CanonicalLocalSection
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Native atlas for the squared canonical line

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The fiber is the actual complex subspace of
two-block canonical tensors. Local coframes come from the smooth almost
complex field, not from a supplied nonvanishing section. Evaluation in
their inverse frames gives the bundle coordinates; determinant
reconstruction gives the inverse. On overlaps, evaluation of one
determinant-square generator in the other inverse frame gives the smooth
complex-linear transition map.

The two-frame evaluation of the determinant-square generator is one.
Every canonical two-block tensor is its evaluation coefficient times that
generator. Thus evaluation and scalar multiplication are inverse complex
linear fiber maps. Smooth coframe inversion and the actual chart-transition
derivatives make both formulas smooth on every overlapping chart. A change
of fiber coordinates is multiplication by the evaluation of the first
generator in the second frame; its composition law follows by reconstructing
the same tensor in three frames. The fiber coordinates preserve the existing
tensor subspace topology. A native bundle section is smooth precisely when
its local scalar coefficients are smooth, and reconstruction identifies this
with the existing tensor-section predicate.

These constructions concern the smooth canonical bundle foundation. They
assert neither a global nonvanishing section nor geometric target existence.
The smooth unsquared canonical-line atlas and global smooth tensor-square
multiplication equivalence are constructed in `CanonicalLineAtlas` and
`CanonicalSquareBundle`. Smooth bundles for varying complex structures and
invariance under compatible changes of complex structure remain separate
foundations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry

/-- A complex coframe on one actual open manifold chart. Its defining
conditions concern the coframe; bundle and transition properties are proved. -/
structure CanonicalSquaredChart {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) where
  anchor : M.Point
  coordinates : Set (Model (2 * n))
  isOpen_coordinates : IsOpen coordinates
  coframe : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n
  smooth_coframe : ContDiffOn ℝ ∞ coframe coordinates
  invertible_coframe : ∀ y ∈ coordinates, (coframe y).IsInvertible
  intertwines_coframe : ∀ y ∈ coordinates, ∀ v,
    coframe y (almostComplexInChart M anchor J y v) =
      coordinateComplexStructure n (coframe y v)

namespace CanonicalSquaredChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : AlmostComplexField M}
variable (c : CanonicalSquaredChart M J)

def domain : Set M.Point := canonicalChartDomain M c.anchor c.coordinates

theorem isOpen_domain : IsOpen c.domain :=
  isOpen_canonicalChartDomain M c.anchor c.isOpen_coordinates

def tangentCoframe (x : M.Point) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  localCanonicalCoframe M c.anchor c.coframe x

def generator (x : M.Point) : SquaredCanonicalTensor n :=
  localCanonicalSquaredSection M c.anchor c.coframe x

def coefficient (x : M.Point) (s : SquaredCanonicalTensor n) : ℂ :=
  squaredCoframeCoefficient (c.tangentCoframe x) s

theorem tangentCoframe_invertible {x : M.Point} (hx : x ∈ c.domain) :
    (c.tangentCoframe x).IsInvertible :=
  (c.invertible_coframe _ hx.2).comp (chartTangentMap_isInvertible M c.anchor x hx.1)

theorem tangentCoframe_intertwines {x : M.Point} (hx : x ∈ c.domain)
    (v : Model (2 * n)) :
    c.tangentCoframe x (J x v) = coordinateComplexStructure n (c.tangentCoframe x v) :=
  localCanonicalCoframe_intertwines M c.anchor J c.coframe x hx.1
    (c.intertwines_coframe _ hx.2) v

theorem generator_canonical {x : M.Point} (hx : x ∈ c.domain) :
    IsSquaredCanonicalTensor (J x) (c.generator x) :=
  localCanonicalSquaredSection_canonical M c.anchor J c.coframe x hx.1
    (c.intertwines_coframe _ hx.2)

theorem generator_ne_zero {x : M.Point} (hx : x ∈ c.domain) : c.generator x ≠ 0 :=
  localCanonicalSquaredSection_ne_zero M c.anchor c.coframe x hx.1
    (c.invertible_coframe _ hx.2)

theorem smooth_generator : IsSmoothSquaredTensorSectionOn M c.generator c.domain :=
  isSmoothSquaredTensorSectionOn_localCanonicalSquaredSection M c.anchor
    c.isOpen_coordinates c.smooth_coframe

theorem coefficient_generator {x : M.Point} (hx : x ∈ c.domain) :
    c.coefficient x (c.generator x) = 1 :=
  coframeSquaredGenerator_frame _ (c.tangentCoframe_invertible hx)

theorem reconstruction {x : M.Point} (hx : x ∈ c.domain)
    (s : squaredCanonicalSubmodule (J x)) :
    s.val = c.coefficient x s.val • c.generator x :=
  squaredCoframe_reconstruction _ (c.tangentCoframe_invertible hx) _
    (c.tangentCoframe_intertwines hx) _ s.property

/-- The bundle coordinate is complex linear, including at points outside
the chart domain; only the inverse is restricted to the domain. -/
def coordinateLinearMap (x : M.Point) : squaredCanonicalSubmodule (J x) →ₗ[ℂ] ℂ where
  toFun s := c.coefficient x s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A genuine complex line coordinate equivalence on the open domain. -/
def coordinateEquiv (x : M.Point) (hx : x ∈ c.domain) :
    squaredCanonicalSubmodule (J x) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.coordinateLinearMap x
  invFun q := q • (⟨c.generator x, c.generator_canonical hx⟩ : squaredCanonicalSubmodule (J x))
  left_inv s := Subtype.ext (c.reconstruction hx s).symm
  right_inv q := by
    change c.coefficient x (q • c.generator x) = q
    change q * c.coefficient x (c.generator x) = q
    rw [c.coefficient_generator hx, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The fiber topology is the existing tensor subspace topology. The
coordinate equivalence is a homeomorphism for that topology. -/
def coordinateContinuousEquiv (x : M.Point) (hx : x ∈ c.domain) :
    squaredCanonicalSubmodule (J x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.coordinateEquiv x hx
  continuous_toFun := by
    change Continuous (fun s : squaredCanonicalSubmodule (J x) =>
      s.val (fun i => (c.tangentCoframe x).inverse (verticalFrame n (i.elim id id))))
    fun_prop
  continuous_invFun := by
    change Continuous (fun q : ℂ =>
      q • (⟨c.generator x, c.generator_canonical hx⟩ : squaredCanonicalSubmodule (J x)))
    exact continuous_id.smul continuous_const

theorem smooth_coefficient (s : M.Point → SquaredCanonicalTensor n)
    (hs : IsSmoothSquaredTensorSectionOn M s c.domain) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun x => c.coefficient x (s x)) c.domain :=
  contMDiffOn_localSquaredCoframeCoefficient M c.anchor c.isOpen_coordinates
    c.smooth_coframe c.invertible_coframe s hs

set_option backward.isDefEq.respectTransparency false in
/-- A restricted open domain permits coefficients of sections defined on
overlapping coframe neighborhoods. -/
theorem smooth_coefficient_on {U : Set M.Point} (hU : IsOpen U)
    (hUc : U ⊆ c.domain) (s : M.Point → SquaredCanonicalTensor n)
    (hs : IsSmoothSquaredTensorSectionOn M s U) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun x => c.coefficient x (s x)) U := by
  intro x hx
  let b := chartAt (Model (2 * n)) x
  let D := b.target ∩ b.symm ⁻¹' U
  have hD : IsOpen D := b.continuousOn_symm.isOpen_inter_preimage b.open_target hU
  have hxc : x ∈ c.domain := hUc hx
  have hsub : D ⊆ b.target ∩ b.symm ⁻¹' c.domain :=
    fun _ hy => ⟨hy.1, hUc hy.2⟩
  have hco := (contDiffOn_localCanonicalCoframe_inChart M c.anchor x
    c.isOpen_coordinates c.smooth_coframe).mono hsub
  have hinv : ∀ y ∈ D,
      ((c.tangentCoframe (b.symm y)).comp (M.inverseChartTangentMap x y)).IsInvertible :=
    fun y hy => (c.tangentCoframe_invertible (hUc hy.2)).comp
      (inverseChartTangentMap_isInvertible M x y hy.1)
  have hq := contDiffOn_squaredCoframeCoefficient hco hinv (hs x)
  have hq' : ContDiffOn ℝ ∞
      ((fun z => c.coefficient z (s z)) ∘ b.symm) D := by
    apply hq.congr
    intro y hy
    exact (squaredCoframeCoefficient_comp _ _
      (inverseChartTangentMap_isInvertible M x y hy.1) _).symm
  have hbx : b x ∈ D := ⟨b.map_source (mem_chart_source _ x), by
    simpa only [mem_preimage, b.left_inv (mem_chart_source _ x)] using hx⟩
  have hqM : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      ((fun z => c.coefficient z (s z)) ∘ b.symm) (b x) :=
    contMDiffAt_iff_contDiffAt.mpr (hq'.contDiffAt (hD.mem_nhds hbx))
  have hb : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ b x :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := x)).contMDiffAt
      (b.open_source.mem_nhds (mem_chart_source _ x))
  apply ((hqM.comp x hb).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [b.open_source.mem_nhds (mem_chart_source _ x)] with z hz
  exact (congrArg (fun z => c.coefficient z (s z)) (b.left_inv hz)).symm

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- Native local equivalence on the actual canonical tensor fibers. -/
def pretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x))) where
  toFun p := (p.proj, c.coefficient p.proj p.snd.val)
  invFun p := if hp : p.1 ∈ c.domain then
    ⟨p.1, (c.coordinateEquiv p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x))) ⁻¹' c.domain
  target := c.domain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.domain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : squaredCanonicalSubmodule (J x) =>
      (⟨x, t⟩ : TotalSpace ℂ (fun x => squaredCanonicalSubmodule (J x))))
      ((c.coordinateEquiv x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.coordinateEquiv p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_domain.prod isOpen_univ
  baseSet := c.domain
  open_baseSet := c.isOpen_domain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance pretrivialization_complexLinear : c.pretrivialization.IsLinear ℂ where
  linear x _ := (c.coordinateLinearMap x).isLinear

instance pretrivialization_realLinear : c.pretrivialization.IsLinear ℝ where
  linear x _ := ((c.coordinateLinearMap x).restrictScalars ℝ).isLinear

@[simp] theorem pretrivialization_apply (p : TotalSpace ℂ
    (fun x : M.Point => squaredCanonicalSubmodule (J x))) :
    c.pretrivialization p = (p.proj, c.coefficient p.proj p.snd.val) := rfl

theorem pretrivialization_symm {x : M.Point} (hx : x ∈ c.domain) (q : ℂ) :
    c.pretrivialization.symm x q = (c.coordinateEquiv x hx).symm q := by
  apply (c.coordinateEquiv x hx).injective
  rw [(c.coordinateEquiv x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.pretrivialization.apply_mk_symm hx q)

/-- The actual inverse fiber coordinate gives the required topology on
each fiber of the native prebundle. -/
theorem pretrivialization_isInducing {x : M.Point} (hx : x ∈ c.domain) :
    Topology.IsInducing (c.pretrivialization ∘ TotalSpace.mk x) := by
  have h := (c.coordinateContinuousEquiv x hx).toHomeomorph.isInducing
  have hc : Continuous (c.pretrivialization ∘ TotalSpace.mk x) :=
    continuous_const.prodMk (c.coordinateContinuousEquiv x hx).continuous
  exact Topology.IsInducing.of_comp hc continuous_snd h

/-- Change of scalar coordinates, derived from actual determinant tensors. -/
def transition (d : CanonicalSquaredChart M J) (x : M.Point) : ℂ :=
  d.coefficient x (c.generator x)

theorem smooth_transition (d : CanonicalSquaredChart M J) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (c.transition d) (c.domain ∩ d.domain) := by
  apply d.smooth_coefficient_on (c.isOpen_domain.inter d.isOpen_domain) inter_subset_right
  intro b
  exact (c.smooth_generator b).mono (fun _ hy => ⟨hy.1, hy.2.1⟩)

theorem transition_apply (d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    (d.pretrivialization ⟨x, c.pretrivialization.symm x q⟩).2 =
      c.transition d x * q := by
  rw [c.pretrivialization_symm hx.1]
  change d.coefficient x (q • c.generator x) = _
  change q * d.coefficient x (c.generator x) = _
  exact mul_comm _ _

end CanonicalSquaredChart

/-- Every smooth almost complex field supplies coframe charts covering the
manifold. No pointwise coframe, atlas, or nonvanishing section is an input. -/
theorem exists_canonicalSquaredChart {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : M.Point) :
    ∃ c : CanonicalSquaredChart M J, a ∈ c.domain := by
  obtain ⟨V, _, hV, haV, C, hC, hinv, hCJ, _⟩ :=
    exists_local_canonicalSquaredTrivialization M J hJ hJsq a
  exact ⟨⟨a, V, hV, C, hC, hinv, hCJ⟩, mem_chart_source _ a, haV⟩

/-- A field-selected chart at each point, obtained from the proved local
coframe construction. The atlas itself contains every valid coframe chart. -/
def canonicalSquaredChartAt {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : M.Point) : CanonicalSquaredChart M J :=
  (exists_canonicalSquaredChart M J hJ hJsq a).choose

theorem mem_canonicalSquaredChartAt_domain {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) (a : M.Point) :
    a ∈ (canonicalSquaredChartAt M J hJ hJsq a).domain :=
  (exists_canonicalSquaredChart M J hJ hJsq a).choose_spec

namespace CanonicalSquaredChart

variable {n : ℕ} {M : SmoothManifold (2 * n)} {J : AlmostComplexField M}

/-- Complex multiplication, regarded as a real continuous linear transition
map because the base manifold is real smooth. -/
def transitionMap (c d : CanonicalSquaredChart M J) (x : M.Point) : ℂ →L[ℝ] ℂ :=
  c.transition d x • ContinuousLinearMap.id ℝ ℂ

theorem smooth_transitionMap (c d : CanonicalSquaredChart M J) :
    ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap d) (c.domain ∩ d.domain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition d)

theorem transitionMap_apply (c d : CanonicalSquaredChart M J) {x : M.Point}
    (hx : x ∈ c.domain ∩ d.domain) (q : ℂ) :
    c.transitionMap d x q = (d.pretrivialization ⟨x, c.pretrivialization.symm x q⟩).2 :=
  (c.transition_apply d hx q).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exact reconstruction turns smooth scalar coordinates back into the
existing smooth tensor-section condition on an open coframe domain. -/
theorem smooth_tensor_iff_coefficient (c : CanonicalSquaredChart M J)
    (s : M.Point → SquaredCanonicalTensor n)
    (hs : ∀ x ∈ c.domain, IsSquaredCanonicalTensor (J x) (s x)) :
    IsSmoothSquaredTensorSectionOn M s c.domain ↔
      ContMDiffOn 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
        (fun x => c.coefficient x (s x)) c.domain := by
  refine ⟨c.smooth_coefficient s, ?_⟩
  intro hq b
  let e := chartAt (Model (2 * n)) b
  let D := e.target ∩ e.symm ⁻¹' c.domain
  have hD : IsOpen D :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target c.isOpen_domain
  have hscalar : ContDiffOn ℝ ∞
      ((fun x => c.coefficient x (s x)) ∘ e.symm) D := by
    intro y hy
    have hq' := hq.contMDiffAt (c.isOpen_domain.mem_nhds hy.2)
    have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e.symm y :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
        (e.open_target.mem_nhds hy.1)
    exact (hq'.comp y he).contDiffAt.contDiffWithinAt
  apply (hscalar.smul (c.smooth_generator b)).congr
  intro y hy
  have hr := c.reconstruction hy.2 ⟨s (e.symm y), hs _ hy.2⟩
  ext v
  exact congrArg (fun t : SquaredCanonicalTensor n =>
    t (fun i => M.inverseChartTangentMap b y (v i))) hr

end CanonicalSquaredChart

set_option backward.isDefEq.respectTransparency false in
/-- The native prebundle has the actual squared canonical tensor subspaces
as its fibers. All its topology and transition requirements are conclusions
of the coframe construction and determinant reconstruction. -/
def squaredCanonicalVectorPrebundle {n : ℕ} (M : SmoothManifold (2 * n))
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (hJsq : ∀ x v, J x (J x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x)) where
  pretrivializationAtlas := Set.range CanonicalSquaredChart.pretrivialization
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt a := (canonicalSquaredChartAt M J hJ hJsq a).pretrivialization
  mem_base_pretrivializationAt := mem_canonicalSquaredChartAt_domain M J hJ hJsq
  pretrivialization_mem_atlas a := ⟨canonicalSquaredChartAt M J hJ hJsq a, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, (c.smooth_transitionMap d).continuousOn,
      fun _ hx q => c.transitionMap_apply d hx q⟩
  totalSpaceMk_isInducing a :=
    (canonicalSquaredChartAt M J hJ hJsq a).pretrivialization_isInducing
      (mem_canonicalSquaredChartAt_domain M J hJ hJsq a)

/-- The constructed native vector bundle is smooth, with complex-linear
rank-one transition maps and real smooth base coordinates. -/
instance squaredCanonicalVectorPrebundle_isContMDiff {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    (squaredCanonicalVectorPrebundle M J hJ hJsq).IsContMDiff
      𝓘(ℝ, Model (2 * n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap d, c.smooth_transitionMap d,
      fun _ hx q => c.transitionMap_apply d hx q⟩

/-- The explicit topology and native bundle instances are available
together, so consumers do not need additional topological certificates. -/
theorem squaredCanonicalVectorBundle_smooth {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := squaredCanonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x))
      𝓘(ℝ, Model (2 * n)) :=
  (squaredCanonicalVectorPrebundle M J hJ hJsq).contMDiffVectorBundle
    𝓘(ℝ, Model (2 * n))

/-- Every fiber of the constructed bundle has complex dimension one. -/
theorem squaredCanonicalVectorBundle_finrank {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v)
    (x : M.Point) : Module.finrank ℂ (squaredCanonicalSubmodule (J x)) = 1 := by
  let c := canonicalSquaredChartAt M J hJ hJsq x
  rw [(c.coordinateEquiv x (mem_canonicalSquaredChartAt_domain M J hJ hJsq x)).finrank_eq]
  exact Module.finrank_self ℂ

set_option backward.isDefEq.respectTransparency false in
/-- The same native atlas is a complex vector bundle. Smoothness is still
real smoothness because the base is a real manifold. -/
theorem squaredCanonicalVectorBundle_complex {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v) :
    let a := squaredCanonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x)) := by
  dsimp only
  let a := squaredCanonicalVectorPrebundle M J hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    exact ⟨fun x _ => (c.coordinateLinearMap x).isLinear⟩
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

set_option backward.isDefEq.respectTransparency false in
/-- Existing canonical tensor smoothness implies native smoothness of the
section of the constructed line bundle. -/
theorem IsSmoothSquaredTensorSection.contMDiff_bundleSection {n : ℕ}
    {M : SmoothManifold (2 * n)} {J : AlmostComplexField M}
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v)
    (s : M.Point → SquaredCanonicalTensor n)
    (hcanonical : ∀ x, IsSquaredCanonicalTensor (J x) (s x))
    (hs : IsSmoothSquaredTensorSection M s) :
    let a := squaredCanonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff 𝓘(ℝ, Model (2 * n)) (𝓘(ℝ, Model (2 * n)).prod 𝓘(ℝ, ℂ)) ∞
      (fun x => (⟨x, ⟨s x, hcanonical x⟩⟩ :
        TotalSpace ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x)))) := by
  dsimp only
  let a := squaredCanonicalVectorPrebundle M J hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  intro x
  rw [Bundle.contMDiffAt_section]
  let c := canonicalSquaredChartAt M J hJ hJsq x
  have hx : x ∈ c.domain := mem_canonicalSquaredChartAt_domain M J hJ hJsq x
  exact (c.smooth_coefficient s (hs.isSmoothOn c.domain)).contMDiffAt
    (c.isOpen_domain.mem_nhds hx)

set_option backward.isDefEq.respectTransparency false in
/-- The existing canonical-section predicate is equivalent to native
smoothness for the constructed bundle topology and atlas. The reverse
direction uses determinant reconstruction on a genuine neighborhood. -/
theorem isSmoothSquaredTensorSection_iff_contMDiff_bundleSection {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (hJsq : ∀ x v, J x (J x v) = -v)
    (s : M.Point → SquaredCanonicalTensor n)
    (hcanonical : ∀ x, IsSquaredCanonicalTensor (J x) (s x)) :
    let a := squaredCanonicalVectorPrebundle M J hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    IsSmoothSquaredTensorSection M s ↔
      ContMDiff 𝓘(ℝ, Model (2 * n)) (𝓘(ℝ, Model (2 * n)).prod 𝓘(ℝ, ℂ)) ∞
        (fun x => (⟨x, ⟨s x, hcanonical x⟩⟩ :
          TotalSpace ℂ (fun x : M.Point => squaredCanonicalSubmodule (J x)))) := by
  dsimp only
  let a := squaredCanonicalVectorPrebundle M J hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨fun hs => hs.contMDiff_bundleSection hJ hJsq s hcanonical, ?_⟩
  intro hn b y hy
  let e := chartAt (Model (2 * n)) b
  let x := e.symm y
  let c := canonicalSquaredChartAt M J hJ hJsq x
  have hx : x ∈ c.domain := mem_canonicalSquaredChartAt_domain M J hJ hJsq x
  have hq : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun z => c.coefficient z (s z)) x := by
    exact (Bundle.contMDiffAt_section x).mp (hn x)
  have he : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ e.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2 * n))) (x := b)).contMDiffAt
      (e.open_target.mem_nhds hy)
  have hscalar := (hq.comp y he).contDiffAt
  let D := e.target ∩ e.symm ⁻¹' c.domain
  have hD : IsOpen D :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target c.isOpen_domain
  have hyD : y ∈ D := ⟨hy, hx⟩
  have hg := (c.smooth_generator b).contDiffAt (hD.mem_nhds hyD)
  apply ((hscalar.smul hg).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hD.mem_nhds hyD] with z hz
  have hr := c.reconstruction hz.2 ⟨s (e.symm z), hcanonical _⟩
  ext v
  exact congrArg (fun t : SquaredCanonicalTensor n =>
    t (fun i => M.inverseChartTangentMap b z (v i))) hr

namespace MaslovRepresentative

/-- The actual section carried by a Maslov representative is a native
smooth section of the constructed canonical-square line bundle. -/
theorem contMDiff_canonicalSquaredBundleSection {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s : MaslovRepresentative M eta) :
    let a := squaredCanonicalVectorPrebundle M s.J s.compatible.1 s.compatible.2.1
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff 𝓘(ℝ, Model (2 * n)) (𝓘(ℝ, Model (2 * n)).prod 𝓘(ℝ, ℂ)) ∞
      (fun x => (⟨x, ⟨s.tensor x, s.canonical x⟩⟩ :
        TotalSpace ℂ (fun x : M.Point => squaredCanonicalSubmodule (s.J x)))) :=
  (isSmoothSquaredTensorSection_iff_contMDiff_bundleSection M s.J
    s.compatible.1 s.compatible.2.1 s.tensor s.canonical).mp s.smooth

end MaslovRepresentative

end FsFltz.Geometry
