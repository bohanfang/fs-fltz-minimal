import FsFltz.Geometry.IntrinsicBoundary

/-!
# The boundaryless native interior atlas

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The native interior atlas is constructed from the smooth
half-space atlas of the input manifold. No interior atlas is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace IntrinsicInterior

/-- Strictly positive half-space coordinates, viewed in the full Euclidean model. -/
def positiveModel (k : ℕ) : TopologicalSpace.Opens (Model (k + 1)) :=
  ⟨{v | 0 < v 0}, isOpen_lt continuous_const
    (PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) 0)⟩

theorem positiveModel_nonempty (k : ℕ) : Nonempty (positiveModel k) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [positiveModel]⟩⟩

/-- Flatten the two subtypes of a strictly positive half-space point. -/
def positiveHalfSpaceHomeomorph (k : ℕ) :
    {v : EuclideanHalfSpace (k + 1) // 0 < v.val 0} ≃ₜ positiveModel k where
  toFun v := ⟨v.val.val, v.property⟩
  invFun v := ⟨⟨v.val, v.property.le⟩, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The positive portion of the half-space is an open Euclidean coordinate chart. -/
def positiveHalfSpaceChart (k : ℕ) :
    OpenPartialHomeomorph {v : EuclideanHalfSpace (k + 1) // 0 < v.val 0}
      (Model (k + 1)) :=
  (positiveHalfSpaceHomeomorph k).toOpenPartialHomeomorph.trans
    ((positiveModel k).openPartialHomeomorphSubtypeCoe (positiveModel_nonempty k))

@[simp] theorem positiveHalfSpaceChart_source (k : ℕ) :
    (positiveHalfSpaceChart k).source = univ := by
  simp [positiveHalfSpaceChart]

@[simp] theorem positiveHalfSpaceChart_apply {k : ℕ}
    (v : {v : EuclideanHalfSpace (k + 1) // 0 < v.val 0}) :
    positiveHalfSpaceChart k v = v.val.val := rfl

@[simp] theorem positiveHalfSpaceChart_target (k : ℕ) :
    (positiveHalfSpaceChart k).target = {v | 0 < v 0} := by
  simp [positiveHalfSpaceChart, positiveModel]

theorem positiveHalfSpaceChart_symm_val {k : ℕ} {v : Model (k + 1)} (hv : 0 < v 0) :
    ((positiveHalfSpaceChart k).symm v).val = (𝓡∂ (k + 1)).symm v := by
  have h := (positiveHalfSpaceChart k).right_inv (by simpa using hv)
  change ((positiveHalfSpaceChart k).symm v).val.val = v at h
  calc
    ((positiveHalfSpaceChart k).symm v).val =
        (𝓡∂ (k + 1)).symm (((positiveHalfSpaceChart k).symm v).val.val) :=
      ((𝓡∂ (k + 1)).left_inv _).symm
    _ = (𝓡∂ (k + 1)).symm v := congrArg (𝓡∂ (k + 1)).symm h

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The literal native intrinsic interior, with its inherited topology. -/
abbrev Point (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] := (𝓡∂ (k + 1)).interior M

theorem isOpen_interior : IsOpen ((𝓡∂ (k + 1)).interior M) :=
  (𝓡∂ (k + 1)).isOpen_interior (n := ∞) (by simp)

/-- The interior inclusion is an open embedding for the inherited topology. -/
theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Subtype.val : Point k M → M) :=
  isOpen_interior.isOpenEmbedding_subtypeVal

/-- Native interior points have strictly positive coordinate in every native chart. -/
theorem isInteriorPoint_iff_chart_pos
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source) :
    (𝓡∂ (k + 1)).IsInteriorPoint x ↔ 0 < (e x).val 0 := by
  rw [(𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint x,
    IntrinsicBoundary.isBoundaryPoint_iff_chart_zero he hx]
  exact ⟨fun h => lt_of_le_of_ne (e x).property (Ne.symm h),
    fun h => ne_of_gt h⟩

/-- An interior chart is a restriction of an actual member of the native atlas. -/
structure Chart (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] where
  ambient : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))
  mem_atlas : ambient ∈ atlas (EuclideanHalfSpace (k + 1)) M
  chart : OpenPartialHomeomorph (Point k M) (Model (k + 1))
  source_eq : chart.source = Subtype.val ⁻¹' ambient.source
  target_eq : chart.target = {v | 0 < v 0 ∧ (𝓡∂ (k + 1)).symm v ∈ ambient.target}
  toFun_eq : ∀ y ∈ chart.source, chart y = (ambient y.val).val
  invFun_eq : ∀ v ∈ chart.target, (chart.symm v).val = ambient.symm ((𝓡∂ (k + 1)).symm v)

/-- Every intrinsic interior point has a native restricted Euclidean chart. -/
theorem exists_chart (x : Point k M) : ∃ c : Chart k M, x ∈ c.chart.source := by
  let e := _root_.chartAt (EuclideanHalfSpace (k + 1)) x.val
  have himage : e.IsImage ((𝓡∂ (k + 1)).interior M)
      {v : EuclideanHalfSpace (k + 1) | 0 < v.val 0} := by
    intro y hy
    exact (isInteriorPoint_iff_chart_pos (chart_mem_atlas _ x.val) hy).symm
  let z : {v : EuclideanHalfSpace (k + 1) // 0 < v.val 0} :=
    (positiveHalfSpaceHomeomorph k).symm (Classical.choice (positiveModel_nonempty k))
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ := exists_openPartialHomeomorph_subtypes e himage x z
  let q := r.trans (positiveHalfSpaceChart k)
  refine ⟨⟨e, chart_mem_atlas _ x.val, q, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change r.source ∩ r ⁻¹' (positiveHalfSpaceChart k).source = _
    rw [positiveHalfSpaceChart_source, preimage_univ, inter_univ]
    exact hrs
  · ext v
    change v ∈ (positiveHalfSpaceChart k).target ∧
      (positiveHalfSpaceChart k).symm v ∈ r.target ↔ _
    rw [positiveHalfSpaceChart_target, hrt]
    exact ⟨fun h => ⟨h.1, by simpa [positiveHalfSpaceChart_symm_val h.1] using h.2⟩,
      fun h => ⟨h.1, by simpa [positiveHalfSpaceChart_symm_val h.1] using h.2⟩⟩
  · intro y hy
    change (r y).val.val = (e y.val).val
    rw [hrf y hy.1]
  · intro v hv
    change (r.symm ((positiveHalfSpaceChart k).symm v)).val = _
    rw [hrg _ hv.2]
    exact congrArg e.symm (positiveHalfSpaceChart_symm_val (by simpa using hv.1))
  · change x ∈ r.source ∩ r ⁻¹' (positiveHalfSpaceChart k).source
    rw [hrs, positiveHalfSpaceChart_source]
    exact ⟨mem_chart_source _ x.val, mem_univ _⟩

/-- Interior transitions are restrictions of the native extended transitions. -/
theorem Chart.contDiffOn_transition (c c' : Chart k M) :
    ContDiffOn ℝ ∞ (c.chart.symm.trans c'.chart) (c.chart.symm.trans c'.chart).source := by
  let t := ModelWithCorners.extendCoordChange (I := 𝓡∂ (k + 1)) c.ambient c'.ambient
  let S := (c.chart.symm.trans c'.chart).source
  have ht : ContDiffOn ℝ ∞ t t.source :=
    ModelWithCorners.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas c.mem_atlas)
      (IsManifold.subset_maximalAtlas c'.mem_atlas)
  have hsub : S ⊆ t.source := by
    intro v hv
    change v ∈ c.chart.target ∧ c.chart.symm v ∈ c'.chart.source at hv
    have hct := hv.1
    rw [c.target_eq] at hct
    have hcs := hv.2
    rw [c'.source_eq] at hcs
    change (c.chart.symm v).val ∈ c'.ambient.source at hcs
    rw [c.invFun_eq v hv.1] at hcs
    rw [ModelWithCorners.extendCoordChange_source]
    refine ⟨(𝓡∂ (k + 1)).symm v, ⟨hct.2, hcs⟩, ?_⟩
    exact (𝓡∂ (k + 1)).right_inv ⟨⟨v, hct.1.le⟩, rfl⟩
  apply (ht.mono hsub).congr
  intro v hv
  change c'.chart (c.chart.symm v) =
    (c'.ambient (c.ambient.symm ((𝓡∂ (k + 1)).symm v))).val
  rw [c'.toFun_eq (c.chart.symm v) hv.2, c.invFun_eq v hv.1]

/-- A preferred Euclidean chart obtained by restricting the native atlas. -/
def chartAt (x : Point k M) : Chart k M := (exists_chart x).choose

theorem mem_chartAt_source (x : Point k M) : x ∈ (chartAt x).chart.source :=
  (exists_chart x).choose_spec

/-- The native interior atlas, constructed on the literal interior subset. -/
instance chartedSpace : ChartedSpace (Model (k + 1)) (Point k M) where
  atlas := range (fun c : Chart k M => c.chart)
  chartAt x := (chartAt x).chart
  mem_chart_source := mem_chartAt_source
  chart_mem_atlas x := ⟨chartAt x, rfl⟩

/-- The native interior atlas has smooth Euclidean transitions. -/
instance isManifold : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Point k M) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨c, rfl⟩ ⟨c', rfl⟩
  simpa using c.contDiffOn_transition c'

/-- The intrinsic interior inclusion is smooth into the native half-space manifold. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) ∞ (Subtype.val : Point k M → M) := by
  intro x
  apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source (Model (k + 1)) x)).mpr
  let c := chartAt x
  have hc : c.chart x ∈ c.chart.target := c.chart.map_source (mem_chartAt_source x)
  have hct := hc
  rw [c.target_eq] at hct
  have hr : range (𝓡∂ (k + 1)) ∈ 𝓝 (c.chart x) := by
    apply mem_of_superset ((positiveModel k).isOpen.mem_nhds hct.1)
    intro v hv
    exact ⟨⟨v, hv.le⟩, rfl⟩
  have hs := contMDiffOn_extend_symm (I := 𝓡∂ (k + 1)) (n := ∞)
    (IsManifold.subset_maximalAtlas c.mem_atlas)
  have hright : (𝓡∂ (k + 1)) ((𝓡∂ (k + 1)).symm (c.chart x)) = c.chart x :=
    (𝓡∂ (k + 1)).right_inv ⟨⟨c.chart x, hct.1.le⟩, rfl⟩
  have hne : (𝓡∂ (k + 1)) '' c.ambient.target ∈ 𝓝 (c.chart x) := by
    have hpos : (𝓡∂ (k + 1)) ((𝓡∂ (k + 1)).symm (c.chart x)) ∈
        interior (range (𝓡∂ (k + 1))) := by
      rw [hright]
      exact mem_interior_iff_mem_nhds.mpr hr
    have h := c.ambient.mem_interior_extend_target hct.2 hpos
    rw [hright] at h
    rw [c.ambient.extend_target'] at h
    exact mem_interior_iff_mem_nhds.mp h
  apply (hs.contMDiffAt hne).contMDiffWithinAt
    |>.congr_of_eventuallyEq_of_mem _ (by simp)
  have ht : ∀ᶠ v in 𝓝 (c.chart x), v ∈ c.chart.target := c.chart.open_target.mem_nhds hc
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with v hv
  exact c.invFun_eq v hv

section SmoothMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Smoothness into the native interior is equivalent to smoothness after inclusion,
also on an arbitrary source subset. -/
theorem contMDiffWithinAt_iff_val {f : X → Point k M} {s : Set X} {x : X} :
    ContMDiffWithinAt I 𝓘(ℝ, Model (k + 1)) ∞ f s x ↔
      ContMDiffWithinAt I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) s x := by
  constructor
  · intro hf
    exact contMDiff_val.contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    have hc : ContinuousWithinAt f s x :=
      Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hf.continuousWithinAt
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨hc, ?_⟩
    let c := chartAt (f x)
    have hcs : f x ∈ c.chart.source := mem_chartAt_source (f x)
    have hes : (f x).val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
    have he := c.ambient.contMDiffAt_extend (I := 𝓡∂ (k + 1)) (n := ∞)
      (IsManifold.subset_maximalAtlas c.mem_atlas) hes
    apply (he.comp_contMDiffWithinAt x hf).congr_of_eventuallyEq
      _ (c.toFun_eq (f x) (mem_chartAt_source (f x)))
    filter_upwards [hc.eventually_mem (c.chart.open_source.mem_nhds hcs)] with y hy
    exact c.toFun_eq (f y) hy

/-- Smoothness into the literal native interior can be checked in the original manifold. -/
theorem contMDiffAt_iff_val {f : X → Point k M} {x : X} :
    ContMDiffAt I 𝓘(ℝ, Model (k + 1)) ∞ f x ↔
      ContMDiffAt I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) x :=
  contMDiffWithinAt_iff_val

theorem contMDiffOn_iff_val {f : X → Point k M} {s : Set X} :
    ContMDiffOn I 𝓘(ℝ, Model (k + 1)) ∞ f s ↔
      ContMDiffOn I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) s := by
  exact forall₂_congr (fun _ _ => contMDiffWithinAt_iff_val)

theorem contMDiff_iff_val {f : X → Point k M} :
    ContMDiff I 𝓘(ℝ, Model (k + 1)) ∞ f ↔
      ContMDiff I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) := by
  exact forall_congr' (fun _ => contMDiffAt_iff_val)

end SmoothMaps

/-- The interior inclusion has injective differential, as its expression in native
interior and ambient coordinates is the identity. -/
theorem injective_mfderiv_val (x : Point k M) :
    Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
      (Subtype.val : Point k M → M) x) := by
  let c := chartAt x
  have hcs : x ∈ c.chart.source := mem_chartAt_source x
  have hes : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
  let g : M → Model (k + 1) := c.ambient.extend (𝓡∂ (k + 1))
  have hg : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g x.val :=
    c.ambient.contMDiffAt_extend (IsManifold.subset_maximalAtlas c.mem_atlas) hes
  have heq : (extChartAt 𝓘(ℝ, Model (k + 1)) x : Point k M → Model (k + 1)) =ᶠ[𝓝 x]
      g ∘ Subtype.val := by
    filter_upwards [c.chart.open_source.mem_nhds hcs] with y hy
    exact c.toFun_eq y hy
  have hd := mfderiv_comp (f := (Subtype.val : Point k M → M)) (g := g) x
    (hg.mdifferentiableAt (by simp)) (contMDiff_val.mdifferentiableAt (by simp))
  have hi := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model (k + 1))) (x := x)
  rw [heq.mfderiv_eq, hd] at hi
  have hi' (v : TangentSpace 𝓘(ℝ, Model (k + 1)) x) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) g x.val
        (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1)) Subtype.val x v) = v :=
    congrArg (fun A => A v) hi
  intro v w hvw
  have h := congrArg (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) g x.val) hvw
  exact (hi' v).symm.trans (h.trans (hi' w))

/-- The interior inclusion is an isomorphism on tangent spaces of equal finite dimension. -/
theorem bijective_mfderiv_val (x : Point k M) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
      (Subtype.val : Point k M → M) x) := by
  have hi := injective_mfderiv_val x
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The boundaryless smooth manifold constructed from the native interior atlas.
Hausdorffness and second countability are inherited from the input manifold. -/
abbrev smoothManifold (k : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
    [T2Space M] [SecondCountableTopology M] : SmoothManifold (k + 1) where
  Point := Point k M
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

end IntrinsicInterior
end FsFltz.Geometry
