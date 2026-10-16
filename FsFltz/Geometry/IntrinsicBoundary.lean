import FsFltz.Geometry.BoundaryIntrinsicEquiv

/-!
# Boundary atlas of an arbitrary intrinsic manifold with boundary

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Here the input is only a native smooth half-space manifold.
No boundary presentation, ambient extension, collar, or defining function
is supplied. Boundary charts are restrictions of its own atlas to the
zero-coordinate hyperplane. Their smooth transitions come from the native
smooth transition maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace IntrinsicBoundary

/-- The boundary hyperplane regarded as a subset of the half-space model. -/
def halfSpaceInsert (k : ℕ) (v : Model k) : EuclideanHalfSpace (k + 1) :=
  ⟨boundaryInsert k v, by simp⟩

@[simp] theorem halfSpaceInsert_val {k : ℕ} (v : Model k) :
    (halfSpaceInsert k v).val = boundaryInsert k v := rfl

theorem contMDiff_halfSpaceInsert (k : ℕ) :
    ContMDiff 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) ∞ (halfSpaceInsert k) := by
  intro v
  apply contMDiffAt_iff.mpr
  refine ⟨(boundaryInsert k).continuous.subtype_mk _ |>.continuousAt, ?_⟩
  simpa [halfSpaceInsert, extChartAt, modelWithCornersEuclideanHalfSpace, Function.comp_def,
    boundaryInsert_zero] using (boundaryInsert k).contDiff.contDiffAt.contDiffWithinAt

/-- Delete the zero first coordinate of the half-space boundary. -/
def halfSpaceBoundaryHomeomorph (k : ℕ) :
    {v : EuclideanHalfSpace (k + 1) // v.val 0 = 0} ≃ₜ Model k where
  toFun v := boundaryDrop k v.val.val
  invFun v := ⟨halfSpaceInsert k v, by simp⟩
  left_inv v := Subtype.ext (Subtype.ext (boundaryInsert_drop v.val.val v.property))
  right_inv := boundaryDrop_insert
  continuous_toFun := (boundaryDrop k).continuous.comp continuous_subtype_val.subtype_val
  continuous_invFun := ((boundaryInsert k).continuous.subtype_mk _).subtype_mk _

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The literal native intrinsic boundary, equipped with its subspace topology. -/
abbrev Point (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] := (𝓡∂ (k + 1)).boundary M

/-- Boundary points have zero normal coordinate in every native atlas chart. -/
theorem isBoundaryPoint_iff_chart_zero
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source) :
    (𝓡∂ (k + 1)).IsBoundaryPoint x ↔ (e x).val 0 = 0 := by
  have hi : (𝓡∂ (k + 1)).IsInteriorPoint x ↔
      (e x).val ∈ interior (range (𝓡∂ (k + 1))) := by
    rw [(𝓡∂ (k + 1)).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) he hx]
    exact ⟨fun h => e.interior_extend_target_subset_interior_range (I := 𝓡∂ (k + 1)) h,
      e.mem_interior_extend_target (I := 𝓡∂ (k + 1)) (e.map_source hx)⟩
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi]
  rw [modelWithCornersEuclideanHalfSpace_toFun, range_euclideanHalfSpace]
  rw [interior_halfSpace]
  exact ⟨fun h => le_antisymm (le_of_not_gt h) (e x).property,
    fun h => by simp [h]⟩

/-- A boundary chart is a restriction of an actual member of the native atlas. -/
structure Chart (k : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] where
  ambient : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))
  mem_atlas : ambient ∈ atlas (EuclideanHalfSpace (k + 1)) M
  chart : OpenPartialHomeomorph (Point k M) (Model k)
  source_eq : chart.source = Subtype.val ⁻¹' ambient.source
  target_eq : chart.target = halfSpaceInsert k ⁻¹' ambient.target
  toFun_eq : ∀ y ∈ chart.source, chart y = boundaryDrop k (ambient y.val).val
  invFun_eq : ∀ v ∈ chart.target, (chart.symm v).val = ambient.symm (halfSpaceInsert k v)

/-- Every intrinsic boundary point has a native restricted boundary chart. -/
theorem exists_chart (x : Point k M) : ∃ c : Chart k M, x ∈ c.chart.source := by
  let e := chartAt (EuclideanHalfSpace (k + 1)) x.val
  have himage : e.IsImage ((𝓡∂ (k + 1)).boundary M)
      {v : EuclideanHalfSpace (k + 1) | v.val 0 = 0} := by
    intro y hy
    exact (isBoundaryPoint_iff_chart_zero (chart_mem_atlas _ x.val) hy).symm
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ := exists_openPartialHomeomorph_subtypes e himage x
    ⟨halfSpaceInsert k 0, by simp⟩
  let q := r.trans (halfSpaceBoundaryHomeomorph k).toOpenPartialHomeomorph
  refine ⟨⟨e, chart_mem_atlas _ x.val, q, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change r.source ∩ r ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    exact hrs
  · change univ ∩ (halfSpaceBoundaryHomeomorph k).symm ⁻¹' r.target = _
    rw [univ_inter, hrt]
    rfl
  · intro y hy
    change boundaryDrop k (r y).val.val = boundaryDrop k (e y.val).val
    rw [hrf y hy.1]
  · intro v hv
    change (r.symm ((halfSpaceBoundaryHomeomorph k).symm v)).val = _
    exact hrg _ hv.2
  · change x ∈ r.source ∩ r ⁻¹' univ
    rw [hrs]
    exact ⟨mem_chart_source _ x.val, mem_univ _⟩

@[simp] theorem model_symm_boundaryInsert (v : Model k) :
    (𝓡∂ (k + 1)).symm (boundaryInsert k v) = halfSpaceInsert k v :=
  (𝓡∂ (k + 1)).left_inv (halfSpaceInsert k v)

/-- Boundary transitions are the native extended transitions precomposed
with hyperplane insertion and postcomposed with coordinate deletion. -/
theorem Chart.contDiffOn_transition (c c' : Chart k M) :
    ContDiffOn ℝ ∞ (c.chart.symm.trans c'.chart) (c.chart.symm.trans c'.chart).source := by
  let t := ModelWithCorners.extendCoordChange (I := 𝓡∂ (k + 1)) c.ambient c'.ambient
  let S := (c.chart.symm.trans c'.chart).source
  have ht : ContDiffOn ℝ ∞ t t.source :=
    ModelWithCorners.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas c.mem_atlas)
      (IsManifold.subset_maximalAtlas c'.mem_atlas)
  have hsub : MapsTo (boundaryInsert k) S t.source := by
    intro v hv
    change v ∈ c.chart.target ∧ c.chart.symm v ∈ c'.chart.source at hv
    have he : halfSpaceInsert k v ∈ c.ambient.target := by
      have hct := hv.1
      rwa [c.target_eq] at hct
    have he' : c.ambient.symm (halfSpaceInsert k v) ∈ c'.ambient.source := by
      have hcs := hv.2
      rw [c'.source_eq] at hcs
      change (c.chart.symm v).val ∈ c'.ambient.source at hcs
      rwa [c.invFun_eq v hv.1] at hcs
    rw [ModelWithCorners.extendCoordChange_source]
    exact ⟨halfSpaceInsert k v, ⟨he, he'⟩, rfl⟩
  apply ((boundaryDrop k).contDiff.comp_contDiffOn
    (ht.comp (boundaryInsert k).contDiff.contDiffOn hsub)).congr
  intro v hv
  change c'.chart (c.chart.symm v) =
    boundaryDrop k (c'.ambient (c.ambient.symm ((𝓡∂ (k + 1)).symm (boundaryInsert k v)))).val
  rw [model_symm_boundaryInsert, c'.toFun_eq (c.chart.symm v) hv.2, c.invFun_eq v hv.1]

/-- A preferred chart obtained by restricting the native atlas. -/
def chartAt (x : Point k M) : Chart k M := (exists_chart x).choose

theorem mem_chartAt_source (x : Point k M) : x ∈ (chartAt x).chart.source :=
  (exists_chart x).choose_spec

/-- Native boundary atlas, constructed on the literal intrinsic boundary. -/
instance chartedSpace : ChartedSpace (Model k) (Point k M) where
  atlas := range (fun c : Chart k M => c.chart)
  chartAt x := (chartAt x).chart
  mem_chart_source := mem_chartAt_source
  chart_mem_atlas x := ⟨chartAt x, rfl⟩

/-- The native boundary atlas has smooth Euclidean transitions. -/
instance isManifold : IsManifold 𝓘(ℝ, Model k) ∞ (Point k M) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨c, rfl⟩ ⟨c', rfl⟩
  simpa using c.contDiffOn_transition c'

/-- The intrinsic boundary inclusion is smooth into the half-space manifold. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) ∞ (Subtype.val : Point k M → M) := by
  intro x
  apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source (Model k) x)).mpr
  let c := chartAt x
  have hc : c.chart x ∈ c.chart.target := c.chart.map_source (mem_chartAt_source x)
  have he : halfSpaceInsert k (c.chart x) ∈ c.ambient.target := by
    rwa [c.target_eq] at hc
  have hs := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓡∂ (k + 1)) (n := ∞) (IsManifold.subset_maximalAtlas c.mem_atlas) he
  apply (hs.comp (c.chart x) (contMDiff_halfSpaceInsert k).contMDiffAt).contMDiffWithinAt
    |>.congr_of_eventuallyEq_of_mem _ (by simp)
  have ht : ∀ᶠ v in 𝓝 (c.chart x), v ∈ c.chart.target := c.chart.open_target.mem_nhds hc
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with v hv
  exact c.invFun_eq v hv

/-- The inclusion differential is injective: its composition with a
native boundary coordinate map is the identity differential. -/
theorem injective_mfderiv_val (x : Point k M) :
    Function.Injective (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
      (Subtype.val : Point k M → M) x) := by
  let c := chartAt x
  have hcs : x ∈ c.chart.source := mem_chartAt_source x
  have hes : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
  let g : M → Model k := boundaryDrop k ∘ c.ambient.extend (𝓡∂ (k + 1))
  have hg : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model k) ∞ g x.val :=
    (boundaryDrop k).contMDiff.contMDiffAt.comp x.val
      (c.ambient.contMDiffAt_extend (IsManifold.subset_maximalAtlas c.mem_atlas) hes)
  have heq : (extChartAt 𝓘(ℝ, Model k) x : Point k M → Model k) =ᶠ[𝓝 x]
      g ∘ Subtype.val := by
    filter_upwards [c.chart.open_source.mem_nhds hcs] with y hy
    exact c.toFun_eq y hy
  have hd := mfderiv_comp (f := (Subtype.val : Point k M → M)) (g := g) x
    (hg.mdifferentiableAt (by simp)) (contMDiff_val.mdifferentiableAt (by simp))
  have hi := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model k)) (x := x)
  rw [heq.mfderiv_eq, hd] at hi
  have hi' (v : TangentSpace 𝓘(ℝ, Model k) x) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model k) g x.val
        (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) Subtype.val x v) = v :=
    congrArg (fun A => A v) hi
  intro v w hvw
  have h := congrArg (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model k) g x.val) hvw
  exact (hi' v).symm.trans (h.trans (hi' w))

/-- The intrinsic boundary of a compact half-space manifold is compact. -/
instance compactSpace [CompactSpace M] : CompactSpace (Point k M) := by
  exact isCompact_iff_compactSpace.mp
    ((𝓡∂ (k + 1)).isClosed_boundary (n := ∞) (by simp)).isCompact

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The native inclusion is a topological embedding for the inherited topology. -/
theorem isEmbedding_val : Topology.IsEmbedding (Subtype.val : Point k M → M) :=
  Topology.IsEmbedding.subtypeVal

/-- The boundaryless smooth manifold constructed from the native atlas.
Hausdorffness and second countability are inherited from the input manifold. -/
abbrev smoothManifold (k : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
    [T2Space M] [SecondCountableTopology M] : SmoothManifold k where
  Point := Point k M
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

end IntrinsicBoundary
end FsFltz.Geometry
