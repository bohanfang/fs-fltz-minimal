import FsFltz.Geometry.BoundaryCharts

/-!
# Intrinsic half-space atlases of regular-sublevel domains

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. An ambient smooth extension supplies local charts of the
domain into the Euclidean half-space. At frontier points these are the
straightened defining-function charts; at interior points an ambient chart
is translated and restricted into the open half-space. Coordinate changes
extend to the ambient smooth coordinate changes, hence define a native
smooth manifold with boundary on the actual domain subtype.

This constructs an intrinsic atlas from a regular-sublevel presentation.
It does not construct a global extension of an arbitrary intrinsic domain,
a Liouville collar, or a completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
namespace CompactDomain

/-- A half-space chart with specified smooth ambient extensions in both
directions and its actual boundary locus. -/
structure ExtendedHalfSpaceChart {d : ℕ} [NeZero d] (D : CompactDomain d) where
  chart : OpenPartialHomeomorph D.Point (EuclideanHalfSpace d)
  extension : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
    D.extension.Point (Model d) ∞
  source_eq : chart.source = Subtype.val ⁻¹' extension.source
  target_eq : chart.target = Subtype.val ⁻¹' extension.target
  toFun_eq : ∀ y ∈ chart.source, (chart y).val = extension y.val
  invFun_eq : ∀ v ∈ chart.target, (chart.symm v).val = extension.invFun v.val
  frontier_iff : ∀ y ∈ chart.source, y.val ∈ frontier D.carrier ↔ (chart y).val 0 = 0

/-- Regular boundary equations produce charts of the actual domain with
smooth ambient extensions; no atlas is an input. -/
theorem exists_extendedHalfSpaceChart_at_boundary {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) (hx : x.val ∈ frontier D.carrier) :
    ∃ c : ExtendedHalfSpaceChart D, x ∈ c.chart.source := by
  obtain ⟨e, r, hxe, _, hrs, hrt, hrf, hrg, _, hb⟩ :=
    (D.defining x.val hx).exists_halfspace_chart x.property
  exact ⟨⟨r, e, hrs, hrt, hrf, hrg, hb⟩, by rw [hrs]; exact hxe⟩

/-- Interior points admit charts into the open half-space, with the same
ambient extension properties as the boundary charts. -/
theorem exists_extendedHalfSpaceChart_at_interior {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) (hx : x.val ∈ interior D.carrier) :
    ∃ c : ExtendedHalfSpaceChart D, x ∈ c.chart.source := by
  let c := chartAt (Model d) x.val
  let b : Model d := PiLp.single 2 0 (1 - (c x.val) 0)
  let a : Model d ≃ₘ[ℝ] Model d :=
    { (Homeomorph.addRight b).toEquiv with
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let c' : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      D.extension.Point (Model d) ∞ :=
    { c.toPartialEquiv with
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let e₀ := c'.trans a.toPartialDiffeomorph
  let P : Set (Model d) := {v | 0 < v 0}
  have hP : IsOpen P := isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)
  let U := interior D.carrier ∩ e₀ ⁻¹' P
  have hU : IsOpen (e₀.source ∩ U) := by
    have h := e₀.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
      e₀.open_source hP
    convert h.inter isOpen_interior using 1
    ext y
    simp only [U, mem_inter_iff, mem_preimage]
    tauto
  let r₀ := e₀.toOpenPartialHomeomorph.restrOpen (e₀.source ∩ U) hU
  let e : PartialDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      D.extension.Point (Model d) ∞ :=
    { r₀.toPartialEquiv with
      open_source := r₀.open_source
      open_target := r₀.open_target
      contMDiffOn_toFun := e₀.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := e₀.contMDiffOn_invFun.mono inter_subset_left }
  have hpos : ∀ y ∈ e.source, 0 < (e y) 0 := fun y hy => hy.2.2.2
  have hinside : e.source ⊆ interior D.carrier := fun y hy => hy.2.2.1
  have hxe : x.val ∈ e.source := by
    refine ⟨⟨mem_chart_source _ _, mem_univ _⟩, ⟨⟨mem_chart_source _ _, mem_univ _⟩,
      hx, ?_⟩⟩
    change 0 < (c x.val + b) 0
    simp only [PiLp.add_apply, b, PiLp.single_apply, ite_true]
    linarith
  have hi : e.toOpenPartialHomeomorph.IsImage D.carrier {v : Model d | 0 ≤ v 0} := by
    intro y hy
    exact iff_of_true (hpos y hy).le (interior_subset (hinside hy))
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ :=
    exists_openPartialHomeomorph_subtypes e.toOpenPartialHomeomorph hi x
      (⟨0, by simp⟩ : EuclideanHalfSpace d)
  refine ⟨⟨r, e, hrs, hrt, hrf, hrg, ?_⟩, ?_⟩
  · intro y hy
    have hye : y.val ∈ e.source := by rwa [hrs] at hy
    rw [hrf y hy]
    exact iff_of_false
      ((mem_interior_iff_notMem_frontier y.property).mp (hinside hye))
      (ne_of_gt (hpos _ hye))
  · rwa [hrs]

/-- The regular-sublevel presentation supplies enough extended half-space
charts to cover the entire actual domain. -/
theorem exists_extendedHalfSpaceChart {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) :
    ∃ c : ExtendedHalfSpaceChart D, x ∈ c.chart.source := by
  by_cases hx : x.val ∈ frontier D.carrier
  · exact D.exists_extendedHalfSpaceChart_at_boundary x hx
  · exact D.exists_extendedHalfSpaceChart_at_interior x
      ((mem_interior_iff_notMem_frontier x.property).mpr hx)

/-- Every transition between these half-space charts is the restriction of
an actual ambient smooth transition, including at its boundary. -/
theorem ExtendedHalfSpaceChart.contDiffOn_transition {d : ℕ} [NeZero d]
    {D : CompactDomain d} (c c' : ExtendedHalfSpaceChart D) :
    ContDiffOn ℝ ∞
      ((𝓡∂ d) ∘ (c.chart.symm.trans c'.chart) ∘ (𝓡∂ d).symm)
      ((𝓡∂ d).symm ⁻¹' (c.chart.symm.trans c'.chart).source ∩ range (𝓡∂ d)) := by
  let t := c.extension.symm.trans c'.extension
  let S := (𝓡∂ d).symm ⁻¹' (c.chart.symm.trans c'.chart).source ∩ range (𝓡∂ d)
  have hval (v : Model d) (hv : v ∈ range (𝓡∂ d)) :
      ((𝓡∂ d).symm v).val = v := (𝓡∂ d).right_inv hv
  have hsub : S ⊆ t.source := by
    intro v hv
    have hct : (𝓡∂ d).symm v ∈ c.chart.target := hv.1.1
    have hcs : c.chart.symm ((𝓡∂ d).symm v) ∈ c'.chart.source := hv.1.2
    have he : v ∈ c.extension.target := by
      rw [c.target_eq] at hct
      simpa only [mem_preimage, hval v hv.2] using hct
    have he' : c.extension.invFun v ∈ c'.extension.source := by
      rw [c'.source_eq] at hcs
      simpa only [mem_preimage, c.invFun_eq _ hct, hval v hv.2] using hcs
    exact ⟨he, he'⟩
  apply (t.contMDiffOn_toFun.contDiffOn.mono hsub).congr
  intro v hv
  have hct : (𝓡∂ d).symm v ∈ c.chart.target := hv.1.1
  have hcs : c.chart.symm ((𝓡∂ d).symm v) ∈ c'.chart.source := hv.1.2
  change (c'.chart (c.chart.symm ((𝓡∂ d).symm v))).val =
    c'.extension (c.extension.invFun v)
  rw [c'.toFun_eq _ hcs, c.invFun_eq _ hct, hval v hv.2]

/-- The preferred chart is chosen from the proved covering family. -/
def halfSpaceChartAt {d : ℕ} [NeZero d] (D : CompactDomain d) (x : D.Point) :
    ExtendedHalfSpaceChart D := (D.exists_extendedHalfSpaceChart x).choose

theorem mem_halfSpaceChartAt_source {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) : x ∈ (D.halfSpaceChartAt x).chart.source :=
  (D.exists_extendedHalfSpaceChart x).choose_spec

/-- The actual domain subtype has a native half-space atlas, using its
existing subspace topology. -/
instance halfSpaceChartedSpace {d : ℕ} [NeZero d] (D : CompactDomain d) :
    ChartedSpace (EuclideanHalfSpace d) D.Point where
  atlas := range (fun c : ExtendedHalfSpaceChart D => c.chart)
  chartAt x := (D.halfSpaceChartAt x).chart
  mem_chart_source := D.mem_halfSpaceChartAt_source
  chart_mem_atlas x := ⟨D.halfSpaceChartAt x, rfl⟩

/-- Smooth compatibility of the ambient extensions produces a native
smooth manifold with boundary on the actual compact domain. -/
instance isManifold_halfSpace {d : ℕ} [NeZero d] (D : CompactDomain d) :
    IsManifold (𝓡∂ d) ∞ D.Point := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨c, rfl⟩ ⟨c', rfl⟩
  exact c.contDiffOn_transition c'

/-- The boundary locus of every atlas chart is the actual frontier of the
regular-sublevel domain. -/
theorem halfSpaceChartAt_frontier_iff {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) :
    x.val ∈ frontier D.carrier ↔ ((chartAt (EuclideanHalfSpace d) x) x).val 0 = 0 :=
  (D.halfSpaceChartAt x).frontier_iff x (D.mem_halfSpaceChartAt_source x)

/-- Native manifold boundary points are exactly the ambient frontier points
of the represented compact domain. -/
theorem isBoundaryPoint_iff_frontier {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.Point) :
    (𝓡∂ d).IsBoundaryPoint x ↔ x.val ∈ frontier D.carrier := by
  rw [ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = ((chartAt (EuclideanHalfSpace d) x) x).val 0 ↔ _
  rw [eq_comm]
  exact (D.halfSpaceChartAt_frontier_iff x).symm

/-- The intrinsic boundary is the literal frontier subtype. -/
theorem boundary_eq_frontier {d : ℕ} [NeZero d] (D : CompactDomain d) :
    (𝓡∂ d).boundary D.Point = Subtype.val ⁻¹' frontier D.carrier := by
  ext x
  exact D.isBoundaryPoint_iff_frontier x

/-- The native manifold interior equals the ambient interior of the domain. -/
theorem interior_eq_interior {d : ℕ} [NeZero d] (D : CompactDomain d) :
    (𝓡∂ d).interior D.Point = Subtype.val ⁻¹' interior D.carrier := by
  ext x
  change (𝓡∂ d).IsInteriorPoint x ↔ x.val ∈ interior D.carrier
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    D.isBoundaryPoint_iff_frontier x]
  exact (mem_interior_iff_notMem_frontier x.property).symm

/-- The intrinsic inclusion into the supplied ambient extension is smooth
up to the boundary, through the same ambient chart extensions. -/
theorem contMDiff_subtype_val {d : ℕ} [NeZero d] (D : CompactDomain d) :
    ContMDiff (𝓡∂ d) 𝓘(ℝ, Model d) ∞ (Subtype.val : D.Point → D.extension.Point) := by
  intro x
  apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source (EuclideanHalfSpace d) x)).mpr
  let c := D.halfSpaceChartAt x
  let v := (c.chart x).val
  have hv : v ∈ c.extension.target := by
    have h := c.chart.map_source (D.mem_halfSpaceChartAt_source x)
    rwa [c.target_eq] at h
  have hvr : v ∈ range (𝓡∂ d) := ⟨c.chart x, rfl⟩
  have hval (z : Model d) (hz : z ∈ range (𝓡∂ d)) :
      ((𝓡∂ d).symm z).val = z := (𝓡∂ d).right_inv hz
  have heq : ∀ z ∈ c.extension.target ∩ range (𝓡∂ d),
      (Subtype.val ∘ (extChartAt (𝓡∂ d) x).symm) z = c.extension.invFun z := by
    intro z hz
    have hzt : (𝓡∂ d).symm z ∈ c.chart.target := by
      rw [c.target_eq]
      change ((𝓡∂ d).symm z).val ∈ c.extension.target
      rw [hval z hz.2]
      exact hz.1
    change (c.chart.symm ((𝓡∂ d).symm z)).val = c.extension.invFun z
    rw [c.invFun_eq _ hzt, hval z hz.2]
  have he := c.extension.contMDiffOn_invFun.contMDiffAt
    (c.extension.open_target.mem_nhds hv)
  apply he.contMDiffWithinAt.congr_of_eventuallyEq_of_mem _ hvr
  have ht : ∀ᶠ z in 𝓝 v, z ∈ c.extension.target := c.extension.open_target.mem_nhds hv
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzt hzr
  exact heq z ⟨hzt, hzr⟩

/-- A zero-dimensional domain has the discrete topology inherited from its
zero-dimensional ambient extension. -/
instance discreteTopology_zero (D : CompactDomain 0) : DiscreteTopology D.Point := by
  let : DiscreteTopology D.extension.Point :=
    ChartedSpace.discreteTopology (Model 0) D.extension.Point
  infer_instance

/-- In dimension zero the intrinsic charts are singleton charts, with the
zero-dimensional Euclidean model rather than a nonexistent half-space. -/
instance zeroChartedSpace (D : CompactDomain 0) : ChartedSpace (Model 0) D.Point :=
  ChartedSpace.ofDiscreteTopology

instance zeroIsManifold (D : CompactDomain 0) : IsManifold 𝓘(ℝ, Model 0) ∞ D.Point :=
  IsManifold.of_discreteTopology ∞

/-- Regularity of the supplied defining functions rules out an ambient
frontier in dimension zero. -/
theorem frontier_eq_empty_of_dimension_zero (D : CompactDomain 0) :
    frontier D.carrier = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (D.defining x hx).dimension_ne_zero rfl

/-- The zero-dimensional intrinsic and represented boundaries are both empty. -/
theorem zero_boundary_eq_frontier (D : CompactDomain 0) :
    (𝓘(ℝ, Model 0)).boundary D.Point = Subtype.val ⁻¹' frontier D.carrier := by
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty,
    D.frontier_eq_empty_of_dimension_zero, preimage_empty]

/-- The dimension-zero intrinsic inclusion is smooth as well. -/
theorem zero_contMDiff_subtype_val (D : CompactDomain 0) :
    ContMDiff 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) ∞
      (Subtype.val : D.Point → D.extension.Point) :=
  contMDiff_of_discreteTopology

end CompactDomain
end FsFltz.Geometry
