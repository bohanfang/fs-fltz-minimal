import FsFltz.Geometry.BoundaryAtlas

/-!
# Smooth maps into represented compact domains

Source: `geoemtric-part-fsf.tex`, the smooth-extension conventions and
`def:pair`, lines 119–160, and `sec:lean`, lines 783–814.

For the native atlas constructed in `BoundaryAtlas`, a map into the actual
domain is smooth precisely when its ambient inclusion is smooth. The proof
uses the chart's ambient extension, including at boundary points. This
correspondence makes the supplied boundary inclusion a native smooth map
onto the intrinsic boundary, and makes the actual ribbon map smooth on its
compact source. Dimension zero uses the already constructed discrete atlas.

These results do not construct a reverse global extension presentation, a
boundary diffeomorphism, a Liouville collar, or a completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace CompactDomain

section SmoothMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Smoothness into the native half-space domain can be checked on its
actual inclusion in the supplied ambient extension, pointwise. -/
theorem contMDiffAt_iff_subtype_val {d : ℕ} [NeZero d] (D : CompactDomain d)
    {f : X → D.Point} {x : X} :
    ContMDiffAt I (𝓡∂ d) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Model d) ∞ (Subtype.val ∘ f) x := by
  constructor
  · intro hf
    exact (D.contMDiff_subtype_val.contMDiffAt).comp x hf
  · intro hf
    have hc : ContinuousAt f x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuousAt
    apply contMDiffAt_iff_target.mpr
    refine ⟨hc, ?_⟩
    let c := D.halfSpaceChartAt (f x)
    have hcs : f x ∈ c.chart.source := D.mem_halfSpaceChartAt_source (f x)
    have hes : (f x).val ∈ c.extension.source := by rwa [c.source_eq] at hcs
    have he := c.extension.contMDiffOn_toFun.contMDiffAt
      (c.extension.open_source.mem_nhds hes)
    apply (he.comp x hf).congr_of_eventuallyEq
    filter_upwards [hc.eventually_mem (c.chart.open_source.mem_nhds hcs)] with y hy
    change (c.chart (f y)).val = c.extension (f y).val
    exact c.toFun_eq (f y) hy

/-- The native smooth-map condition is equivalent to the condition on the
represented ambient map; no extra smoothness certificate is required. -/
theorem contMDiff_iff_subtype_val {d : ℕ} [NeZero d] (D : CompactDomain d)
    {f : X → D.Point} :
    ContMDiff I (𝓡∂ d) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Model d) ∞ (Subtype.val ∘ f) := by
  constructor
  · intro hf x
    exact (D.contMDiffAt_iff_subtype_val).mp (hf x)
  · intro hf x
    exact (D.contMDiffAt_iff_subtype_val).mpr (hf x)

/-- The zero-dimensional correspondence uses the discrete intrinsic atlas.
A continuous map into a discrete domain is locally constant and smooth. -/
theorem zero_contMDiffAt_iff_subtype_val (D : CompactDomain 0)
    {f : X → D.Point} {x : X} :
    ContMDiffAt I 𝓘(ℝ, Model 0) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Model 0) ∞ (Subtype.val ∘ f) x := by
  constructor
  · intro hf
    exact (D.zero_contMDiff_subtype_val.contMDiffAt).comp x hf
  · intro hf
    have hc : ContinuousAt f x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuousAt
    apply contMDiffAt_const.congr_of_eventuallyEq
    exact hc.eventually_mem ((isOpen_discrete {f x}).mem_nhds (mem_singleton (f x)))

theorem zero_contMDiff_iff_subtype_val (D : CompactDomain 0)
    {f : X → D.Point} :
    ContMDiff I 𝓘(ℝ, Model 0) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Model 0) ∞ (Subtype.val ∘ f) := by
  constructor
  · intro hf x
    exact (D.zero_contMDiffAt_iff_subtype_val).mp (hf x)
  · intro hf x
    exact (D.zero_contMDiffAt_iff_subtype_val).mpr (hf x)

end SmoothMaps

/-- The native domain inclusion is an immersion up to its boundary. Its
chart coordinate map has identity differential and factors through this
inclusion via the proved smooth ambient chart extension. -/
theorem injective_mfderiv_subtype_val {d : ℕ} [NeZero d] (D : CompactDomain d)
    (x : D.Point) :
    Function.Injective (mfderiv (𝓡∂ d) 𝓘(ℝ, Model d)
      (Subtype.val : D.Point → D.extension.Point) x) := by
  let c := D.halfSpaceChartAt x
  have hcs : x ∈ c.chart.source := D.mem_halfSpaceChartAt_source x
  have hes : x.val ∈ c.extension.source := by rwa [c.source_eq] at hcs
  have heq : (extChartAt (𝓡∂ d) x : D.Point → Model d) =ᶠ[𝓝 x]
      c.extension ∘ Subtype.val := by
    filter_upwards [c.chart.open_source.mem_nhds hcs] with y hy
    exact c.toFun_eq y hy
  have hd := mfderiv_comp (f := (Subtype.val : D.Point → D.extension.Point))
    (g := c.extension) x
    ((c.extension.contMDiffOn_toFun.contMDiffAt
      (c.extension.open_source.mem_nhds hes)).mdifferentiableAt (by simp))
    (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
  have hi := mfderiv_extChartAt_self (I := 𝓡∂ d) (x := x)
  rw [heq.mfderiv_eq, hd] at hi
  have hi' (v : TangentSpace (𝓡∂ d) x) :
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.extension x.val
        (mfderiv (𝓡∂ d) 𝓘(ℝ, Model d) Subtype.val x v) = v :=
    congrArg (fun A => A v) hi
  intro v w hvw
  have h := congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.extension x.val) hvw
  exact (hi' v).symm.trans (h.trans (hi' w))

/-- The supplied boundary inclusion as a map into the actual domain. -/
def boundaryToPoint {d : ℕ} (D : CompactDomain d) (x : D.boundary.Point) : D.Point :=
  ⟨D.boundaryInclusion.map x, D.compact.isClosed.frontier_subset (by
    rw [← D.boundary_range]
    exact ⟨x, rfl⟩)⟩

@[simp] theorem boundaryToPoint_val {d : ℕ} (D : CompactDomain d)
    (x : D.boundary.Point) :
    (D.boundaryToPoint x).val = D.boundaryInclusion.map x := rfl

/-- The supplied smooth boundary presentation is smooth into the native
manifold with boundary, through its proved ambient-chart correspondence. -/
theorem contMDiff_boundaryToPoint {d : ℕ} [NeZero d] (D : CompactDomain d) :
    ContMDiff 𝓘(ℝ, Model (d - 1)) (𝓡∂ d) ∞ D.boundaryToPoint := by
  apply D.contMDiff_iff_subtype_val.mpr
  exact D.boundaryInclusion.map.contMDiff

/-- The map from the supplied boundary presentation has exactly the native
intrinsic boundary as its image. -/
theorem range_boundaryToPoint {d : ℕ} [NeZero d] (D : CompactDomain d) :
    range D.boundaryToPoint = (𝓡∂ d).boundary D.Point := by
  rw [D.boundary_eq_frontier]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change D.boundaryInclusion.map y ∈ frontier D.carrier
    rw [← D.boundary_range]
    exact ⟨y, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := D.boundary_range.symm ▸ hx
    exact ⟨y, Subtype.ext hy⟩

/-- The supplied boundary remains a topological embedding into the actual
domain with its subspace topology. -/
theorem isEmbedding_boundaryToPoint {d : ℕ} (D : CompactDomain d) :
    Topology.IsEmbedding D.boundaryToPoint := by
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp D.boundaryInclusion.embedding

/-- The native smooth boundary map is an immersion; injectivity of its
differential follows from the given ambient boundary immersion. -/
theorem injective_mfderiv_boundaryToPoint {d : ℕ} [NeZero d]
    (D : CompactDomain d) (x : D.boundary.Point) :
    Function.Injective (mfderiv 𝓘(ℝ, Model (d - 1)) (𝓡∂ d) D.boundaryToPoint x) := by
  intro v w hvw
  apply D.boundaryInclusion.immersion x
  have he := mfderiv_comp (f := D.boundaryToPoint)
    (g := (Subtype.val : D.Point → D.extension.Point)) x
    (D.contMDiff_subtype_val.mdifferentiableAt (by simp))
    (D.contMDiff_boundaryToPoint.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
    D.boundaryInclusion.map x = _ at he
  rw [he]
  exact congrArg (mfderiv (𝓡∂ d) 𝓘(ℝ, Model d)
    (Subtype.val : D.Point → D.extension.Point) (D.boundaryToPoint x)) hvw

/-- The empty zero-dimensional boundary has a smooth inclusion as well. -/
theorem zero_contMDiff_boundaryToPoint (D : CompactDomain 0) :
    ContMDiff 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) ∞ D.boundaryToPoint := by
  apply D.zero_contMDiff_iff_subtype_val.mpr
  exact D.boundaryInclusion.map.contMDiff

/-- The supplied zero-dimensional boundary has the same empty range as the
native boundary of its discrete domain. -/
theorem zero_range_boundaryToPoint (D : CompactDomain 0) :
    range D.boundaryToPoint = (𝓘(ℝ, Model 0)).boundary D.Point := by
  let : IsEmpty D.boundary.Point := D.zero_boundary rfl
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty]
  exact range_eq_empty D.boundaryToPoint

end CompactDomain

namespace WitnessedPair

/-- The actual ribbon map on compact points, with values in the actual
ambient domain. -/
def ribbonToPoint {n : ℕ} (P : WitnessedPair n) :
    P.ribbonDomain.domain.Point → P.ambientDomain.domain.Point :=
  fun x => P.ambientDomain.domain.boundaryToPoint (P.ribbonEmbedding.map x.val)

/-- In positive ribbon dimension the extension embedding restricts to a
native smooth map between the actual compact manifolds with boundary. -/
theorem contMDiff_ribbonToPoint {n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
    (P : WitnessedPair n) :
    ContMDiff (𝓡∂ (2 * n - 2)) (𝓡∂ (2 * n)) ∞ P.ribbonToPoint := by
  exact P.ambientDomain.domain.contMDiff_boundaryToPoint.comp
    (P.ribbonEmbedding.map.contMDiff.comp P.ribbonDomain.domain.contMDiff_subtype_val)

/-- For `n = 1` the ribbon is zero-dimensional and its actual map is smooth
using the discrete source atlas, as required by the source convention. -/
theorem contMDiff_ribbonToPoint_dimension_one (P : WitnessedPair 1) :
    ContMDiff 𝓘(ℝ, Model 0) (𝓡∂ 2) ∞ P.ribbonToPoint :=
  contMDiff_of_discreteTopology

/-- Restriction to compact points preserves the supplied ribbon's
topological embedding in the native ambient domain. -/
theorem isEmbedding_ribbonToPoint {n : ℕ} (P : WitnessedPair n) :
    Topology.IsEmbedding P.ribbonToPoint :=
  P.ambientDomain.domain.isEmbedding_boundaryToPoint.comp
    (P.ribbonEmbedding.embedding.comp Topology.IsEmbedding.subtypeVal)

/-- The native compact ribbon map is immersive, using the actual native
domain inclusion differential and the two supplied embedding differentials. -/
theorem injective_mfderiv_ribbonToPoint {n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
    (P : WitnessedPair n) (x : P.ribbonDomain.domain.Point) :
    Function.Injective (mfderiv (𝓡∂ (2 * n - 2)) (𝓡∂ (2 * n)) P.ribbonToPoint x) := by
  let f : P.ribbonDomain.domain.Point → P.ambientDomain.domain.boundary.Point :=
    fun y => P.ribbonEmbedding.map y.val
  have hf := P.ribbonEmbedding.map.contMDiff.comp
    P.ribbonDomain.domain.contMDiff_subtype_val
  have hd₁ := mfderiv_comp (f := (Subtype.val : P.ribbonDomain.domain.Point →
      P.ribbonDomain.domain.extension.Point)) (g := P.ribbonEmbedding.map) x
    (P.ribbonEmbedding.map.contMDiff.mdifferentiableAt (by simp))
    (P.ribbonDomain.domain.contMDiff_subtype_val.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (f := f) (g := P.ambientDomain.domain.boundaryToPoint) x
    (P.ambientDomain.domain.contMDiff_boundaryToPoint.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  change mfderiv (𝓡∂ (2 * n - 2)) (𝓡∂ (2 * n)) P.ribbonToPoint x = _ at hd₂
  change mfderiv (𝓡∂ (2 * n - 2)) 𝓘(ℝ, Model (2 * n - 1)) f x = _ at hd₁
  erw [hd₂, hd₁]
  exact (P.ambientDomain.domain.injective_mfderiv_boundaryToPoint (f x)).comp
    ((P.ribbonEmbedding.immersion x.val).comp
      (P.ribbonDomain.domain.injective_mfderiv_subtype_val x))

/-- The dimension-one ribbon also has injective differential: its native
tangent space is the zero vector space. -/
theorem injective_mfderiv_ribbonToPoint_dimension_one (P : WitnessedPair 1)
    (x : P.ribbonDomain.domain.Point) :
    Function.Injective (mfderiv 𝓘(ℝ, Model 0) (𝓡∂ 2) P.ribbonToPoint x) := by
  intro v w _
  exact PiLp.ext (fun i => Fin.elim0 i)

/-- The actual ribbon lies in the native intrinsic boundary of the actual
ambient compact domain. -/
theorem ribbonToPoint_mem_boundary {n : ℕ} [NeZero n] (P : WitnessedPair n)
    (x : P.ribbonDomain.domain.Point) :
    P.ribbonToPoint x ∈ (𝓡∂ (2 * n)).boundary P.ambientDomain.domain.Point := by
  rw [← P.ambientDomain.domain.range_boundaryToPoint]
  exact ⟨P.ribbonEmbedding.map x.val, rfl⟩

end WitnessedPair
end FsFltz.Geometry
