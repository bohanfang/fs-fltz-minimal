import FsFltz.Geometry.BoundaryPresentationBridge

/-!
# Intrinsic charts and the supplied boundary presentation

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The boundary charts are restrictions of the proved native
half-space charts to their zero first coordinate, followed by deletion of
that coordinate. Their ambient extensions prove smooth compatibility.

In these charts the actual frontier inclusion is the ambient inverse chart
composed with hyperplane insertion, hence is smooth. Its chart coordinate
map factors through the inclusion and has identity differential, proving
immersion without using the supplied boundary presentation. The supplied
boundary inclusion lifts to a bijective smooth immersion of this independent
atlas. Equal finite dimensions and the inverse function theorem give its
smooth inverse. The resulting diffeomorphism transports the actual restricted
boundary primitive to the supplied boundary form.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- Delete the first coordinate of the Euclidean boundary model. -/
def boundaryDrop (k : ℕ) : Model (k + 1) →L[ℝ] Model k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => v i.succ)
      map_add' := by intro v w; exact PiLp.ext (fun _ => rfl)
      map_smul' := by intro r v; exact PiLp.ext (fun _ => rfl) }

/-- Insert a zero first coordinate. -/
def boundaryInsert (k : ℕ) : Model k →L[ℝ] Model (k + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 v)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro i
        exact Fin.cases (by simp) (fun _ => rfl) i
      map_smul' := by
        intro r v
        apply PiLp.ext
        intro i
        exact Fin.cases (by simp) (fun _ => rfl) i }

@[simp] theorem boundaryDrop_apply {k : ℕ} (v : Model (k + 1)) (i : Fin k) :
    boundaryDrop k v i = v i.succ := rfl

@[simp] theorem boundaryInsert_zero {k : ℕ} (v : Model k) :
    boundaryInsert k v 0 = 0 := rfl

@[simp] theorem boundaryInsert_succ {k : ℕ} (v : Model k) (i : Fin k) :
    boundaryInsert k v i.succ = v i := rfl

@[simp] theorem boundaryDrop_insert {k : ℕ} (v : Model k) :
    boundaryDrop k (boundaryInsert k v) = v := PiLp.ext (fun _ => rfl)

theorem boundaryInsert_drop {k : ℕ} (v : Model (k + 1)) (hv : v 0 = 0) :
    boundaryInsert k (boundaryDrop k v) = v := by
  apply PiLp.ext
  intro i
  exact Fin.cases hv.symm (fun _ => rfl) i

/-- The zero first-coordinate hyperplane has its literal Euclidean model,
including when the boundary itself is zero-dimensional. -/
def boundaryHyperplaneHomeomorph (k : ℕ) : {v : Model (k + 1) // v 0 = 0} ≃ₜ Model k where
  toFun v := boundaryDrop k v.val
  invFun v := ⟨boundaryInsert k v, boundaryInsert_zero v⟩
  left_inv v := Subtype.ext (boundaryInsert_drop v.val v.property)
  right_inv := boundaryDrop_insert
  continuous_toFun := (boundaryDrop k).continuous.comp continuous_subtype_val
  continuous_invFun := (boundaryInsert k).continuous.subtype_mk _

namespace CompactDomain

/-- The actual ambient frontier, already proved to be the native domain's
intrinsic boundary. -/
abbrev FrontierPoint {d : ℕ} (D : CompactDomain d) :=
  {x : D.extension.Point // x ∈ frontier D.carrier}

/-- A frontier chart with its smooth ambient extension in both directions. -/
structure ExtendedFrontierChart {k : ℕ} (D : CompactDomain (k + 1)) where
  chart : OpenPartialHomeomorph D.FrontierPoint (Model k)
  extension : PartialDiffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    D.extension.Point (Model (k + 1)) ∞
  source_eq : chart.source = Subtype.val ⁻¹' extension.source
  target_eq : chart.target = boundaryInsert k ⁻¹' extension.target
  toFun_eq : ∀ y ∈ chart.source, chart y = boundaryDrop k (extension y.val)
  invFun_eq : ∀ v ∈ chart.target, (chart.symm v).val = extension.invFun (boundaryInsert k v)

/-- The boundary restriction of an extended half-space chart identifies
the entire ambient frontier with its zero first-coordinate hyperplane. -/
theorem ExtendedHalfSpaceChart.isImage_frontier {k : ℕ}
    {D : CompactDomain (k + 1)} (c : ExtendedHalfSpaceChart D) :
    c.extension.toOpenPartialHomeomorph.IsImage (frontier D.carrier)
      {v : Model (k + 1) | v 0 = 0} := by
  intro y hy
  constructor
  · intro hv
    let v : EuclideanHalfSpace (k + 1) := ⟨c.extension y, hv.ge⟩
    have hvt : v ∈ c.chart.target := by
      rw [c.target_eq]
      exact c.extension.map_source hy
    let z := c.chart.symm v
    have hzs : z ∈ c.chart.source := c.chart.map_target hvt
    have hzv : z.val = y := by
      rw [c.invFun_eq v hvt]
      exact c.extension.left_inv hy
    have hzero : (c.chart z).val 0 = 0 := by
      rw [c.chart.right_inv hvt]
      exact hv
    exact hzv ▸ (c.frontier_iff z hzs).mpr hzero
  · intro hfr
    let z : D.Point := ⟨y, D.compact.isClosed.frontier_subset hfr⟩
    have hzs : z ∈ c.chart.source := by rw [c.source_eq]; exact hy
    change (c.extension z.val) 0 = 0
    rw [← c.toFun_eq z hzs]
    exact (c.frontier_iff z hzs).mp hfr

/-- Every boundary point admits a chart obtained from the native domain
atlas by restriction to its boundary hyperplane. -/
theorem exists_extendedFrontierChart {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.FrontierPoint) :
    ∃ c : ExtendedFrontierChart D, x ∈ c.chart.source := by
  let y : D.Point := ⟨x.val, D.compact.isClosed.frontier_subset x.property⟩
  obtain ⟨c, hy⟩ := D.exists_extendedHalfSpaceChart_at_boundary y x.property
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ := exists_openPartialHomeomorph_subtypes
    c.extension.toOpenPartialHomeomorph c.isImage_frontier x ⟨0, by simp⟩
  let q := r.trans (boundaryHyperplaneHomeomorph k).toOpenPartialHomeomorph
  refine ⟨⟨q, c.extension, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change r.source ∩ r ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    exact hrs
  · change univ ∩ (boundaryHyperplaneHomeomorph k).symm ⁻¹' r.target = _
    rw [univ_inter, hrt]
    rfl
  · intro z hz
    change boundaryDrop k (r z).val = boundaryDrop k (c.extension z.val)
    rw [hrf z hz.1]
    rfl
  · intro v hv
    change (r.symm ((boundaryHyperplaneHomeomorph k).symm v)).val = _
    exact hrg _ hv.2
  · change x ∈ r.source ∩ r ⁻¹' univ
    rw [hrs]
    exact ⟨by rwa [c.source_eq] at hy, mem_univ _⟩

/-- Frontier chart transitions are restrictions of the actual ambient
smooth transitions, composed with the fixed hyperplane insertion/deletion. -/
theorem ExtendedFrontierChart.contDiffOn_transition {k : ℕ}
    {D : CompactDomain (k + 1)} (c c' : ExtendedFrontierChart D) :
    ContDiffOn ℝ ∞ (c.chart.symm.trans c'.chart) (c.chart.symm.trans c'.chart).source := by
  let t := c.extension.symm.trans c'.extension
  let S := (c.chart.symm.trans c'.chart).source
  have hsub : MapsTo (boundaryInsert k) S t.source := by
    intro v hv
    have hct : v ∈ c.chart.target := hv.1
    have hcs : c.chart.symm v ∈ c'.chart.source := hv.2
    have he : boundaryInsert k v ∈ c.extension.target := by
      rwa [c.target_eq] at hct
    have he' : c.extension.invFun (boundaryInsert k v) ∈ c'.extension.source := by
      rw [c'.source_eq] at hcs
      change (c.chart.symm v).val ∈ c'.extension.source at hcs
      rwa [c.invFun_eq v hv.1] at hcs
    exact ⟨he, he'⟩
  apply ((boundaryDrop k).contDiff.comp_contDiffOn
    (t.contMDiffOn_toFun.contDiffOn.comp (boundaryInsert k).contDiff.contDiffOn hsub)).congr
  intro v hv
  change v ∈ c.chart.target ∧ c.chart.symm v ∈ c'.chart.source at hv
  change c'.chart (c.chart.symm v) =
    boundaryDrop k (c'.extension (c.extension.invFun (boundaryInsert k v)))
  rw [c'.toFun_eq (c.chart.symm v) hv.2, c.invFun_eq v hv.1]

/-- Preferred intrinsic boundary charts come from the proved boundary
restrictions of the domain atlas. -/
def frontierChartAt {k : ℕ} (D : CompactDomain (k + 1)) (x : D.FrontierPoint) :
    ExtendedFrontierChart D := (D.exists_extendedFrontierChart x).choose

theorem mem_frontierChartAt_source {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.FrontierPoint) : x ∈ (D.frontierChartAt x).chart.source :=
  (D.exists_extendedFrontierChart x).choose_spec

/-- The actual frontier has its intrinsic atlas, constructed independently
of the supplied abstract boundary manifold. -/
instance frontierChartedSpace {k : ℕ} (D : CompactDomain (k + 1)) :
    ChartedSpace (Model k) D.FrontierPoint where
  atlas := range (fun c : ExtendedFrontierChart D => c.chart)
  chartAt x := (D.frontierChartAt x).chart
  mem_chart_source := D.mem_frontierChartAt_source
  chart_mem_atlas x := ⟨D.frontierChartAt x, rfl⟩

instance frontierIsManifold {k : ℕ} (D : CompactDomain (k + 1)) :
    IsManifold 𝓘(ℝ, Model k) ∞ D.FrontierPoint := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨c, rfl⟩ ⟨c', rfl⟩
  simpa using c.contDiffOn_transition c'

/-- The actual frontier inclusion is smooth with the independently
constructed intrinsic boundary atlas. -/
theorem contMDiff_frontier_val {k : ℕ} (D : CompactDomain (k + 1)) :
    ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1)) ∞
      (Subtype.val : D.FrontierPoint → D.extension.Point) := by
  intro x
  apply (contMDiffAt_iff_source_of_mem_source (mem_chart_source (Model k) x)).mpr
  let c := D.frontierChartAt x
  have hc : c.chart x ∈ c.chart.target := c.chart.map_source (D.mem_frontierChartAt_source x)
  have he : boundaryInsert k (c.chart x) ∈ c.extension.target := by
    rwa [c.target_eq] at hc
  have hs := c.extension.contMDiffOn_invFun.contMDiffAt
    (c.extension.open_target.mem_nhds he)
  apply (hs.comp (c.chart x) (boundaryInsert k).contDiff.contMDiff.contMDiffAt).contMDiffWithinAt
    |>.congr_of_eventuallyEq_of_mem _ (by simp)
  have ht : ∀ᶠ v in 𝓝 (c.chart x), v ∈ c.chart.target :=
    c.chart.open_target.mem_nhds hc
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with v hv
  change (c.chart.symm v).val = c.extension.invFun (boundaryInsert k v)
  exact c.invFun_eq v hv

section SmoothMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Native smoothness into the actual frontier is equivalent to ambient
smoothness of its inclusion. -/
theorem contMDiffAt_frontier_iff_val {k : ℕ} (D : CompactDomain (k + 1))
    {f : X → D.FrontierPoint} {x : X} :
    ContMDiffAt I 𝓘(ℝ, Model k) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Model (k + 1)) ∞ (Subtype.val ∘ f) x := by
  constructor
  · intro hf
    exact D.contMDiff_frontier_val.contMDiffAt.comp x hf
  · intro hf
    have hc : ContinuousAt f x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuousAt
    apply contMDiffAt_iff_target.mpr
    refine ⟨hc, ?_⟩
    let c := D.frontierChartAt (f x)
    have hcs : f x ∈ c.chart.source := D.mem_frontierChartAt_source (f x)
    have hes : (f x).val ∈ c.extension.source := by rwa [c.source_eq] at hcs
    have he := c.extension.contMDiffOn_toFun.contMDiffAt
      (c.extension.open_source.mem_nhds hes)
    apply ((boundaryDrop k).contDiff.contMDiff.contMDiffAt.comp x (he.comp x hf))
      |>.congr_of_eventuallyEq
    filter_upwards [hc.eventually_mem (c.chart.open_source.mem_nhds hcs)] with y hy
    exact c.toFun_eq (f y) hy

theorem contMDiff_frontier_iff_val {k : ℕ} (D : CompactDomain (k + 1))
    {f : X → D.FrontierPoint} :
    ContMDiff I 𝓘(ℝ, Model k) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Model (k + 1)) ∞ (Subtype.val ∘ f) := by
  constructor
  · intro hf x
    exact (D.contMDiffAt_frontier_iff_val).mp (hf x)
  · intro hf x
    exact (D.contMDiffAt_frontier_iff_val).mpr (hf x)

end SmoothMaps

/-- The intrinsic frontier inclusion is immersive from its own constructed
charts, independently of the supplied boundary presentation. -/
theorem injective_mfderiv_frontier_val {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.FrontierPoint) :
    Function.Injective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
      (Subtype.val : D.FrontierPoint → D.extension.Point) x) := by
  let c := D.frontierChartAt x
  have hcs : x ∈ c.chart.source := D.mem_frontierChartAt_source x
  have hes : x.val ∈ c.extension.source := by rwa [c.source_eq] at hcs
  let g : D.extension.Point → Model k := boundaryDrop k ∘ c.extension
  have hg : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) ∞ g x.val :=
    (boundaryDrop k).contMDiff.contMDiffAt.comp x.val
      (c.extension.contMDiffOn_toFun.contMDiffAt (c.extension.open_source.mem_nhds hes))
  have heq : (extChartAt 𝓘(ℝ, Model k) x : D.FrontierPoint → Model k) =ᶠ[𝓝 x]
      g ∘ Subtype.val := by
    filter_upwards [c.chart.open_source.mem_nhds hcs] with y hy
    exact c.toFun_eq y hy
  have hd := mfderiv_comp (f := (Subtype.val : D.FrontierPoint → D.extension.Point))
    (g := g) x (hg.mdifferentiableAt (by simp))
    (D.contMDiff_frontier_val.mdifferentiableAt (by simp))
  have hi := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model k)) (x := x)
  rw [heq.mfderiv_eq, hd] at hi
  have hi' (v : TangentSpace 𝓘(ℝ, Model k) x) :
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) g x.val
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1)) Subtype.val x v) = v :=
    congrArg (fun A => A v) hi
  intro v w hvw
  have h := congrArg (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) g x.val) hvw
  exact (hi' v).symm.trans (h.trans (hi' w))

/-- The independently constructed smooth manifold on the actual frontier. -/
abbrev intrinsicBoundary {k : ℕ} (D : CompactDomain (k + 1)) : SmoothManifold k where
  Point := D.FrontierPoint
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

/-- The actual smooth embedding of the intrinsic boundary in the supplied
ambient extension; every component has been constructed from its charts. -/
def intrinsicBoundaryInclusion {k : ℕ} (D : CompactDomain (k + 1)) :
    D.intrinsicBoundary.SmoothEmbedding D.extension where
  map := ⟨Subtype.val, D.contMDiff_frontier_val⟩
  embedding := Topology.IsEmbedding.subtypeVal
  immersion := D.injective_mfderiv_frontier_val

/-- The actual frontier is the literal intrinsic boundary subset of the
native half-space domain, with its inherited topology. -/
def intrinsicBoundaryPointHomeomorph {k : ℕ} (D : CompactDomain (k + 1)) :
    D.FrontierPoint ≃ₜ (𝓡∂ (k + 1)).boundary D.Point where
  toFun x := ⟨⟨x.val, D.compact.isClosed.frontier_subset x.property⟩,
    (D.isBoundaryPoint_iff_frontier _).mpr x.property⟩
  invFun x := ⟨x.val.val, (D.isBoundaryPoint_iff_frontier x.val).mp x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_val.subtype_mk _

/-- The supplied boundary embedding, with its actual frontier as codomain. -/
def boundaryToFrontier {d : ℕ} (D : CompactDomain d) (x : D.boundary.Point) : D.FrontierPoint :=
  ⟨D.boundaryInclusion.map x, by rw [← D.boundary_range]; exact ⟨x, rfl⟩⟩

theorem bijective_boundaryToFrontier {d : ℕ} (D : CompactDomain d) :
    Function.Bijective D.boundaryToFrontier := by
  constructor
  · intro x y hxy
    exact D.boundaryInclusion.embedding.injective (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨y, hy⟩ : ∃ y, D.boundaryInclusion.map y = x.val := by
      simpa only [← D.boundary_range, mem_range] using x.property
    exact ⟨y, Subtype.ext hy⟩

theorem contMDiff_boundaryToFrontier {k : ℕ} (D : CompactDomain (k + 1)) :
    ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ D.boundaryToFrontier := by
  apply D.contMDiff_frontier_iff_val.mpr
  exact D.boundaryInclusion.map.contMDiff

theorem injective_mfderiv_boundaryToFrontier {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.boundary.Point) :
    Function.Injective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) D.boundaryToFrontier x) := by
  intro v w hvw
  apply D.boundaryInclusion.immersion x
  have he := mfderiv_comp (f := D.boundaryToFrontier)
    (g := (Subtype.val : D.FrontierPoint → D.extension.Point)) x
    (D.contMDiff_frontier_val.mdifferentiableAt (by simp))
    (D.contMDiff_boundaryToFrontier.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1)) D.boundaryInclusion.map x = _ at he
  erw [he]
  exact congrArg (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
    (Subtype.val : D.FrontierPoint → D.extension.Point) (D.boundaryToFrontier x)) hvw

/-- Equal finite dimensions upgrade the supplied boundary immersion to a
local diffeomorphism of the independently constructed intrinsic boundary. -/
theorem isLocalDiffeomorph_boundaryToFrontier {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.boundary.Point) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ D.boundaryToFrontier x := by
  apply isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ
    D.contMDiff_boundaryToFrontier.contMDiffOn (mem_univ x)
  have hi := D.injective_mfderiv_boundaryToFrontier x
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The specified boundary inclusion is a smooth diffeomorphism onto the
actual intrinsic boundary. Smoothness of its inverse is proved by the
inverse function theorem, rather than put into the atlas or assumed. -/
def boundaryDiffeomorph {k : ℕ} (D : CompactDomain (k + 1)) :
    D.boundary.SmoothEquiv D.intrinsicBoundary := by
  let e := Equiv.ofBijective D.boundaryToFrontier D.bijective_boundaryToFrontier
  refine { e with
    contMDiff_toFun := D.contMDiff_boundaryToFrontier
    contMDiff_invFun := ?_ }
  intro y
  obtain ⟨q, hxq, hq⟩ := D.isLocalDiffeomorph_boundaryToFrontier (e.symm y)
  have hqy : q (e.symm y) = y := (hq hxq).symm.trans (e.apply_symm_apply y)
  have hyq : y ∈ q.target := hqy ▸ q.map_source hxq
  apply (q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds hyq))
    |>.congr_of_eventuallyEq
  filter_upwards [q.open_target.mem_nhds hyq] with z hz
  apply e.injective
  have hqz : e (q.invFun z) = z := (hq (q.map_target hz)).trans (q.right_inv hz)
  exact (e.apply_symm_apply z).trans hqz.symm

@[simp] theorem boundaryDiffeomorph_val {k : ℕ} (D : CompactDomain (k + 1))
    (x : D.boundary.Point) :
    (D.boundaryDiffeomorph x).val = D.boundaryInclusion.map x := rfl

/-- The actual frontier also carries the discrete atlas in ambient
dimension zero. Its emptiness was proved from defining-function regularity. -/
instance zeroFrontierDiscreteTopology (D : CompactDomain 0) :
    DiscreteTopology D.FrontierPoint := by
  let : DiscreteTopology D.extension.Point :=
    ChartedSpace.discreteTopology (Model 0) D.extension.Point
  infer_instance

instance zeroFrontierChartedSpace (D : CompactDomain 0) :
    ChartedSpace (Model 0) D.FrontierPoint := ChartedSpace.ofDiscreteTopology

instance zeroFrontierIsManifold (D : CompactDomain 0) :
    IsManifold 𝓘(ℝ, Model 0) ∞ D.FrontierPoint := IsManifold.of_discreteTopology ∞

abbrev zeroIntrinsicBoundary (D : CompactDomain 0) : SmoothManifold 0 where
  Point := D.FrontierPoint
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

def zeroIntrinsicBoundaryInclusion (D : CompactDomain 0) :
    D.zeroIntrinsicBoundary.SmoothEmbedding D.extension where
  map := ⟨Subtype.val, contMDiff_of_discreteTopology⟩
  embedding := Topology.IsEmbedding.subtypeVal
  immersion := by
    intro x v w _
    exact PiLp.ext (fun i => Fin.elim0 i)

/-- The dimension-zero supplied boundary and actual frontier are both
empty and have the same native smooth structure. -/
def zeroBoundaryDiffeomorph (D : CompactDomain 0) :
    D.boundary.SmoothEquiv D.zeroIntrinsicBoundary := by
  let e := Equiv.ofBijective D.boundaryToFrontier D.bijective_boundaryToFrontier
  let : IsEmpty D.boundary.Point := D.zero_boundary rfl
  refine { e with
    contMDiff_toFun := ?_
    contMDiff_invFun := contMDiff_of_discreteTopology }
  intro x
  exact isEmptyElim x

/-- The primitive of the intrinsic boundary is its actual restriction
through the smooth frontier inclusion. -/
def intrinsicBoundaryForm {k : ℕ} (D : CompactDomain (k + 1))
    (alpha : D.extension.Form 1) : D.intrinsicBoundary.Form 1 :=
  D.intrinsicBoundary.pullback D.extension Subtype.val alpha

/-- The boundary diffeomorphism transports the actual intrinsic boundary
primitive to the specified primitive on the supplied boundary presentation. -/
theorem pullback_intrinsicBoundaryForm {k : ℕ} (D : CompactDomain (k + 1))
    (alpha : D.extension.Form 1) :
    D.boundary.pullback D.intrinsicBoundary D.boundaryDiffeomorph
      (D.intrinsicBoundaryForm alpha) = D.boundaryForm alpha := by
  exact (SmoothManifold.pullback_comp D.boundary D.intrinsicBoundary D.extension
    (D.boundaryDiffeomorph.contMDiff.mdifferentiable (by simp))
    (D.contMDiff_frontier_val.mdifferentiable (by simp)) alpha).symm

end CompactDomain
end FsFltz.Geometry
