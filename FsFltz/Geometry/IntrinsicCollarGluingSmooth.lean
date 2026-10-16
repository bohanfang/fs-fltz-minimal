import FsFltz.QuotientGeometry
import FsFltz.Geometry.IntrinsicCollarGluing
import FsFltz.Geometry.IntrinsicCylinder

/-!
# Smooth charts on the actual native collar attachment

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The charts are pushed through open embeddings of the native
interior and the two-sided cylinder. Their mixed transitions are proved from
the original collar and its produced inverse germs, rather than supplied as
a smooth atlas on the quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

section OpenCover

variable {E U V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace X]
  [ChartedSpace E U] [ChartedSpace E V]
  [IsManifold 𝓘(ℝ, E) ∞ U] [IsManifold 𝓘(ℝ, E) ∞ V]
  {i : U → X} {j : V → X}
  (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)

/-- Smooth germs between two open patches prove the mixed chart transitions. -/
theorem contDiffOn_lifted_transition
    (hij : ∀ x y, i x = j y → ∃ g : U → V,
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g x ∧ g x = y ∧
        ∀ᶠ z in 𝓝 x, i z = j (g z))
    {e : OpenPartialHomeomorph U E} {f : OpenPartialHomeomorph V E}
    (he : e ∈ atlas E U) (hf : f ∈ atlas E V) :
    ContDiffOn ℝ ∞ ((e.lift_openEmbedding hi).symm.trans (f.lift_openEmbedding hj))
      ((e.lift_openEmbedding hi).symm.trans (f.lift_openEmbedding hj)).source := by
  intro z hz
  change z ∈ e.target ∧ i (e.symm z) ∈ j '' f.source at hz
  obtain ⟨y, hy, hiy⟩ := hz.2
  obtain ⟨g, hg, hgy, heq⟩ := hij (e.symm z) y hiy.symm
  have he' := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.subset_maximalAtlas he) hz.1
  have hf' := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.subset_maximalAtlas hf) hy
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (f ∘ g ∘ e.symm) z :=
    hf'.comp_of_eq (hg.comp z he') hgy
  apply (hcomp.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  have heq' := he'.continuousAt.eventually heq
  filter_upwards [heq'] with w hw
  change (f.lift_openEmbedding hj) (i (e.symm w)) = f (g (e.symm w))
  rw [hw, OpenPartialHomeomorph.lift_openEmbedding_apply]

/-- The two families of pushed charts. -/
def openCoverAtlas : Set (OpenPartialHomeomorph X E) :=
  (fun e : OpenPartialHomeomorph U E => e.lift_openEmbedding hi) '' atlas E U ∪
    (fun e : OpenPartialHomeomorph V E => e.lift_openEmbedding hj) '' atlas E V

variable (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)

include hcover in
omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ U] [IsManifold 𝓘(ℝ, E) ∞ V] in
theorem exists_openCover_chart (x : X) :
    ∃ e ∈ openCoverAtlas (E := E) hi hj, x ∈ e.source := by
  rcases hcover x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · refine ⟨(chartAt E u).lift_openEmbedding hi, Or.inl ?_, ?_⟩
    · exact ⟨chartAt E u, chart_mem_atlas E u, rfl⟩
    · exact ⟨u, mem_chart_source E u, rfl⟩
  · refine ⟨(chartAt E v).lift_openEmbedding hj, Or.inr ?_, ?_⟩
    · exact ⟨chartAt E v, chart_mem_atlas E v, rfl⟩
    · exact ⟨v, mem_chart_source E v, rfl⟩

/-- The charted space on the existing quotient topology, constructed from an open cover. -/
@[instance_reducible]
def openCoverChartedSpace : ChartedSpace E X where
  atlas := openCoverAtlas (E := E) hi hj
  chartAt x := (exists_openCover_chart (E := E) hi hj hcover x).choose
  mem_chart_source x := (exists_openCover_chart (E := E) hi hj hcover x).choose_spec.2
  chart_mem_atlas x := (exists_openCover_chart (E := E) hi hj hcover x).choose_spec.1

/-- Smoothness of each overlap germ gives a smooth atlas on the covered space. -/
theorem openCover_isManifold
    (hij : ∀ x y, i x = j y → ∃ g : U → V,
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g x ∧ g x = y ∧
        ∀ᶠ z in 𝓝 x, i z = j (g z))
    (hji : ∀ y x, j y = i x → ∃ g : V → U,
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g y ∧ g y = x ∧
        ∀ᶠ z in 𝓝 y, j z = i (g z)) :
    letI := openCoverChartedSpace (E := E) hi hj hcover
    IsManifold 𝓘(ℝ, E) ∞ X := by
  let := openCoverChartedSpace (E := E) hi hj hcover
  apply isManifold_of_contDiffOn
  intro e f he hf
  change e ∈ openCoverAtlas hi hj at he
  change f ∈ openCoverAtlas hi hj at hf
  rcases he with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;>
    rcases hf with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact ((contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible he hf).1
  · simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, preimage_id, range_id, inter_univ] using
      contDiffOn_lifted_transition hi hj hij he hf
  · simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, preimage_id, range_id, inter_univ] using
      contDiffOn_lifted_transition hj hi hji he hf
  · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact ((contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible he hf).1

omit [IsManifold 𝓘(ℝ, E) ∞ V] in
/-- The first patch inclusion is smooth for the atlas made from the two patches. -/
theorem contMDiff_openCover_inclusion
    (hs : letI := openCoverChartedSpace (E := E) hi hj hcover
      IsManifold 𝓘(ℝ, E) ∞ X) :
    letI := openCoverChartedSpace (E := E) hi hj hcover
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ i := by
  let := openCoverChartedSpace (E := E) hi hj hcover
  let : IsManifold 𝓘(ℝ, E) ∞ X := hs
  intro u
  let e := chartAt E u
  let f := e.lift_openEmbedding hi
  have hf : f ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X := by
    apply IsManifold.subset_maximalAtlas
    exact Or.inl ⟨e, chart_mem_atlas E u, rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas hf
    (show i u ∈ f.source from ⟨u, mem_chart_source E u, rfl⟩)).mpr
  refine ⟨hi.continuous.continuousAt.continuousWithinAt, ?_⟩
  have he := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas u) (mem_chart_source E u)
  apply he.contMDiffWithinAt.congr
  · intro v _
    exact OpenPartialHomeomorph.lift_openEmbedding_apply e hi
  · exact OpenPartialHomeomorph.lift_openEmbedding_apply e hi

omit [IsManifold 𝓘(ℝ, E) ∞ U] in
/-- The second patch inclusion is smooth for that same atlas. -/
theorem contMDiff_openCover_inclusion_right
    (hs : letI := openCoverChartedSpace (E := E) hi hj hcover
      IsManifold 𝓘(ℝ, E) ∞ X) :
    letI := openCoverChartedSpace (E := E) hi hj hcover
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ j := by
  let := openCoverChartedSpace (E := E) hi hj hcover
  let : IsManifold 𝓘(ℝ, E) ∞ X := hs
  intro v
  let e := chartAt E v
  let f := e.lift_openEmbedding hj
  have hf : f ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X := by
    apply IsManifold.subset_maximalAtlas
    exact Or.inr ⟨e, chart_mem_atlas E v, rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas hf
    (show j v ∈ f.source from ⟨v, mem_chart_source E v, rfl⟩)).mpr
  refine ⟨hj.continuous.continuousAt.continuousWithinAt, ?_⟩
  have he := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas v) (mem_chart_source E v)
  apply he.contMDiffWithinAt.congr
  · intro w _
    exact OpenPartialHomeomorph.lift_openEmbedding_apply e hj
  · exact OpenPartialHomeomorph.lift_openEmbedding_apply e hj

omit [IsManifold 𝓘(ℝ, E) ∞ V] in
/-- A pushed patch inclusion has injective actual differential. -/
theorem injective_mfderiv_openCover_inclusion
    (hs : letI := openCoverChartedSpace (E := E) hi hj hcover
      IsManifold 𝓘(ℝ, E) ∞ X) (u : U) :
    letI := openCoverChartedSpace (E := E) hi hj hcover
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) i u) := by
  let := openCoverChartedSpace (E := E) hi hj hcover
  let : IsManifold 𝓘(ℝ, E) ∞ X := hs
  let e := chartAt E u
  let f := e.lift_openEmbedding hi
  have hf : f ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X := by
    apply IsManifold.subset_maximalAtlas
    exact Or.inl ⟨e, chart_mem_atlas E u, rfl⟩
  have hfs : i u ∈ f.source := ⟨u, mem_chart_source E u, rfl⟩
  have hd := mfderiv_comp u
    ((contMDiffAt_of_mem_maximalAtlas hf hfs).mdifferentiableAt (by simp))
    ((contMDiff_openCover_inclusion hi hj hcover hs).mdifferentiableAt (by simp))
  have heq : f ∘ i = e := funext (fun _ => OpenPartialHomeomorph.lift_openEmbedding_apply e hi)
  rw [heq] at hd
  have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e u = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := u)
  rw [hid] at hd
  intro v w hvw
  have heval (a : TangentSpace 𝓘(ℝ, E) u) := congrArg (fun A => A a) hd
  exact (heval v).trans ((congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (i u)) hvw).trans
    (heval w).symm)

end OpenCover

section InverseGerms

variable {E U X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace U] [TopologicalSpace X] [ChartedSpace E U] [ChartedSpace E X]
  [IsManifold 𝓘(ℝ, E) ∞ U] [IsManifold 𝓘(ℝ, E) ∞ X]
  {i : U → X} (hi : IsOpenEmbedding i)

omit [IsManifold 𝓘(ℝ, E) ∞ X] in
/-- A pushed chart supplies an actual smooth inverse germ of its patch map. -/
theorem smooth_inverse_germ_of_lifted_chart (u : U)
    (hf : (chartAt E u).lift_openEmbedding hi ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X) :
    ∃ g : X → U, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g (i u) ∧ g (i u) = u ∧
      ∀ᶠ z in 𝓝 (i u), i (g z) = z := by
  let e := chartAt E u
  let f := e.lift_openEmbedding hi
  have hu : u ∈ e.source := mem_chart_source E u
  have hfu : f (i u) = e u := OpenPartialHomeomorph.lift_openEmbedding_apply e hi
  have hfs : i u ∈ f.source := ⟨u, hu, rfl⟩
  have hes := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas u) (e.map_source hu)
  have hff := contMDiffAt_of_mem_maximalAtlas hf hfs
  refine ⟨e.symm ∘ f, hes.comp_of_eq hff hfu, ?_, ?_⟩
  · change e.symm (f (i u)) = u
    rw [hfu, e.left_inv hu]
  · filter_upwards [f.open_source.mem_nhds hfs] with z hz
    exact f.left_inv hz

variable {A M : Type*} [TopologicalSpace A] [TopologicalSpace M]
  {s : Set A} {C : s → M} (hC : IsOpenEmbedding C)

include hC in
/-- A left-inverse germ of an open embedding is also a right-inverse germ
on an actual neighborhood in its target. -/
theorem eventually_inverse_of_openEmbedding (p : s) (g : M → A)
    (hg : ∀ᶠ q in 𝓝 p, g (C q) = q.val) :
    ∀ᶠ z in 𝓝 (C p), ∃ q : s, C q = z ∧ g z = q.val := by
  rw [← hC.map_nhds_eq p]
  change ∀ᶠ q in 𝓝 p, ∃ r : s, C r = C q ∧ g (C q) = r.val
  filter_upwards [hg] with q hq
  exact ⟨q, rfl, hq⟩

end InverseGerms

section Native

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

/-- A total map to the band, equal to a given product map wherever it is in the band. -/
def intoBand {X : Type*} (p : Band δ (IntrinsicBoundary.Point k M))
    (f : X → ℝ × IntrinsicBoundary.Point k M) : X → Band δ (IntrinsicBoundary.Point k M) :=
  fun x => if hx : f x ∈ Band δ (IntrinsicBoundary.Point k M) then ⟨f x, hx⟩ else p

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem intoBand_val {X : Type*} (p : Band δ (IntrinsicBoundary.Point k M))
    (f : X → ℝ × IntrinsicBoundary.Point k M) {x : X}
    (hx : f x ∈ Band δ (IntrinsicBoundary.Point k M)) :
    (intoBand p f x).val = f x := by simp [intoBand, hx]

section SmoothBandLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Local smoothness of a product map gives local smoothness of its total band lift. -/
theorem contMDiffAt_intoBand (p : Band δ (IntrinsicBoundary.Point k M))
    (f : X → ℝ × IntrinsicBoundary.Point k M) {x : X}
    (hf : ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ f x)
    (hx : f x ∈ Band δ (IntrinsicBoundary.Point k M)) :
    ContMDiffAt I 𝓘(ℝ, Model (k + 1)) ∞ (intoBand p f) x := by
  apply contMDiffAt_band_iff_val.mpr
  apply hf.congr_of_eventuallyEq
  have hn := hf.continuousAt.eventually ((bandOpen δ _).isOpen.mem_nhds hx)
  filter_upwards [hn] with y hy
  exact intoBand_val p f hy

end SmoothBandLift

include hemb in
/-- The produced native inverse germ determines the actual original-side
inverse, also at the seam. -/
theorem collar_inverse_germ
    (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
      ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
          ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
    (p : Half δ (IntrinsicBoundary.Point k M)) :
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p.val) ∧
        g (C p.val) = p.val ∧
          ∀ᶠ z in 𝓝 (C p.val), ∃ q : Half δ (IntrinsicBoundary.Point k M),
            C q.val = z ∧ g z = q.val := by
  obtain ⟨g, hg, heq⟩ := hinv p.val p.property
  rw [nhdsWithin_eq_map_subtype_coe p.property] at heq
  change ∀ᶠ q in 𝓝 p, g (C q.val) = q.val at heq
  exact ⟨g, hg, heq.self_of_nhds,
    eventually_inverse_of_openEmbedding hemb p g heq⟩

variable
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)

include hboundary in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem collar_isInterior_of_pos (p : Band δ (IntrinsicBoundary.Point k M))
    (hp : 0 < p.val.1) : (𝓡∂ (k + 1)).IsInteriorPoint (C p.val) := by
  apply ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mpr
  intro hb
  have hz := (hboundary (halfOfNonneg p hp.le)).mp hb
  exact (ne_of_gt hp) hz

include hC in
theorem contMDiffAt_collar_of_pos (p : Band δ (IntrinsicBoundary.Point k M))
    (hp : 0 < p.val.1) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C p.val := by
  apply hC.contMDiffAt
  apply mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds
    (show p.val ∈ Ioo 0 δ ×ˢ (univ : Set (IntrinsicBoundary.Point k M)) from
      ⟨⟨hp, p.property.1.2⟩, mem_univ _⟩))
  intro q hq
  exact ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩

/-- A total interior-valued map, using the actual collar whenever it is interior. -/
def collarIntoInterior (x : IntrinsicInterior.Point k M) :
    Band δ (IntrinsicBoundary.Point k M) → IntrinsicInterior.Point k M := by
  classical
  exact fun p => if hp : (𝓡∂ (k + 1)).IsInteriorPoint (C p.val) then ⟨C p.val, hp⟩ else x

include hC hboundary in
/-- The cylinder-to-interior overlap map is the same collar on its positive strip. -/
theorem cylinder_interior_germ (p : Band δ (IntrinsicBoundary.Point k M))
    (x : IntrinsicInterior.Point k M)
    (hpx : cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p =
      interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x) :
    ∃ g : Band δ (IntrinsicBoundary.Point k M) → IntrinsicInterior.Point k M,
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g p ∧ g p = x ∧
        ∀ᶠ q in 𝓝 p,
          cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q =
            interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) (g q) := by
  obtain ⟨hp, hCp⟩ := (interiorIn_eq_cylinder_iff
    (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hboundary x p).mp hpx.symm
  have hi := collar_isInterior_of_pos C hboundary p hp
  let g := collarIntoInterior (δ := δ) C x
  have hgval : (Subtype.val ∘ g) =ᶠ[𝓝 p] C ∘ Subtype.val := by
    have hcc := (contMDiffAt_from_band (I := 𝓡∂ (k + 1)) p).mpr
      (contMDiffAt_collar_of_pos C hC p hp)
    have hn := hcc.continuousAt.eventually
      (IntrinsicInterior.isOpen_interior.mem_nhds hi)
    filter_upwards [hn] with q hq
    change (𝓡∂ (k + 1)).IsInteriorPoint (C q.val) at hq
    simp [g, collarIntoInterior, hq]
  have hgs : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g p := by
    apply IntrinsicInterior.contMDiffAt_iff_val.mpr
    exact ((contMDiffAt_from_band (I := 𝓡∂ (k + 1)) p).mpr
      (contMDiffAt_collar_of_pos C hC p hp)).congr_of_eventuallyEq hgval
  refine ⟨g, hgs, ?_, ?_⟩
  · apply Subtype.ext
    simpa [g, collarIntoInterior, hi, halfOfNonneg] using hCp
  · have hn : ∀ᶠ q : Band δ (IntrinsicBoundary.Point k M) in 𝓝 p, 0 < q.val.1 :=
      ((continuous_fst.comp continuous_subtype_val).continuousAt).eventually
        (Ioi_mem_nhds hp)
    filter_upwards [hn] with q hq
    have hqi := collar_isInterior_of_pos C hboundary q hq
    apply ((interiorIn_eq_cylinder_iff
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) hboundary (g q) q).mpr
      ⟨hq, ?_⟩).symm
    simp [g, collarIntoInterior, hqi, halfOfNonneg]

variable
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)

include hδ hemb hinv in
/-- Every point of the original half collar, including its seam, has a
smooth band-valued inverse describing its original inclusion in the quotient. -/
theorem original_cylinder_germ (p : Half δ (IntrinsicBoundary.Point k M)) :
    ∃ g : M → Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g (C p.val) ∧
        g (C p.val) = halfToBand hδ p ∧
          ∀ᶠ z in 𝓝 (C p.val),
            original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) z =
              cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g z) := by
  obtain ⟨f, hf, hfp, heq⟩ := collar_inverse_germ C hemb hinv p
  let b := halfToBand hδ p
  let g := intoBand b f
  have hfb : f (C p.val) ∈ Band δ (IntrinsicBoundary.Point k M) := by
    rw [hfp]
    exact b.property
  refine ⟨g, contMDiffAt_intoBand b f hf hfb, ?_, ?_⟩
  · apply Subtype.ext
    exact (intoBand_val b f hfb).trans hfp
  · filter_upwards [heq] with z hz
    obtain ⟨q, hqz, hfz⟩ := hz
    have hqband : f z ∈ Band δ (IntrinsicBoundary.Point k M) := by
      rw [hfz]
      exact (halfToBand hδ q).property
    have hgq : g z = halfToBand hδ q :=
      Subtype.ext ((intoBand_val b f hqband).trans hfz)
    rw [hgq, ← hqz]
    exact original_collar_eq_cylinder hδ
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) q

include hδ hemb hboundary hinv in
/-- The interior-to-cylinder transition comes from the produced native inverse germ. -/
theorem interior_cylinder_germ (x : IntrinsicInterior.Point k M)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hxp : interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x =
      cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p) :
    ∃ g : IntrinsicInterior.Point k M → Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g x ∧ g x = p ∧
        ∀ᶠ y in 𝓝 x,
          interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) y =
            cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) (g y) := by
  obtain ⟨hp, hCp⟩ := (interiorIn_eq_cylinder_iff
    (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hboundary x p).mp hxp
  let q := halfOfNonneg p hp.le
  obtain ⟨f, hf, hfq, heq⟩ := original_cylinder_germ hδ C hemb hinv q
  have hqx : C q.val = x.val := hCp
  refine ⟨f ∘ Subtype.val, ?_, ?_, ?_⟩
  · exact hf.comp_of_eq IntrinsicInterior.contMDiff_val.contMDiffAt hqx.symm
  · change f x.val = p
    rw [← hqx, hfq]
    rfl
  · rw [hqx] at heq
    exact continuous_subtype_val.continuousAt.eventually heq

variable (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

include hδ hzero in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem native_open_cover (x : Extension
    (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :
    (∃ u, interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) u = x) ∨
      ∃ p, cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) p = x :=
  interior_cylinder_cover hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
    hzero x

/-- The atlas of the actual attached carrier. Its choices depend only on
the two topological patches; smoothness is proved from the same native collar. -/
@[instance_reducible]
def extensionChartedSpace : ChartedSpace (Model (k + 1))
    (Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) :=
  openCoverChartedSpace
    (isOpenEmbedding_interiorIn hδ
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb hboundary)
    (isOpenEmbedding_cylinder hδ
      (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb)
    (native_open_cover hδ C hzero)

include hC hinv in
/-- The actual quotient has a boundaryless smooth atlas. The hypotheses
are precisely the native collar properties, with no supplied quotient atlas. -/
theorem extension_isManifold :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞
      (Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) := by
  exact openCover_isManifold _ _ (native_open_cover hδ C hzero)
    (interior_cylinder_germ hδ C hemb hboundary hinv)
    (cylinder_interior_germ C hC hboundary)

end Native

end FsFltz.Geometry.IntrinsicCollarGluing
