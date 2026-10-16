import FsFltz.Geometry.IntrinsicCompletionFamilyConstruction
import FsFltz.Geometry.IntrinsicCompletionFamilyTopology
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Smooth charts on the original completed total family

Source: `geoemtric-part-fsf.tex`, smooth endpoint conventions, lines 119–122;
`def:pair`, lines 142–158; `def:chain`, lines 163–169; and `sec:lean`,
lines 788–793 and 805–812. The parameter interval retains its manifold
boundary. Native interiors and full cylinders are open patches of the
original attachment topology. Real mixed-transition germs supply their
compatibility, including smooth extensions at both parameter endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

namespace RelativeOpenCover

section Charts

variable {H U V X : Type*} [TopologicalSpace H] [Nonempty H] [TopologicalSpace U]
  [TopologicalSpace V] [TopologicalSpace X] [ChartedSpace H U] [ChartedSpace H V]
  {i : U → X} {j : V → X} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)

/-- Charts pushed through two open patch embeddings, for an arbitrary model. -/
def atlas : Set (OpenPartialHomeomorph X H) :=
  (fun e : OpenPartialHomeomorph U H => e.lift_openEmbedding hi) '' _root_.atlas H U ∪
    (fun e : OpenPartialHomeomorph V H => e.lift_openEmbedding hj) '' _root_.atlas H V

variable (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)

include hcover in
theorem exists_chart (x : X) : ∃ e ∈ atlas (H := H) hi hj, x ∈ e.source := by
  rcases hcover x with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨(chartAt H u).lift_openEmbedding hi,
      Or.inl ⟨chartAt H u, chart_mem_atlas H u, rfl⟩,
      ⟨u, mem_chart_source H u, rfl⟩⟩
  · exact ⟨(chartAt H v).lift_openEmbedding hj,
      Or.inr ⟨chartAt H v, chart_mem_atlas H v, rfl⟩,
      ⟨v, mem_chart_source H v, rfl⟩⟩

/-- Assembly preserves the original topology, including the parameter boundary. -/
@[instance_reducible]
def chartedSpace : ChartedSpace H X where
  atlas := atlas (H := H) hi hj
  chartAt x := (exists_chart (H := H) hi hj hcover x).choose
  mem_chart_source x := (exists_chart (H := H) hi hj hcover x).choose_spec.2
  chart_mem_atlas x := (exists_chart (H := H) hi hj hcover x).choose_spec.1

end Charts

section Smooth

variable {E H U V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace X]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H U] [ChartedSpace H V]
  [IsManifold I ∞ U] [IsManifold I ∞ V]
  {i : U → X} {j : V → X} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)

theorem contMDiffOn_lifted_transition
    (hij : ∀ x y, i x = j y → ∃ g : U → V,
      ContMDiffAt I I ∞ g x ∧ g x = y ∧ ∀ᶠ z in 𝓝 x, i z = j (g z))
    {e : OpenPartialHomeomorph U H} {f : OpenPartialHomeomorph V H}
    (he : e ∈ _root_.atlas H U) (hf : f ∈ _root_.atlas H V) :
    ContMDiffOn I I ∞ ((e.lift_openEmbedding hi).symm.trans (f.lift_openEmbedding hj))
      ((e.lift_openEmbedding hi).symm.trans (f.lift_openEmbedding hj)).source := by
  intro z hz
  change z ∈ e.target ∧ i (e.symm z) ∈ j '' f.source at hz
  obtain ⟨y, hy, hiy⟩ := hz.2
  obtain ⟨g, hg, hgy, heq⟩ := hij (e.symm z) y hiy.symm
  have he' := contMDiffAt_symm_of_mem_maximalAtlas (I := I) (n := ∞)
    (IsManifold.subset_maximalAtlas he) hz.1
  have hf' := contMDiffAt_of_mem_maximalAtlas (I := I) (n := ∞)
    (IsManifold.subset_maximalAtlas hf) hy
  have hcomp : ContMDiffAt I I ∞ (f ∘ g ∘ e.symm) z :=
    hf'.comp_of_eq (hg.comp z he') hgy
  apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  have heq' := he'.continuousAt.eventually heq
  filter_upwards [heq'] with w hw
  change (f.lift_openEmbedding hj) (i (e.symm w)) = f (g (e.symm w))
  rw [hw, OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [Nonempty H] in
private theorem mem_groupoid_of_smooth
    (f : OpenPartialHomeomorph H H) (hf : ContMDiffOn I I ∞ f f.source)
    (hg : ContMDiffOn I I ∞ f.symm f.target) : f ∈ contDiffGroupoid ∞ I := by
  have h := OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn f hf hg
  have hh := (mem_maximalAtlas_iff.mp h) (OpenPartialHomeomorph.refl H) (by simp)
  simpa using hh.2

/-- Smooth germs between the patches construct the manifold with corners. -/
theorem isManifold
    (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)
    (hij : ∀ x y, i x = j y → ∃ g : U → V,
      ContMDiffAt I I ∞ g x ∧ g x = y ∧ ∀ᶠ z in 𝓝 x, i z = j (g z))
    (hji : ∀ y x, j y = i x → ∃ g : V → U,
      ContMDiffAt I I ∞ g y ∧ g y = x ∧ ∀ᶠ z in 𝓝 y, j z = i (g z)) :
    letI := chartedSpace (H := H) hi hj hcover
    IsManifold I ∞ X := by
  let := chartedSpace (H := H) hi hj hcover
  refine { compatible := ?_ }
  intro e f he hf
  change e ∈ atlas (H := H) hi hj at he
  change f ∈ atlas (H := H) hi hj at hf
  rcases he with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;>
    rcases hf with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact (contDiffGroupoid ∞ I).compatible he hf
  · apply mem_groupoid_of_smooth
    · exact contMDiffOn_lifted_transition hi hj hij he hf
    · exact contMDiffOn_lifted_transition hj hi hji hf he
  · apply mem_groupoid_of_smooth
    · exact contMDiffOn_lifted_transition hj hi hji he hf
    · exact contMDiffOn_lifted_transition hi hj hij hf he
  · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    exact (contDiffGroupoid ∞ I).compatible he hf

omit [IsManifold I ∞ U] [IsManifold I ∞ V] in
/-- The first patch is smooth in the assembled atlas with corners. -/
theorem contMDiff_left
    (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)
    (hs : letI := chartedSpace (H := H) hi hj hcover
      IsManifold I ∞ X) :
    letI := chartedSpace (H := H) hi hj hcover
    ContMDiff I I ∞ i := by
  let := chartedSpace (H := H) hi hj hcover
  let : IsManifold I ∞ X := hs
  intro u
  let e := chartAt H u
  let f := e.lift_openEmbedding hi
  have hf : f ∈ IsManifold.maximalAtlas I ∞ X :=
    IsManifold.subset_maximalAtlas (Or.inl ⟨e, chart_mem_atlas H u, rfl⟩)
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas hf
    (show i u ∈ f.source from ⟨u, mem_chart_source H u, rfl⟩)).mpr
  refine ⟨hi.continuous.continuousAt.continuousWithinAt, ?_⟩
  have he : ContMDiffAt I 𝓘(ℝ, E) ∞ (e.extend I) u := contMDiffAt_extChartAt
  apply he.contMDiffWithinAt.congr
  · intro v _
    exact congrArg I (OpenPartialHomeomorph.lift_openEmbedding_apply e hi)
  · exact congrArg I (OpenPartialHomeomorph.lift_openEmbedding_apply e hi)

omit [IsManifold I ∞ U] [IsManifold I ∞ V] in
/-- The full second patch is smooth in that same atlas. -/
theorem contMDiff_right
    (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)
    (hs : letI := chartedSpace (H := H) hi hj hcover
      IsManifold I ∞ X) :
    letI := chartedSpace (H := H) hi hj hcover
    ContMDiff I I ∞ j := by
  let := chartedSpace (H := H) hi hj hcover
  let : IsManifold I ∞ X := hs
  intro v
  let e := chartAt H v
  let f := e.lift_openEmbedding hj
  have hf : f ∈ IsManifold.maximalAtlas I ∞ X :=
    IsManifold.subset_maximalAtlas (Or.inr ⟨e, chart_mem_atlas H v, rfl⟩)
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas hf
    (show j v ∈ f.source from ⟨v, mem_chart_source H v, rfl⟩)).mpr
  refine ⟨hj.continuous.continuousAt.continuousWithinAt, ?_⟩
  have he : ContMDiffAt I 𝓘(ℝ, E) ∞ (e.extend I) v := contMDiffAt_extChartAt
  apply he.contMDiffWithinAt.congr
  · intro w _
    exact congrArg I (OpenPartialHomeomorph.lift_openEmbedding_apply e hj)
  · exact congrArg I (OpenPartialHomeomorph.lift_openEmbedding_apply e hj)

/-- A chart pushed through an open patch gives an actual smooth inverse
germ in the assembled atlas. The germ retains the original patch map. -/
theorem inverse_germ
    [ChartedSpace H X] (u : U)
    (hf : (chartAt H u).lift_openEmbedding hi ∈ IsManifold.maximalAtlas I ∞ X) :
    ∃ g : X → U, ContMDiffAt I I ∞ g (i u) ∧ g (i u) = u ∧
      ∀ᶠ z in 𝓝 (i u), i (g z) = z := by
  let e := chartAt H u
  let f := e.lift_openEmbedding hi
  have hu : u ∈ e.source := mem_chart_source H u
  have hfu : f (i u) = e u := OpenPartialHomeomorph.lift_openEmbedding_apply e hi
  have hfs : i u ∈ f.source := ⟨u, hu, rfl⟩
  have hes := contMDiffAt_symm_of_mem_maximalAtlas (I := I) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas u) (e.map_source hu)
  have hff := contMDiffAt_of_mem_maximalAtlas hf hfs
  refine ⟨e.symm ∘ f, hes.comp_of_eq hff hfu, ?_, ?_⟩
  · change e.symm (f (i u)) = u
    rw [hfu, e.left_inv hu]
  · filter_upwards [f.open_source.mem_nhds hfs] with z hz
    exact f.left_inv hz

/-- Smooth maps out of the assembled manifold are detected on the actual
open patches. This is the descent criterion used by completion comparisons. -/
theorem contMDiff_iff
    (hcover : ∀ x : X, (∃ u, i u = x) ∨ ∃ v, j v = x)
    (hs : letI := chartedSpace (H := H) hi hj hcover
      IsManifold I ∞ X)
    {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] [TopologicalSpace N] {J : ModelWithCorners ℝ F K}
    [ChartedSpace K N] (f : X → N) :
    letI := chartedSpace (H := H) hi hj hcover
    ContMDiff I J ∞ f ↔ ContMDiff I J ∞ (f ∘ i) ∧ ContMDiff I J ∞ (f ∘ j) := by
  let := chartedSpace (H := H) hi hj hcover
  constructor
  · intro hf
    exact ⟨hf.comp (contMDiff_left hi hj hcover hs),
      hf.comp (contMDiff_right hi hj hcover hs)⟩
  · rintro ⟨hfi, hfj⟩ x
    rcases hcover x with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · obtain ⟨g, hg, hgu, heq⟩ := inverse_germ hi u
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞)
          (Or.inl ⟨chartAt H u, chart_mem_atlas H u, rfl⟩))
      apply ((hfi u).comp_of_eq hg hgu).congr_of_eventuallyEq
      filter_upwards [heq] with z hz
      change f z = f (i (g z))
      rw [hz]
    · obtain ⟨g, hg, hgv, heq⟩ := inverse_germ hj v
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞)
          (Or.inr ⟨chartAt H v, chart_mem_atlas H v, rfl⟩))
      apply ((hfj v).comp_of_eq hg hgv).congr_of_eventuallyEq
      filter_upwards [heq] with z hz
      change f z = f (j (g z))
      rw [hz]

end Smooth
end RelativeOpenCover

section Family

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))

local instance familyFullBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance familyFullBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

/-- Product model with the two endpoint boundary charts of `[0,1]`. -/
abbrev familyModel (d : ℕ) := (𝓡∂ 1).prod 𝓘(ℝ, Model d)

/-- The actual source-produced real transition, before restricting parameter. -/
abbrev RealMixedTransition := PartialDiffeomorph
  ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)))
  ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
  (ℝ × (ℝ × IntrinsicBoundary.Point k M))
  (ℝ × IntrinsicInterior.Point k M) ∞

/-- Real smooth germs of the literal mixed patch maps. This property is
proved by the native family producer, before the total atlas is constructed. -/
def HasRealMixedGerms : Prop :=
  ∀ (t : Parameter) (p : ℝ × IntrinsicBoundary.Point k M), p.1 ∈ Ioo 0 δ →
    ∃ A : RealMixedTransition (M := M),
      (t.val, p) ∈ A.source ∧
      (∀ q ∈ A.source, q.2.1 ∈ Ioo 0 δ) ∧
      (∀ q ∈ A.source, (A q).1 = q.1) ∧
      (∀ q ∈ A.target, (A.symm q).1 = q.1) ∧
      (∀ (a : Parameter) (q : Band δ (IntrinsicBoundary.Point k M)),
        (a.val, q.val) ∈ A.source →
        totalInterior (fun t p => C t p.val) (a, (A (a.val, q.val)).2) =
          totalCylinder (fun t p => C t p.val) (a, q)) ∧
      (∀ (a : Parameter) (x : IntrinsicInterior.Point k M), (a.val, x) ∈ A.target →
        ∃ q : Band δ (IntrinsicBoundary.Point k M),
          A.symm (a.val, x) = (a.val, q.val) ∧
          totalCylinder (fun t p => C t p.val) (a, q) =
            totalInterior (fun t p => C t p.val) (a, x))

private def intoFullBand {X : Type*} (p : Band δ (IntrinsicBoundary.Point k M))
    (f : X → ℝ × IntrinsicBoundary.Point k M) (x : X) :
    Band δ (IntrinsicBoundary.Point k M) :=
  if hx : f x ∈ Band δ (IntrinsicBoundary.Point k M) then ⟨f x, hx⟩ else p

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem intoFullBand_val {X : Type*} (p : Band δ (IntrinsicBoundary.Point k M))
    (f : X → ℝ × IntrinsicBoundary.Point k M) (x : X)
    (hx : f x ∈ Band δ (IntrinsicBoundary.Point k M)) :
    (intoFullBand p f x).val = f x := by
  simp only [intoFullBand, hx, ↓reduceDIte]

include hboundary hzero hjoint hδ in
/-- The real cylinder-to-interior germ restricts smoothly to the closed
parameter interval, with the original parameter literally retained. -/
theorem totalCylinder_interior_germ (hmix : HasRealMixedGerms (δ := δ) C)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (x : Parameter × IntrinsicInterior.Point k M)
    (hpx : totalCylinder (fun t p => C t p.val) p =
      totalInterior (fun t p => C t p.val) x) :
    ∃ g : Parameter × Band δ (IntrinsicBoundary.Point k M) →
      Parameter × IntrinsicInterior.Point k M,
      ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g p ∧
      g p = x ∧ ∀ᶠ q in 𝓝 p,
        totalCylinder (fun t p => C t p.val) q =
          totalInterior (fun t p => C t p.val) (g q) := by
  obtain ⟨ht, hp, hc⟩ := (totalInterior_eq_totalCylinder_iff
    (fun t p => C t p.val) hboundary x p).mp hpx.symm
  obtain ⟨A, hpA, hpos, hparam, hparamInv, hforward, hreverse⟩ :=
    hmix p.1 p.2.val ⟨hp, p.2.property.1⟩
  let v : Parameter × Band δ (IntrinsicBoundary.Point k M) →
      ℝ × (ℝ × IntrinsicBoundary.Point k M) := fun q => (q.1.val, q.2.val)
  have hv : ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k))) ∞ v :=
    contMDiff_subtypeVal_Icc.prodMap (contMDiff_band_val δ)
  let g := fun q : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
    (q.1, (A (v q)).2)
  have hg : ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g p :=
    contMDiffAt_fst.prodMk (contMDiffAt_snd.comp _
      ((A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds hpA)).comp p (hv p)))
  have he : totalInterior (fun t p => C t p.val) (g p) =
      totalInterior (fun t p => C t p.val) x := (hforward p.1 p.2 hpA).trans hpx
  have hgp : g p = x := by
    apply (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val)
      (fun t b => hzero t b) hjoint).injective
    exact he
  refine ⟨g, hg, hgp, ?_⟩
  have hn := hv.continuous.continuousAt.eventually (A.open_source.mem_nhds hpA)
  filter_upwards [hn] with q hq
  exact (hforward q.1 q.2 hq).symm

include hboundary hzero hjoint hδ in
/-- The inverse real germ restricts to the same original interior patch.
The band fallback is away from the germ and imposes no nonempty hypothesis. -/
theorem totalInterior_cylinder_germ (hmix : HasRealMixedGerms (δ := δ) C)
    (x : Parameter × IntrinsicInterior.Point k M)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M))
    (hxp : totalInterior (fun t p => C t p.val) x =
      totalCylinder (fun t p => C t p.val) p) :
    ∃ g : Parameter × IntrinsicInterior.Point k M →
      Parameter × Band δ (IntrinsicBoundary.Point k M),
      ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g x ∧
      g x = p ∧ ∀ᶠ y in 𝓝 x,
        totalInterior (fun t p => C t p.val) y =
          totalCylinder (fun t p => C t p.val) (g y) := by
  obtain ⟨ht, hp, hc⟩ := (totalInterior_eq_totalCylinder_iff
    (fun t p => C t p.val) hboundary x p).mp hxp
  obtain ⟨A, hpA, hpos, hparam, hparamInv, hforward, hreverse⟩ :=
    hmix p.1 p.2.val ⟨hp, p.2.property.1⟩
  have hA : A (p.1.val, p.2.val) = (x.1.val, x.2) := by
    have he := (hforward p.1 p.2 hpA).trans hxp.symm
    have h := (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val)
      (fun t b => hzero t b) hjoint).injective he
    exact Prod.ext ((hparam _ hpA).trans (congrArg (fun q => q.1.val) h))
      (congrArg (fun z : Parameter × IntrinsicInterior.Point k M => z.2) h)
  have hxA : (x.1.val, x.2) ∈ A.target := hA ▸ A.map_source hpA
  let v : Parameter × IntrinsicInterior.Point k M → ℝ × IntrinsicInterior.Point k M :=
    fun y => (y.1.val, y.2)
  have hv : ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ v :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  let f := fun y : Parameter × IntrinsicInterior.Point k M => (A.symm (v y)).2
  have hf : ContMDiffAt (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ f x :=
    contMDiffAt_snd.comp _
      ((A.contMDiffOn_invFun.contMDiffAt (A.open_target.mem_nhds hxA)).comp x (hv x))
  have hfx : f x = p.2.val := by
    change (A.symm (x.1.val, x.2)).2 = p.2.val
    rw [← hA]
    exact congrArg Prod.snd (A.toPartialEquiv.left_inv hpA)
  have hn : ∀ᶠ y in 𝓝 x, v y ∈ A.target :=
    hv.continuous.continuousAt.eventually (A.open_target.mem_nhds hxA)
  have hnBand : ∀ᶠ y in 𝓝 x, f y ∈ Band δ (IntrinsicBoundary.Point k M) := by
    filter_upwards [hn] with y hy
    exact ⟨(hpos _ (A.map_target hy)).2, mem_univ _⟩
  let g := fun y : Parameter × IntrinsicInterior.Point k M =>
    (y.1, intoFullBand p.2 f y)
  have hg : ContMDiffAt (familyModel (k + 1)) (familyModel (k + 1)) ∞ g x := by
    apply contMDiffAt_fst.prodMk
    apply contMDiffAt_band_iff_val.mpr
    apply hf.congr_of_eventuallyEq
    filter_upwards [hnBand] with y hy
    exact intoFullBand_val p.2 f y hy
  refine ⟨g, hg, ?_, ?_⟩
  · apply Prod.ext ht
    apply Subtype.ext
    exact (intoFullBand_val p.2 f x (hfx.symm ▸ p.2.property)).trans hfx
  · filter_upwards [hn, hnBand] with y hy hby
    obtain ⟨q, hq, heq⟩ := hreverse y.1 y.2 hy
    have hband : intoFullBand p.2 f y = q := by
      apply Subtype.ext
      exact (intoFullBand_val p.2 f y hby).trans (congrArg Prod.snd hq)
    change totalInterior (fun t p => C t p.val) y =
      totalCylinder (fun t p => C t p.val) (y.1, intoFullBand p.2 f y)
    rw [hband]
    exact heq.symm

/-- The interval charts and spatial patch charts are pushed through the
original open embeddings. No quotient smooth structure is an input. -/
@[instance_reducible]
def totalFamilyChartedSpace :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (Model (k + 1)))
      (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :=
  RelativeOpenCover.chartedSpace
    (H := ModelProd (EuclideanHalfSpace 1) (Model (k + 1)))
    (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val)
      (fun t b => hzero t b) hjoint)
    (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint)
    (totalInterior_cylinder_cover hδ (fun t p => C t p.val) (fun t b => hzero t b))

include hboundary in
/-- Compatibility of the produced real germs gives a smooth total atlas
with boundary only at the two parameter endpoints. -/
theorem totalFamily_isManifold (hmix : HasRealMixedGerms (δ := δ) C) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    IsManifold (familyModel (k + 1)) ∞
      (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) := by
  exact RelativeOpenCover.isManifold _ _
    (totalInterior_cylinder_cover hδ (fun t p => C t p.val) (fun t b => hzero t b))
    (totalInterior_cylinder_germ hδ C hboundary hzero hjoint hmix)
    (totalCylinder_interior_germ hδ C hboundary hzero hjoint hmix)

include hboundary in
/-- Joint smoothness of the unchanged native interior in the total atlas. -/
theorem contMDiff_totalInterior (hmix : HasRealMixedGerms (δ := δ) C) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞
      (totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) := by
  exact RelativeOpenCover.contMDiff_left _ _
    (totalInterior_cylinder_cover hδ (fun t p => C t p.val) (fun t b => hzero t b))
    (totalFamily_isManifold hδ C hboundary hzero hjoint hmix)

include hboundary in
/-- Joint smoothness of the entire half-infinite cylinder, including the seam. -/
theorem contMDiff_totalCylinder (hmix : HasRealMixedGerms (δ := δ) C) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞
      (totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) := by
  exact RelativeOpenCover.contMDiff_right _ _
    (totalInterior_cylinder_cover hδ (fun t p => C t p.val) (fun t b => hzero t b))
    (totalFamily_isManifold hδ C hboundary hzero hjoint hmix)

include hboundary in
/-- A map from the original completed family is jointly smooth exactly
when its literal interior and full-cylinder formulas are smooth. -/
theorem contMDiff_totalFamily_iff (hmix : HasRealMixedGerms (δ := δ) C)
    {F K N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] [TopologicalSpace N] {J : ModelWithCorners ℝ F K}
    [ChartedSpace K N]
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → N) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) J ∞ f ↔
      ContMDiff (familyModel (k + 1)) J ∞
        (f ∘ totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) ∧
      ContMDiff (familyModel (k + 1)) J ∞
        (f ∘ totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) := by
  exact RelativeOpenCover.contMDiff_iff _ _
    (totalInterior_cylinder_cover hδ (fun t p => C t p.val) (fun t b => hzero t b))
    (totalFamily_isManifold hδ C hboundary hzero hjoint hmix) f

include hboundary in
/-- The projection is smooth in the actual total atlas and agrees with
the literal parameter in both native patch formulas. -/
theorem contMDiff_parameter (hmix : HasRealMixedGerms (δ := δ) C) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞
      (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) := by
  apply (contMDiff_totalFamily_iff hδ C hboundary hzero hjoint hmix _).mpr
  constructor
  · simpa only [Function.comp_def, totalInterior, parameter_original] using
      (contMDiff_fst : ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞
        (Prod.fst : Parameter × IntrinsicInterior.Point k M → Parameter))
  · simpa only [Function.comp_def, parameter_totalCylinder] using
      (contMDiff_fst : ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞
        (Prod.fst : Parameter × Band δ (IntrinsicBoundary.Point k M) → Parameter))

end Family

section NativeProducer

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- Native compact family data produce one original smooth total quotient,
with its real endpoint transition germs and the very same slice primitives
and complete Liouville flows. The atlas and its topology are conclusions. -/
theorem exists_native_completionFamily_atlas [CompactSpace M]
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (α t)
            (IntrinsicLiouville.exteriorDerivative (α t)) x.val))) :
    ∃ (δ : ℝ) (hδ : 0 < δ)
      (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
      (hemb : ∀ t, IsOpenEmbedding
        (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
      (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
        (C t) (Half δ (IntrinsicBoundary.Point k M)))
      (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
        (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
      (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
        ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
            ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
      (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)
      (hjoint : IsOpenEmbedding (totalCollar
        (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))),
    HasRealMixedGerms (δ := δ) C ∧
      let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)
      let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
      let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
      letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
      letI := totalFamilyChartedSpace hδ C hzero hjoint
      IsManifold (familyModel (k + 1)) ∞ (TotalSpace c) ∧
        T2Space (TotalSpace c) ∧ SecondCountableTopology (TotalSpace c) ∧
        ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalInterior c) ∧
        ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (totalCylinder c) ∧
        ContMDiff (familyModel (k + 1)) (𝓡∂ 1) ∞ (parameter c) ∧
        (∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
          (fun x => -IntrinsicLiouville.liouvilleVector (α t)
            (IntrinsicLiouville.exteriorDerivative (α t)) x) (Ico 0 δ)) ∧
        ∃ lam : ∀ t, (X t).Form 1,
          (∀ t, (X t).IsSmoothForm (lam t)) ∧
          (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            (fun x => (lam t (original (c t) x)).compContinuousLinearMap
              (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original (c t)) x)) = α t) ∧
          (∀ t, P.pullback (X t) (cylinder (c t)) (lam t) = cylinderPrimitive δ (α t)) ∧
          (∀ t x, (X t).Nondegenerate ((X t).exteriorDerivative (lam t)) x) ∧
          (∀ t, Nonempty (CompleteLiouvilleFlow (X t) ((X t).liouvilleVector (lam t)))) ∧
          P.IsSmoothIntervalFormFamily (fun t => P.pullback (X t) (cylinder (c t)) (lam t)) := by
  obtain ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hode, hlam,
      D, i, eB, cReal, J, hi, hiemb, hbij, hcoord, hc, hJ, hdiff, hsquare, hmix⟩ :=
    exists_native_completionFamily_with_mixed_germs α hα hnd hout
  have hmixed : HasRealMixedGerms (δ := δ) C := by
    intro t p hp
    obtain ⟨A, hpA, hpos, hparam, hparamInv, hnative, hforward, hreverse⟩ := hmix t p hp
    exact ⟨A, hpA, hpos, hparam, hparamInv, hforward, hreverse⟩
  refine ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed, ?_⟩
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  refine ⟨totalFamily_isManifold hδ C hboundary hzero hjoint hmixed,
    t2Space_totalSpace hδ c hjoint,
    secondCountableTopology_totalSpace hδ c (fun t b => hzero t b) hjoint,
    contMDiff_totalInterior hδ C hboundary hzero hjoint hmixed,
    contMDiff_totalCylinder hδ C hboundary hzero hjoint hmixed,
    contMDiff_parameter hδ C hboundary hzero hjoint hmixed, hode, ?_⟩
  rcases hlam with ⟨lam, hsmooth, hnative, hcylinder, hnondeg, hflows, hfamily,
    hcylEmb, hintEmb, hcover, hfiber⟩
  exact ⟨lam, hsmooth, hnative, hcylinder, hnondeg, hflows, hfamily⟩

end NativeProducer

end FsFltz.Geometry.IntrinsicCompletionGluing
