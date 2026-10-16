import FsFltz.Geometry.IntrinsicBundleLocalCompletionOverlap
import FsFltz.Geometry.IntrinsicCompletionFamilyMap

/-!
# Joint native smoothness of original local completion overlaps

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The overlap uses the original compact bundle
transition and its actual boundary restriction. Its smoothness is derived
on the common relative-open base from the retained interior and cylinder
formulas and the produced real mixed germs.

Native `ContMDiff` smoothness of the total overlap is an intermediate
foundation. It does not, by itself, assert one real open smooth extension
germ for an eventual fixed-manifold interval map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- Original real coordinate germs imply joint native smoothness on the
actual open parameter set. The germs remain stronger than this conclusion. -/
theorem HasSmoothFamilyOn.contMDiffOn_joint {d : ℕ} {H M : Type*}
    [TopologicalSpace H] [TopologicalSpace M]
    {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H M] [IsManifold I ∞ M]
    {S : Set Parameter} (hS : IsOpen S) {f : Parameter → M → M}
    (hf : HasSmoothFamilyOn I S f)
    (hc : ContinuousOn (fun p : Parameter × M => f p.1 p.2) (S ×ˢ univ)) :
    ContMDiffOn ((𝓡∂ 1).prod I) I ∞ (fun p : Parameter × M => f p.1 p.2)
      (S ×ˢ univ) := by
  intro p hp
  let a := chartAt H p.2
  have ha : p.2 ∈ a.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hf a (chart_mem_atlas _ _) p.1 hp.1 p.2 ha
  let q : Parameter × M → ℝ × Model d := fun z => (z.1.val, a.extend I z.2)
  have hq : ContMDiffAt ((𝓡∂ 1).prod I) 𝓘(ℝ, ℝ × Model d) ∞ q p :=
    (contMDiff_subtypeVal_Icc.contMDiffAt.comp p contMDiffAt_fst).prodMk_space
      ((a.contMDiffAt_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ _)) ha).comp
        p contMDiffAt_snd)
  have hcont := hc.continuousAt ((hS.prod isOpen_univ).mem_nhds hp)
  apply contMDiffAt_iff_target.mpr _ |>.contMDiffWithinAt
  refine ⟨hcont, ?_⟩
  apply ((hβ.contDiffAt (hU.mem_nhds hpU)).contMDiffAt.comp p hq).congr_of_eventuallyEq
  filter_upwards [(hS.preimage continuous_fst).mem_nhds hp.1,
    (a.open_source.preimage continuous_snd).mem_nhds ha,
    hq.continuousAt.eventually (hU.mem_nhds hpU)] with z hzS hzA hzU
  change z.2 ∈ a.source at hzA
  simpa only [Function.comp_def, q,
    (a.extend I).left_inv (by simpa only [a.extend_source] using hzA)] using
    (heq z.1 hzS (a.extend I z.2)
      ((a.extend I).map_source (by simpa only [a.extend_source] using hzA)) hzU).symm

/-- Actual target-valued real germs give joint native smoothness after
restricting the real parameter to the original interval. -/
theorem HasSmoothManifoldTargetFamilyOn.contMDiffOn_joint {d r : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold r) {S : Set Parameter}
    (hS : IsOpen S) {v : Parameter → M.Point → N.Point}
    (hv : HasSmoothManifoldTargetFamilyOn M N S v) :
    ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞
      (fun p : Parameter × M.Point => v p.1 p.2) (S ×ˢ univ) := by
  intro p hp
  obtain ⟨U, hpU, β, hβ, heq⟩ := hv p.1 hp.1 p.2
  let q : Parameter × M.Point → ℝ × M.Point := fun z => (z.1.val, z.2)
  have hq : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ q :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  let O : TopologicalSpace.Opens (Parameter × M.Point) :=
    ⟨q ⁻¹' U, U.isOpen.preimage hq.continuous⟩
  let Q : O → U := fun z => ⟨q z.val, z.property⟩
  have hQ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff U Q).mp
    exact hq.comp contMDiff_subtype_val
  let z : O := ⟨p, hpU⟩
  have hg := (hβ.comp hQ).contMDiffAt (x := z)
  have hlocal : ContMDiffAt ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞
      (fun z : O => v z.val.1 z.val.2) z := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.comp continuous_subtype_val).continuousAt.eventually
      (hS.mem_nhds hp.1)] with y hy
    exact (heq y.val.1 hy y.val.2 y.property).symm
  exact ((contMDiffAt_subtype_iff (f := fun p => v p.1 p.2) (x := z)).mp hlocal).contMDiffWithinAt

end FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

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
  (hmix : HasRealMixedGerms (δ := δ) C)

local instance overlapCriterionBandCharts : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance overlapCriterionBandSmooth : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

include hboundary hmix in
/-- Joint native smoothness on a relative-open parameter set is detected
on the original interior and any positive-width strip containing the seam
and every outward radius. No collar width is changed. -/
theorem contMDiffOn_totalFamily_of_end_strip
    {V H N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] [TopologicalSpace N] {I : ModelWithCorners ℝ V H}
    [ChartedSpace H N] {S : Set Parameter} (hS : IsOpen S)
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → N)
    {ε : ℝ} (hε : 0 < ε)
    (hi : ContMDiffOn (familyModel (k + 1)) I ∞
      (f ∘ totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
      (S ×ˢ univ))
    (hc : ContMDiffOn (familyModel (k + 1)) I ∞
      (f ∘ totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
      {p | p.1 ∈ S ∧ p.2.val.1 < ε}) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffOn (familyModel (k + 1)) I ∞ f
      (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) ⁻¹' S) := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  have hint (p : Parameter × IntrinsicInterior.Point k M) (hp : p.1 ∈ S) :
      ContMDiffAt (familyModel (k + 1)) I ∞ f (totalInterior c p) := by
    obtain ⟨g, hg, hgp, heq⟩ := RelativeOpenCover.inverse_germ
      (isOpenEmbedding_totalInterior hδ c (fun t b => hzero t b) hjoint) p
      (IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
        (Or.inl ⟨chartAt _ p, chart_mem_atlas _ p, rfl⟩))
    apply (((hi p ⟨hp, mem_univ _⟩).contMDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp_of_eq hg hgp).congr_of_eventuallyEq
    filter_upwards [heq] with z hz
    change f z = f (totalInterior c (g z))
    rw [hz]
  intro z hz
  rcases totalInterior_cylinder_cover hδ c (fun t b => hzero t b) z with
    ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact (hint p hz).contMDiffWithinAt
  · by_cases hp : p.2.val.1 < ε
    · have hr : Continuous (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
          p.2.val.1) := continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
      obtain ⟨g, hg, hgp, heq⟩ := RelativeOpenCover.inverse_germ
        (isOpenEmbedding_totalCylinder c hjoint) p
        (IsManifold.subset_maximalAtlas (I := familyModel (k + 1)) (n := ∞)
          (Or.inr ⟨chartAt _ p, chart_mem_atlas _ p, rfl⟩))
      have hpc : ContMDiffAt (familyModel (k + 1)) I ∞ (f ∘ totalCylinder c) p :=
        (hc p ⟨hz, hp⟩).contMDiffAt
          (((hS.preimage continuous_fst).inter (isOpen_lt hr continuous_const)).mem_nhds ⟨hz, hp⟩)
      apply ContMDiffAt.contMDiffWithinAt
      apply (hpc.comp_of_eq hg hgp).congr_of_eventuallyEq
      filter_upwards [heq] with z hz
      change f z = f (totalCylinder c (g z))
      rw [hz]
    · have hs : 0 < p.2.val.1 := lt_of_lt_of_le hε (le_of_not_gt hp)
      let q : Half δ (IntrinsicBoundary.Point k M) := halfOfNonneg p.2 hs.le
      have hnot : ¬(𝓡∂ (k + 1)).IsBoundaryPoint (C p.1 q.val) := by
        rw [hboundary]
        exact ne_of_gt hs
      let x : Parameter × IntrinsicInterior.Point k M :=
        (p.1, ⟨C p.1 q.val, ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mpr hnot⟩)
      have he : totalInterior c x = totalCylinder c p :=
        (totalInterior_eq_totalCylinder_iff c hboundary x p).mpr ⟨rfl, hs, rfl⟩
      rw [← he]
      exact (hint x hz).contMDiffWithinAt

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c d : OriginalCompactChart (k := k) (M := M) (E := E)} {t u : Parameter}

/-- The actual common-base open subspace of the retained source total quotient. -/
def overlapSource (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u) :
    TopologicalSpace.Opens F.native.total :=
  ⟨parameter F.native.patches ⁻¹' (F.base ∩ G.base),
    (F.base_open.inter G.base_open).preimage (continuous_parameter F.native.patches)⟩

@[simp]
theorem mem_overlapSource (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (z : F.native.total) : z ∈ F.overlapSource G ↔ parameter F.native.patches z ∈ F.base ∩ G.base :=
  Iff.rfl

/-- The total overlap is the canonical strict slice overlap on each actual
parameter fiber of the original completed total quotient. -/
def totalOverlap (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) : F.overlapSource G → G.native.total :=
  fun z => sliceIn G.native.patches (parameter F.native.patches z.val)
    (F.overlapEquiv G L _ z.property.1 z.property.2
      ((fiberEquiv F.native.patches _).symm ⟨z.val, rfl⟩))

private def overlapExtension (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) : F.native.total → G.native.total := by
  classical
  exact fun z =>
  if h : parameter F.native.patches z ∈ F.base ∩ G.base then F.totalOverlap G L ⟨z, h⟩ else
    match normalEquiv (totalCollar F.native.patches) z with
    | .inl p => original (totalCollar G.native.patches) p
    | .inr p => original (totalCollar G.native.patches) (p.val.val.2.1, p.val.val.2.2.val)

private theorem overlapExtension_original (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hs : s ∈ F.base ∩ G.base) (x : M) :
    F.overlapExtension G L (original (totalCollar F.native.patches) (s, x)) =
      original (totalCollar G.native.patches) (s, c.val.coordChange d.val s x) := by
  have hx : (fiberEquiv F.native.patches s).symm
      ⟨original (totalCollar F.native.patches) (s, x), rfl⟩ = original (F.native.patches s) x := by
    apply (fiberEquiv F.native.patches s).symm_apply_eq.mpr
    apply Subtype.ext
    exact (sliceIn_original F.native.patches s x).symm
  simp only [overlapExtension, parameter_original, dite_eq_left hs, totalOverlap, hx,
    F.overlapEquiv_compact G L s hs.1 hs.2, sliceIn_original]

private theorem overlapExtension_cylinder (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hs : s ∈ F.base ∩ G.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ)
    (hrF : r < F.native.width) (hrG : r < G.native.width) :
    F.overlapExtension G L (totalCylinder F.native.patches
      (s, ⟨(r, b), hrF, mem_univ _⟩)) =
      totalCylinder G.native.patches
        (s, ⟨(r, F.overlapBoundary G s hs.1 hs.2 b), hrG, mem_univ _⟩) := by
  have hx : (fiberEquiv F.native.patches s).symm
      ⟨totalCylinder F.native.patches (s, ⟨(r, b), hrF, mem_univ _⟩), rfl⟩ =
        cylinder (F.native.patches s) ⟨(r, b), hrF, mem_univ _⟩ := by
    apply (fiberEquiv F.native.patches s).symm_apply_eq.mpr
    apply Subtype.ext
    exact (sliceIn_cylinder F.native.patches s _).symm
  simp only [overlapExtension, parameter_totalCylinder, dite_eq_left hs, totalOverlap, hx,
    F.overlapEquiv_cylinder G L s hs.1 hs.2 b r hrF hrG, sliceIn_cylinder]

private def interiorTransition (_F : LocalCompletionFamily P c t) (_G : LocalCompletionFamily P d u)
    (s : Parameter) (x : IntrinsicInterior.Point k M) : IntrinsicInterior.Point k M := by
  classical
  exact
  if h : s ∈ c.val.baseSet ∩ d.val.baseSet then
    ⟨c.val.coordChange d.val s x.val, by
      have hpre := Diffeomorph.preimage_interior (by simp)
        (OriginalBundleLiouvilleLaws.chartTransition c d s h)
      have hx : x.val ∈ (OriginalBundleLiouvilleLaws.chartTransition c d s h) ⁻¹'
          (𝓡∂ (k + 1)).interior M := by rw [hpre]; exact x.property
      exact hx⟩
  else x

private theorem interiorTransition_smooth (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => F.interiorTransition G p.1 p.2)
      ((F.base ∩ G.base) ×ˢ univ) := by
  have hS := c.val.open_baseSet.inter d.val.open_baseSet
  have hf := (SmoothCompactBundle.smoothTransition c.val c.property d.val d.property).hasSmoothFamilyOn
  have hjoint := hf.contMDiffOn_joint hS (continuousOn_coordChange c.val d.val)
  intro p hp
  have hpS : p.1 ∈ c.val.baseSet ∩ d.val.baseSet :=
    ⟨F.base_subset hp.1.1, G.base_subset hp.1.2⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply IntrinsicInterior.contMDiffAt_iff_val.mpr
  have hval : ContMDiff (familyModel (k + 1)) ((𝓡∂ 1).prod (𝓡∂ (k + 1))) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => (p.1, p.2.val)) :=
    contMDiff_id.prodMap IntrinsicInterior.contMDiff_val
  apply (((hjoint (p.1, p.2.val) ⟨hpS, mem_univ _⟩).contMDiffAt
    ((hS.prod isOpen_univ).mem_nhds ⟨hpS, mem_univ _⟩)).comp p (hval p)).congr_of_eventuallyEq
  filter_upwards [(hS.preimage continuous_fst).mem_nhds hpS] with q hq
  change q.1 ∈ c.val.baseSet ∩ d.val.baseSet at hq
  simp only [Function.comp_def, interiorTransition, dite_eq_left hq]

private def boundaryTransition (_F : LocalCompletionFamily P c t) (_G : LocalCompletionFamily P d u) :=
  boundaryFamilyOn (c.val.baseSet ∩ d.val.baseSet) (c.val.coordChange d.val)
    (compatibleTransition_boundary c.val d.val
      (compatibleTrivialization_of_mem c.property) (compatibleTrivialization_of_mem d.property))

private theorem boundaryTransition_smooth (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) :
    ContMDiffOn (familyModel k) 𝓘(ℝ, Model k) ∞
      (fun p : Parameter × IntrinsicBoundary.Point k M => F.boundaryTransition G p.1 p.2)
      ((c.val.baseSet ∩ d.val.baseSet) ×ˢ univ) :=
  ((compatibleTransition_boundary_germs c.val d.val
    (compatibleTrivialization_of_mem c.property) (compatibleTrivialization_of_mem d.property)).native_manifold
      (IntrinsicBoundary.smoothManifold k M) (IntrinsicBoundary.smoothManifold k M)).contMDiffOn_joint
        (IntrinsicBoundary.smoothManifold k M) (IntrinsicBoundary.smoothManifold k M)
        (c.val.open_baseSet.inter d.val.open_baseSet)

local instance localOverlapBandCharts {j : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model j) B]
    (δ : ℝ) : ChartedSpace (Model (j + 1)) (Band δ B) := bandChartedSpace δ

local instance localOverlapBandSmooth {j : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model j) B]
    [IsManifold 𝓘(ℝ, Model j) ∞ B] (δ : ℝ) : IsManifold 𝓘(ℝ, Model (j + 1)) ∞
    (Band δ B) := band_isManifold δ

private def cylinderTransition (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (p : Parameter × Band F.native.width (IntrinsicBoundary.Point k M)) :
    Parameter × Band G.native.width (IntrinsicBoundary.Point k M) := by
  classical
  exact (p.1, if h : p.2.val.1 < G.native.width then
    ⟨(p.2.val.1, F.boundaryTransition G p.1 p.2.val.2), h, mem_univ _⟩ else
    ⟨(0, F.boundaryTransition G p.1 p.2.val.2), G.native.width_pos, mem_univ _⟩)

private theorem cylinderTransition_smooth (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) :
    ContMDiffOn (familyModel (k + 1)) (familyModel (k + 1)) ∞
      (F.cylinderTransition G)
      {p | p.1 ∈ F.base ∩ G.base ∧ p.2.val.1 < G.native.width} := by
  intro p hp
  have hS := c.val.open_baseSet.inter d.val.open_baseSet
  have hpS : p.1 ∈ c.val.baseSet ∩ d.val.baseSet :=
    ⟨F.base_subset hp.1.1, G.base_subset hp.1.2⟩
  have hband : ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞
      (fun p : Parameter × Band F.native.width (IntrinsicBoundary.Point k M) => p.2.val) :=
    (contMDiff_band_val F.native.width).comp contMDiff_snd
  have hr := contMDiff_fst.comp hband
  have hb := contMDiff_snd.comp hband
  have hq : ContMDiff (familyModel (k + 1)) (familyModel k) ∞
      (fun p : Parameter × Band F.native.width (IntrinsicBoundary.Point k M) => (p.1, p.2.val.2)) :=
    contMDiff_fst.prodMk hb
  have hB : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, Model k) ∞
      (fun p : Parameter × Band F.native.width (IntrinsicBoundary.Point k M) =>
        F.boundaryTransition G p.1 p.2.val.2) p :=
    (((F.boundaryTransition_smooth G) (p.1, p.2.val.2) ⟨hpS, mem_univ _⟩).contMDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hpS, mem_univ _⟩)).comp p (hq p)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_fst.prodMk
  apply contMDiffAt_band_iff_val.mpr
  apply ((hr p).prodMk hB).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt hr.continuous continuous_const).mem_nhds hp.2] with q hq
  change q.2.val.1 < G.native.width at hq
  simp only [Function.comp_def, dite_eq_left hq]

private theorem overlapExtension_interior_smooth (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    letI := G.native.totalCharts
    ContMDiffOn (familyModel (k + 1)) (familyModel (k + 1)) ∞
      (F.overlapExtension G L ∘ totalInterior F.native.patches)
      ((F.base ∩ G.base) ×ˢ univ) := by
  let := G.native.totalCharts
  have h := G.native.smooth_totalInterior.comp_contMDiffOn
    (contMDiff_fst.contMDiffOn.prodMk (F.interiorTransition_smooth G))
  apply h.congr
  intro p hp
  have hpS : p.1 ∈ c.val.baseSet ∩ d.val.baseSet :=
    ⟨F.base_subset hp.1.1, G.base_subset hp.1.2⟩
  simpa only [Function.comp_def, totalInterior, interiorTransition, dite_eq_left hpS] using
    F.overlapExtension_original G L p.1 hp.1 p.2.val

private theorem overlapExtension_cylinder_smooth (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    letI := G.native.totalCharts
    ContMDiffOn (familyModel (k + 1)) (familyModel (k + 1)) ∞
      (F.overlapExtension G L ∘ totalCylinder F.native.patches)
      {p | p.1 ∈ F.base ∩ G.base ∧ p.2.val.1 < G.native.width} := by
  let := G.native.totalCharts
  have h := G.native.smooth_totalCylinder.comp_contMDiffOn (F.cylinderTransition_smooth G)
  apply h.congr
  intro p hp
  have he : F.boundaryTransition G p.1 p.2.val.2 = F.overlapBoundary G p.1 hp.1.1 hp.1.2 p.2.val.2 := rfl
  simpa only [Function.comp_def, cylinderTransition, dite_eq_left hp.2, he] using
    F.overlapExtension_cylinder G L p.1 hp.1 p.2.val.2 p.2.val.1 p.2.property.1 hp.2

/-- The canonical total overlap is jointly natively smooth on the actual
common-base open subspace, including either parameter endpoint, the seam,
and every outward radius. No smooth-overlap hypothesis is supplied. -/
theorem smooth_totalOverlap (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    letI := F.native.totalCharts
    letI := G.native.totalCharts
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (F.totalOverlap G L) := by
  let := F.native.totalCharts
  let := G.native.totalCharts
  have h : ContMDiffOn (familyModel (k + 1)) (familyModel (k + 1)) ∞ (F.overlapExtension G L)
      (F.overlapSource G) :=
    contMDiffOn_totalFamily_of_end_strip F.native.width_pos F.native.collar F.native.boundary
      F.native.zero F.native.joint F.native.mixed (F.base_open.inter G.base_open)
      (F.overlapExtension G L) G.native.width_pos
      (F.overlapExtension_interior_smooth G L) (F.overlapExtension_cylinder_smooth G L)
  intro z
  apply ((h z.val z.property).contMDiffAt ((F.overlapSource G).isOpen.mem_nhds z.property)).comp
    z contMDiff_subtype_val.contMDiffAt |>.congr_of_eventuallyEq
  filter_upwards [] with y
  have hy : parameter F.native.patches y.val ∈ F.base ∩ G.base := y.property
  simp only [Function.comp_def, overlapExtension, dite_eq_left hy]

/-- The canonical total overlap preserves the original parameter literally. -/
@[simp]
theorem totalOverlap_parameter (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (z : F.overlapSource G) :
    parameter G.native.patches (F.totalOverlap G L z) = parameter F.native.patches z.val :=
  parameter_sliceIn G.native.patches _ _

/-- Fiber transport in the shared quotient retains the whole original
strict slice map, including all completed points. -/
theorem totalOverlap_sliceIn (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hs : s ∈ F.base ∩ G.base)
    (x : Space (F.native.patches s)) :
    F.totalOverlap G L
      ⟨sliceIn F.native.patches s x, by simpa only [mem_overlapSource, parameter_sliceIn] using hs⟩ =
      sliceIn G.native.patches s (F.overlapEquiv G L s hs.1 hs.2 x) := by
  have hx : (fiberEquiv F.native.patches s).symm ⟨sliceIn F.native.patches s x, parameter_sliceIn _ _ _⟩ = x :=
    (fiberEquiv F.native.patches s).symm_apply_apply x
  rcases jointly_surjective (F.native.patches s) x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · simp only [sliceIn_original] at hx ⊢
    simp only [totalOverlap, parameter_original, hx]
  · simp only [sliceIn_cylinder] at hx ⊢
    simp only [totalOverlap, parameter_totalCylinder, hx]

/-- The canonical total overlap has values in the actual opposite
common-base open subspace. -/
def totalOverlapToOverlap (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) : F.overlapSource G → G.overlapSource F := fun z =>
  ⟨F.totalOverlap G L z, by
    change parameter G.native.patches (F.totalOverlap G L z) ∈ G.base ∩ F.base
    rw [totalOverlap_parameter]
    exact ⟨z.property.2, z.property.1⟩⟩

/-- Reversing the original-chart total overlap is its literal inverse
on the actual original shared quotients. -/
theorem totalOverlapToOverlap_left_inverse (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    Function.LeftInverse (G.totalOverlapToOverlap F L) (F.totalOverlapToOverlap G L) := by
  intro z
  let s := parameter F.native.patches z.val
  have hs : s ∈ F.base ∩ G.base := z.property
  obtain ⟨x, hx⟩ := (fiberEquiv F.native.patches s).surjective ⟨z.val, rfl⟩
  have hz : (⟨sliceIn F.native.patches s x,
      by simpa only [mem_overlapSource, parameter_sliceIn] using hs⟩ : F.overlapSource G) = z := by
    apply Subtype.ext
    exact congrArg (fun q : {z : F.native.total // parameter F.native.patches z = s} => q.val) hx
  rw [← hz]
  apply Subtype.ext
  change G.totalOverlap F L (F.totalOverlapToOverlap G L _) = sliceIn F.native.patches s x
  have he : F.totalOverlapToOverlap G L
      ⟨sliceIn F.native.patches s x, by simpa only [mem_overlapSource, parameter_sliceIn] using hs⟩ =
      ⟨sliceIn G.native.patches s (F.overlapEquiv G L s hs.1 hs.2 x),
        by simpa only [mem_overlapSource, parameter_sliceIn] using
          (show s ∈ G.base ∩ F.base from ⟨hs.2, hs.1⟩)⟩ := by
    apply Subtype.ext
    exact F.totalOverlap_sliceIn G L s hs x
  rw [he, G.totalOverlap_sliceIn F L s (And.symm hs),
    ← F.overlapEquiv_symm G L s hs.1 hs.2]
  exact congrArg (sliceIn F.native.patches s) ((F.overlapEquiv G L s hs.1 hs.2).symm_apply_apply x)

/-- The strict original overlap constructs a native diffeomorphism of
the actual relative-open completed total spaces, in both directions. -/
def totalOverlapDiffeomorph (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) :
    letI := F.native.totalCharts
    letI := G.native.totalCharts
    Diffeomorph (familyModel (k + 1)) (familyModel (k + 1))
      (F.overlapSource G) (G.overlapSource F) ∞ := by
  let := F.native.totalCharts
  let := G.native.totalCharts
  exact {
    toFun := F.totalOverlapToOverlap G L
    invFun := G.totalOverlapToOverlap F L
    left_inv := F.totalOverlapToOverlap_left_inverse G L
    right_inv := G.totalOverlapToOverlap_left_inverse F L
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (G.overlapSource F)
      (F.totalOverlapToOverlap G L)).mp (F.smooth_totalOverlap G L)
    contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (F.overlapSource G)
      (G.totalOverlapToOverlap F L)).mp (G.smooth_totalOverlap F L) }

@[simp]
theorem totalOverlapDiffeomorph_val (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    letI := F.native.totalCharts
    letI := G.native.totalCharts
    ∀ z : F.overlapSource G, (F.totalOverlapDiffeomorph G L z).val = F.totalOverlap G L z :=
  fun _ => rfl

@[simp]
theorem totalOverlapDiffeomorph_symm (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P) :
    letI := F.native.totalCharts
    letI := G.native.totalCharts
    (F.totalOverlapDiffeomorph G L).symm = G.totalOverlapDiffeomorph F L := rfl

/-- On every original compact point, the total overlap retains the
unchanged original bundle coordinate change and actual parameter. -/
theorem totalOverlap_original (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hs : s ∈ F.base ∩ G.base) (x : M) :
    F.totalOverlap G L ⟨original (totalCollar F.native.patches) (s, x), hs⟩ =
      original (totalCollar G.native.patches) (s, c.val.coordChange d.val s x) := by
  simpa only [overlapExtension, parameter_original, dite_eq_left hs] using
    F.overlapExtension_original G L s hs x

/-- The total overlap carries the original common inward strip and the
whole outward cylinder by the literal original boundary coordinate change. -/
theorem totalOverlap_cylinder (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hs : s ∈ F.base ∩ G.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ)
    (hrF : r < F.native.width) (hrG : r < G.native.width) :
    F.totalOverlap G L
      ⟨totalCylinder F.native.patches (s, ⟨(r, b), hrF, mem_univ _⟩), hs⟩ =
      totalCylinder G.native.patches
        (s, ⟨(r, F.overlapBoundary G s hs.1 hs.2 b), hrG, mem_univ _⟩) := by
  simpa only [overlapExtension, parameter_totalCylinder, dite_eq_left hs] using
    F.overlapExtension_cylinder G L s hs b r hrF hrG

/-- Original Liouville data specialize the joint overlap theorem at any
actual parameters and charts, with no selected smooth overlap as input. -/
theorem smooth_original_totalOverlap (L : OriginalBundleLiouvilleLaws P)
    (c d : OriginalCompactChart (k := k) (M := M) (E := E))
    (t u : Parameter) (ht : t ∈ c.val.baseSet) (hu : u ∈ d.val.baseSet) :
    let F := L.localCompletionFamily c t ht
    let G := L.localCompletionFamily d u hu
    letI := F.native.totalCharts
    letI := G.native.totalCharts
    ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ (F.totalOverlap G L) :=
  (L.localCompletionFamily c t ht).smooth_totalOverlap (L.localCompletionFamily d u hu) L

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
