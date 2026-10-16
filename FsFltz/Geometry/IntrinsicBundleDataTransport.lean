import FsFltz.Geometry.IntrinsicBundleTrivialization
import FsFltz.Geometry.IntrinsicPairFamilyTransport

/-!
# Transport of actual bundle values and target maps

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. Local data are functions on the original dependent total space.
Their local coordinate germs transport through a compatible chart by
composition of the actual joint open extensions. No global data germ is
an input. This module treats values and maps; covariant one-form transport
and the boundary-valued ribbon conjugation are separate operations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]

/-- Joint value germs in the source coordinates, across the native boundary
and the parameter endpoints. The codomain can in particular be `ℝ`. -/
def HasSmoothValueFamilyOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : ModelWithCorners ℝ (Model d) H) (S : Set Parameter)
    (v : Parameter → F → V) : Prop :=
  ∀ a : OpenPartialHomeomorph F H, a ∈ atlas H F →
    ∀ t ∈ S, ∀ x ∈ a.source,
      ∃ (U : Set (ℝ × Model d)) (β : ℝ × Model d → V),
        IsOpen U ∧ (t.val, a.extend I x) ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        ∀ s ∈ S, ∀ y ∈ a.source, (s.val, a.extend I y) ∈ U →
          β (s.val, a.extend I y) = v s y

/-- A local target map extends into the actual target manifold, including
across both kinds of source boundary. This is stronger than mere smooth
coordinate values, as required for ribbon maps. -/
def HasSmoothTargetFamilyOn {r : ℕ} (I : ModelWithCorners ℝ (Model d) H)
    (N : SmoothManifold r) (S : Set Parameter) (v : Parameter → F → N.Point) : Prop :=
  ∀ a : OpenPartialHomeomorph F H, a ∈ atlas H F →
    ∀ t ∈ S, ∀ x ∈ a.source,
      ∃ U : TopologicalSpace.Opens (ℝ × Model d),
        (t.val, a.extend I x) ∈ U ∧ ∃ β : U → N.Point,
          ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, Model r) ∞ β ∧
          ∀ s ∈ S, ∀ y ∈ a.source, ∀ h : (s.val, a.extend I y) ∈ U,
            β ⟨(s.val, a.extend I y), h⟩ = v s y

/-- An actual transition germ can be shrunk so that its native image lies
in the fixed target chart used at the center. The real interval projection
is used only for this topological shrinking. -/
theorem HasSmoothFamilyOn.exists_coordinate_lift {S : Set Parameter} (hS : IsOpen S)
    {f : Parameter → F → F} (hf : HasSmoothFamilyOn I S f)
    (hfc : ContinuousOn (fun p : Parameter × F => f p.1 p.2) (S ×ˢ univ))
    (a : OpenPartialHomeomorph F H) (ha : a ∈ atlas H F)
    (t : Parameter) (ht : t ∈ S) (x : F) (hx : x ∈ a.source) :
    ∃ (U : Set (ℝ × Model d)) (β : ℝ × Model d → Model d),
      IsOpen U ∧ (t.val, a.extend I x) ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
      ∀ s ∈ S, ∀ y ∈ a.source, (s.val, a.extend I y) ∈ U →
        f s y ∈ (chartAt H (f t x)).source ∧
        β (s.val, a.extend I y) = (chartAt H (f t x)).extend I (f s y) := by
  let b := chartAt H (f t x)
  let p : ℝ × Model d := (t.val, a.extend I x)
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hf a ha t ht x hx
  let k : ℝ × Model d → Parameter × F := fun z =>
    (projIcc 0 1 (by norm_num) z.1, (a.extend I).symm z.2)
  have hkp : k p = (t, x) := by
    change (projIcc 0 1 (by norm_num) t.val, (a.extend I).symm (a.extend I x)) = (t, x)
    rw [projIcc_of_mem (by norm_num) t.property,
      (a.extend I).left_inv (by simpa only [a.extend_source] using hx)]
  have hkc : ContinuousAt k p :=
    (continuous_projIcc.comp continuous_fst).continuousAt.prodMk
      ((a.continuousAt_extend_symm (I := I) hx).comp_of_eq
        (continuous_snd.continuousAt (x := p)) rfl)
  have hfcAt : ContinuousAt (fun z : Parameter × F => f z.1 z.2) (t, x) :=
    hfc.continuousAt ((hS.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hsource : {z | f (k z).1 (k z).2 ∈ b.source} ∈ 𝓝 p :=
    (hfcAt.comp_of_eq hkc hkp).preimage_mem_nhds
      (b.open_source.mem_nhds (by simpa only [Function.comp_apply, hkp] using
        (mem_chart_source H (f t x))))
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hsource
  refine ⟨U ∩ N, β, hU.inter hN, ⟨hpU, hpN⟩, hβ.mono inter_subset_left, ?_⟩
  intro s hs y hy hsy
  have hin : f s y ∈ b.source := by
    have h := hNsub hsy.2
    change f (projIcc 0 1 (by norm_num) s.val) ((a.extend I).symm (a.extend I y)) ∈ b.source at h
    simpa only [projIcc_of_mem (by norm_num) s.property,
      (a.extend I).left_inv (by simpa only [a.extend_source] using hy)] using h
  refine ⟨hin, ?_⟩
  simpa only [extChartAt, (a.extend I).left_inv (by simpa only [a.extend_source] using hy)] using
    heq s hs (a.extend I y)
      ((a.extend I).map_source (by simpa only [a.extend_source] using hy)) hsy.1

theorem HasSmoothValueFamilyOn.comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set Parameter} (hS : IsOpen S) {f : Parameter → F → F}
    (hf : HasSmoothFamilyOn I S f)
    (hfc : ContinuousOn (fun p : Parameter × F => f p.1 p.2) (S ×ˢ univ))
    {v : Parameter → F → V} (hv : HasSmoothValueFamilyOn I S v) :
    HasSmoothValueFamilyOn I S (fun t x => v t (f t x)) := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hpU, hβ, heqβ⟩ := hf.exists_coordinate_lift hS hfc a ha t ht x hx
  let b := chartAt H (f t x)
  obtain ⟨W, γ, hW, hpW, hγ, heqγ⟩ :=
    hv b (chart_mem_atlas _ _) t ht (f t x) (mem_chart_source _ _)
  let q : ℝ × Model d → ℝ × Model d := fun z => (z.1, β z)
  have hq : ContDiffOn ℝ ∞ q U := contDiff_fst.contDiffOn.prodMk hβ
  have hqp : q (t.val, a.extend I x) = (t.val, b.extend I (f t x)) :=
    Prod.ext rfl (heqβ t ht x hx hpU).2
  refine ⟨U ∩ q ⁻¹' W, γ ∘ q, hq.continuousOn.isOpen_inter_preimage hU hW,
    ⟨hpU, by change q (t.val, a.extend I x) ∈ W; rw [hqp]; exact hpW⟩,
    hγ.comp (hq.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
  intro s hs y hy hsy
  obtain ⟨hin, he⟩ := heqβ s hs y hy hsy.1
  have hmid : (s.val, b.extend I (f s y)) ∈ W := by
    have h := hsy.2
    change (s.val, β (s.val, a.extend I y)) ∈ W at h
    rwa [he] at h
  change γ (s.val, β (s.val, a.extend I y)) = _
  rw [he]
  exact heqγ s hs (f s y) hin hmid

theorem HasSmoothTargetFamilyOn.comp {r : ℕ} (N : SmoothManifold r)
    {S : Set Parameter} (hS : IsOpen S) {f : Parameter → F → F}
    (hf : HasSmoothFamilyOn I S f)
    (hfc : ContinuousOn (fun p : Parameter × F => f p.1 p.2) (S ×ˢ univ))
    {v : Parameter → F → N.Point} (hv : HasSmoothTargetFamilyOn I N S v) :
    HasSmoothTargetFamilyOn I N S (fun t x => v t (f t x)) := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hpU, hβ, heqβ⟩ := hf.exists_coordinate_lift hS hfc a ha t ht x hx
  let b := chartAt H (f t x)
  obtain ⟨W, hpW, γ, hγ, heqγ⟩ :=
    hv b (chart_mem_atlas _ _) t ht (f t x) (mem_chart_source _ _)
  let q : ℝ × Model d → ℝ × Model d := fun z => (z.1, β z)
  have hq : ContDiffOn ℝ ∞ q U := contDiff_fst.contDiffOn.prodMk hβ
  let O : TopologicalSpace.Opens (ℝ × Model d) :=
    ⟨U ∩ q ⁻¹' W, hq.continuousOn.isOpen_inter_preimage hU W.isOpen⟩
  let Q : O → W := fun z => ⟨q z.val, z.property.2⟩
  have hQ : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model d) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff W Q).mp
    intro z
    exact ((hq.contDiffAt (hU.mem_nhds z.property.1)).contMDiffAt).comp
      z contMDiff_subtype_val.contMDiffAt
  have hqp : q (t.val, a.extend I x) = (t.val, b.extend I (f t x)) :=
    Prod.ext rfl (heqβ t ht x hx hpU).2
  refine ⟨O, ⟨hpU, by change q (t.val, a.extend I x) ∈ W; rw [hqp]; exact hpW⟩,
    γ ∘ Q, hγ.comp hQ, ?_⟩
  intro s hs y hy hsy
  obtain ⟨hin, he⟩ := heqβ s hs y hy hsy.1
  have hmid : (s.val, b.extend I (f s y)) ∈ W := by
    have h := hsy.2
    change (s.val, β (s.val, a.extend I y)) ∈ W at h
    rwa [he] at h
  have harg : Q ⟨(s.val, a.extend I y), hsy⟩ =
      ⟨(s.val, b.extend I (f s y)), hmid⟩ := Subtype.ext (Prod.ext rfl he)
  exact (congrArg γ harg).trans (heqγ s hs (f s y) hin hmid)

theorem HasSmoothValueFamilyOn.mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S T : Set Parameter} {v : Parameter → F → V}
    (h : HasSmoothValueFamilyOn I S v) (hTS : T ⊆ S) : HasSmoothValueFamilyOn I T v := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h a ha t (hTS ht) x hx
  exact ⟨U, β, hU, hp, hβ, fun s hs y hy hsy => heq s (hTS hs) y hy hsy⟩

theorem HasSmoothValueFamilyOn.congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set Parameter} {v w : Parameter → F → V}
    (h : HasSmoothValueFamilyOn I S v) (he : ∀ t ∈ S, ∀ x, v t x = w t x) :
    HasSmoothValueFamilyOn I S w := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h a ha t ht x hx
  exact ⟨U, β, hU, hp, hβ, fun s hs y hy hsy => (heq s hs y hy hsy).trans (he s hs y)⟩

theorem HasSmoothTargetFamilyOn.mono {r : ℕ} {N : SmoothManifold r}
    {S T : Set Parameter} {v : Parameter → F → N.Point}
    (h : HasSmoothTargetFamilyOn I N S v) (hTS : T ⊆ S) :
    HasSmoothTargetFamilyOn I N T v := by
  intro a ha t ht x hx
  obtain ⟨U, hp, β, hβ, heq⟩ := h a ha t (hTS ht) x hx
  exact ⟨U, hp, β, hβ, fun s hs y hy hsy => heq s (hTS hs) y hy hsy⟩

theorem HasSmoothTargetFamilyOn.congr {r : ℕ} {N : SmoothManifold r}
    {S : Set Parameter} {v w : Parameter → F → N.Point}
    (h : HasSmoothTargetFamilyOn I N S v) (he : ∀ t ∈ S, ∀ x, v t x = w t x) :
    HasSmoothTargetFamilyOn I N S w := by
  intro a ha t ht x hx
  obtain ⟨U, hp, β, hβ, heq⟩ := h a ha t ht x hx
  exact ⟨U, hp, β, hβ, fun s hs y hy hsy => (heq s hs y hy hsy).trans (he s hs y)⟩

theorem HasSmoothValueFamilyOn.of_locally {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set Parameter} {v : Parameter → F → V}
    (h : ∀ t ∈ S, ∃ T : Set Parameter, IsOpen T ∧ t ∈ T ∧
      HasSmoothValueFamilyOn I (S ∩ T) v) : HasSmoothValueFamilyOn I S v := by
  intro a ha t ht x hx
  obtain ⟨T, hT, htT, hlocal⟩ := h t ht
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  have htO : t.val ∈ O := by change t ∈ Subtype.val ⁻¹' O; rwa [hOT]
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hlocal a ha t ⟨ht, htT⟩ x hx
  refine ⟨U ∩ Prod.fst ⁻¹' O, β, hU.inter (hO.preimage continuous_fst),
    ⟨hpU, htO⟩, hβ.mono inter_subset_left, ?_⟩
  intro s hs y hy hsy
  have hsT : s ∈ T := by rw [← hOT]; exact hsy.2
  exact heq s ⟨hs, hsT⟩ y hy hsy.1

theorem HasSmoothTargetFamilyOn.of_locally {r : ℕ} {N : SmoothManifold r}
    {S : Set Parameter} {v : Parameter → F → N.Point}
    (h : ∀ t ∈ S, ∃ T : Set Parameter, IsOpen T ∧ t ∈ T ∧
      HasSmoothTargetFamilyOn I N (S ∩ T) v) : HasSmoothTargetFamilyOn I N S v := by
  intro a ha t ht x hx
  obtain ⟨T, hT, htT, hlocal⟩ := h t ht
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  have htO : t.val ∈ O := by change t ∈ Subtype.val ⁻¹' O; rwa [hOT]
  obtain ⟨U, hpU, β, hβ, heq⟩ := hlocal a ha t ⟨ht, htT⟩ x hx
  let W : TopologicalSpace.Opens (ℝ × Model d) :=
    ⟨(U : Set (ℝ × Model d)) ∩ Prod.fst ⁻¹' O, U.isOpen.inter (hO.preimage continuous_fst)⟩
  let j : W → U := fun p => ⟨p.val, p.property.1⟩
  have hj : ContMDiff 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model d) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff U j).mp contMDiff_subtype_val
  refine ⟨W, ⟨hpU, htO⟩, β ∘ j, hβ.comp hj, ?_⟩
  intro s hs y hy hsy
  have hsT : s ∈ T := by rw [← hOT]; exact hsy.2
  exact heq s ⟨hs, hsT⟩ y hy hsy.1

variable {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace F E)] [SmoothCompactBundle I (F := F) E]

/-- The coordinate expression of an actual original total-space value.
Only parameters in the chart base are used by the germ predicates. -/
def chartValue {V : Type*} (e : Trivialization F (π F E))
    (v : TotalSpace F E → V) : Parameter → F → V :=
  fun t x => v (e.toOpenPartialHomeomorph.symm (t, x))

omit [∀ t, TopologicalSpace (E t)] in
/-- Actual bundle chart inverses give the exact precomposition identity.
There is no separately supplied coherence certificate for values or maps. -/
theorem chartValue_coordChange {V : Type*} (e e' : Trivialization F (π F E))
    (v : TotalSpace F E → V) {t : Parameter}
    (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : F) :
    chartValue e' v t (e.coordChange e' t x) = chartValue e v t x := by
  let p := e.toOpenPartialHomeomorph.symm (t, x)
  have hp : p.proj = t := e.proj_symm_apply' ht.1
  have hp' : p ∈ e'.source := by rw [e'.mem_source, hp]; exact ht.2
  have hval : e' p = (t, e.coordChange e' t x) :=
    Prod.ext ((e'.coe_fst' (by rw [hp]; exact ht.2)).trans hp) rfl
  unfold chartValue
  rw [← hval]
  exact congrArg v (e'.toOpenPartialHomeomorph.left_inv hp')

variable (I) in
/-- Local value germs are attached to the actual original bundle data in
each designated atlas chart, rather than to a chosen global presentation. -/
def HasSmoothBundleValues {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : TotalSpace F E → V) : Prop :=
  ∀ e ∈ trivializationAtlas F E, HasSmoothValueFamilyOn I e.baseSet (chartValue e v)

variable (I) in
/-- Original bundle maps into an actual fixed target carry local
manifold-valued germs in the designated bundle atlas. -/
def HasSmoothBundleTarget {r : ℕ} (N : SmoothManifold r) (v : TotalSpace F E → N.Point) : Prop :=
  ∀ e ∈ trivializationAtlas F E, HasSmoothTargetFamilyOn I N e.baseSet (chartValue e v)

/-- Original local value germs transport into any compatible chart.
The proof uses one original atlas chart near each parameter and composes
the actual smooth transition germs. -/
theorem HasSmoothBundleValues.in_compatible_chart {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {v : TotalSpace F E → V}
    (hv : HasSmoothBundleValues I v) (e : Trivialization F (π F E))
    (he : CompatibleTrivialization I E e) :
    HasSmoothValueFamilyOn I e.baseSet (chartValue e v) := by
  apply HasSmoothValueFamilyOn.of_locally
  intro t ht
  let c := trivializationAt F E t
  have hc : c ∈ trivializationAtlas F E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨c.baseSet, c.open_baseSet, htc, ?_⟩
  exact ((hv c hc).mono inter_subset_right |>.comp (e.open_baseSet.inter c.open_baseSet)
    (he c hc).1.hasSmoothFamilyOn (continuousOn_coordChange e c)).congr
      (fun s hs x => chartValue_coordChange e c v hs x)

/-- Original target-valued local germs likewise survive the constructed
compatible chart, retaining every actual target point. -/
theorem HasSmoothBundleTarget.in_compatible_chart {r : ℕ} {N : SmoothManifold r}
    {v : TotalSpace F E → N.Point} (hv : HasSmoothBundleTarget I N v)
    (e : Trivialization F (π F E)) (he : CompatibleTrivialization I E e) :
    HasSmoothTargetFamilyOn I N e.baseSet (chartValue e v) := by
  apply HasSmoothTargetFamilyOn.of_locally
  intro t ht
  let c := trivializationAt F E t
  have hc : c ∈ trivializationAtlas F E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨c.baseSet, c.open_baseSet, htc, ?_⟩
  exact ((hv c hc).mono inter_subset_right |>.comp N (e.open_baseSet.inter c.open_baseSet)
    (he c hc).1.hasSmoothFamilyOn (continuousOn_coordChange e c)).congr
      (fun s hs x => chartValue_coordChange e c v hs x)

/-- One constructed global smooth chart presents the original bundle
values and maps jointly smoothly at every parameter. -/
theorem exists_global_chart_with_values_and_target {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ} (N : SmoothManifold r)
    (v : TotalSpace F E → V) (hv : HasSmoothBundleValues I v)
    (j : TotalSpace F E → N.Point) (hj : HasSmoothBundleTarget I N j) :
    ∃ e : Trivialization F (π F E), e.baseSet = univ ∧
      CompatibleTrivialization I E e ∧
      HasSmoothValueFamilyOn I univ (chartValue e v) ∧
      HasSmoothTargetFamilyOn I N univ (chartValue e j) := by
  obtain ⟨e, hbase, he⟩ := exists_global_smooth_trivialization (I := I) (F := F) (E := E)
  refine ⟨e, hbase, he, ?_, ?_⟩
  · simpa only [hbase] using hv.in_compatible_chart e he
  · simpa only [hbase] using hj.in_compatible_chart e he

end FsFltz.Geometry.IntrinsicSmoothBundle
