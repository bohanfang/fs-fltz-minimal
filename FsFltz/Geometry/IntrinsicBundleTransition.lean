import FsFltz.Geometry.IntrinsicSmoothBundle
import Mathlib.Topology.Order.ProjIcc

/-!
# Composition of joint bundle transition germs

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. These lemmas compose the actual open extension germs. Native
smoothness alone is not used as a replacement for boundary extension.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]

/-- Joint open coordinate germs for a family of native fibre maps on an
actual parameter set. No extension is required to take values in the
native manifold away from the specified coordinate carrier. -/
def HasSmoothFamilyOn (I : ModelWithCorners ℝ (Model d) H)
    (S : Set Parameter) (f : Parameter → F → F) : Prop :=
  ∀ a : OpenPartialHomeomorph F H, a ∈ atlas H F →
    ∀ t ∈ S, ∀ x ∈ a.source,
      ∃ (U : Set (ℝ × Model d)) (β : ℝ × Model d → Model d),
        IsOpen U ∧ (t.val, a.extend I x) ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        ∀ s ∈ S, ∀ z ∈ (a.extend I).target, (s.val, z) ∈ U →
          β (s.val, z) = extChartAt I (f t x) (f s ((a.extend I).symm z))

theorem HasSmoothFamilyOn.mono {S T : Set Parameter} {f : Parameter → F → F}
    (h : HasSmoothFamilyOn I S f) (hTS : T ⊆ S) : HasSmoothFamilyOn I T f := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h a ha t (hTS ht) x hx
  exact ⟨U, β, hU, hp, hβ, fun s hs z hz hsz => heq s (hTS hs) z hz hsz⟩

theorem HasSmoothFamilyOn.congr {S : Set Parameter} {f g : Parameter → F → F}
    (h : HasSmoothFamilyOn I S f) (he : ∀ t ∈ S, ∀ x, f t x = g t x) :
    HasSmoothFamilyOn I S g := by
  intro a ha t ht x hx
  obtain ⟨U, β, hU, hp, hβ, heq⟩ := h a ha t ht x hx
  refine ⟨U, β, hU, hp, hβ, ?_⟩
  intro s hs z hz hsz
  rw [← he t ht x, ← he s hs ((a.extend I).symm z)]
  exact heq s hs z hz hsz

/-- Composition uses the inner map's native continuity to keep actual
intermediate points in a fixed chart, and composes the supplied open
germs on a smaller full ambient neighborhood. The interval clamp is used
only to choose that neighborhood; it is never asserted to be smooth. -/
theorem HasSmoothFamilyOn.comp {S : Set Parameter} (hS : IsOpen S)
    {f g : Parameter → F → F} (hf : HasSmoothFamilyOn I S f)
    (hg : HasSmoothFamilyOn I S g)
    (hfc : ContinuousOn (fun p : Parameter × F => f p.1 p.2) (S ×ˢ univ)) :
    HasSmoothFamilyOn I S (fun t x => g t (f t x)) := by
  intro a ha t ht x hx
  let b := chartAt H (f t x)
  have hfx : f t x ∈ b.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hpU, hβ, heqβ⟩ := hf a ha t ht x hx
  obtain ⟨V, γ, hV, hpV, hγ, heqγ⟩ := hg b (chart_mem_atlas _ _) t ht (f t x) hfx
  let p : ℝ × Model d := (t.val, a.extend I x)
  let q : ℝ × Model d → ℝ × Model d := fun z => (z.1, β z)
  have hq : ContDiffOn ℝ ∞ q U := contDiff_fst.contDiffOn.prodMk hβ
  have hxT : a.extend I x ∈ (a.extend I).target :=
    (a.extend I).map_source (by simpa only [a.extend_source] using hx)
  have hqp : q p = (t.val, b.extend I (f t x)) := by
    refine Prod.ext (by rfl) ?_
    change β (t.val, a.extend I x) = extChartAt I (f t x) (f t x)
    simpa only [(a.extend I).left_inv (by simpa only [a.extend_source] using hx)] using
      heqβ t ht _ hxT hpU
  let k : ℝ × Model d → Parameter × F := fun z =>
    (projIcc 0 1 (by norm_num) z.1, (a.extend I).symm z.2)
  have hkp : k p = (t, x) := by
    change (projIcc 0 1 (by norm_num) t.val,
      (a.extend I).symm (a.extend I x)) = (t, x)
    rw [projIcc_of_mem (by norm_num) t.property,
      (a.extend I).left_inv (by simpa only [a.extend_source] using hx)]
  have hkc : ContinuousAt k p :=
    (continuous_projIcc.comp continuous_fst).continuousAt.prodMk
      ((a.continuousAt_extend_symm (I := I) hx).comp_of_eq
        (continuous_snd.continuousAt (x := p)) rfl)
  have hfcAt : ContinuousAt (fun z : Parameter × F => f z.1 z.2) (t, x) :=
    hfc.continuousAt ((hS.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hsource : {z | f (k z).1 (k z).2 ∈ b.source} ∈ 𝓝 p := by
    exact (hfcAt.comp_of_eq hkc hkp).preimage_mem_nhds
      (b.open_source.mem_nhds (by simpa only [Function.comp_apply, hkp] using hfx))
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hsource
  let W := U ∩ q ⁻¹' V ∩ N
  have hW : IsOpen W :=
    ((hq.continuousOn).isOpen_inter_preimage hU hV).inter hN
  refine ⟨W, γ ∘ q, hW, ⟨⟨hpU, by change q p ∈ V; rw [hqp]; exact hpV⟩, hpN⟩,
    hγ.comp (hq.mono (inter_subset_left.trans inter_subset_left))
      (fun z hz => hz.1.2), ?_⟩
  intro s hs z hz hsz
  have hinner : f s ((a.extend I).symm z) ∈ b.source := by
    have hm := hNsub hsz.2
    change f (projIcc 0 1 (by norm_num) s.val) ((a.extend I).symm z) ∈ b.source at hm
    simpa only [projIcc_of_mem (by norm_num) s.property] using hm
  have hβsz : β (s.val, z) = b.extend I (f s ((a.extend I).symm z)) :=
    heqβ s hs z hz hsz.1.1
  have hmid : β (s.val, z) ∈ (b.extend I).target := by
    rw [hβsz]
    exact (b.extend I).map_source (by simpa only [b.extend_source] using hinner)
  have hback : (b.extend I).symm (β (s.val, z)) = f s ((a.extend I).symm z) := by
    rw [hβsz, (b.extend I).left_inv (by simpa only [b.extend_source] using hinner)]
  simpa only [Function.comp_apply, q, hback] using
    heqγ s hs (β (s.val, z)) hmid hsz.1.2

/-- Joint extension germs are local in the actual base parameter. -/
theorem HasSmoothFamilyOn.of_locally {S : Set Parameter} {f : Parameter → F → F}
    (h : ∀ t ∈ S, ∃ T : Set Parameter, IsOpen T ∧ t ∈ T ∧
      HasSmoothFamilyOn I (S ∩ T) f) : HasSmoothFamilyOn I S f := by
  intro a ha t ht x hx
  obtain ⟨T, hT, htT, hlocal⟩ := h t ht
  obtain ⟨O, hO, hOT⟩ := isOpen_induced_iff.mp hT
  have htO : t.val ∈ O := by change t ∈ Subtype.val ⁻¹' O; rwa [hOT]
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hlocal a ha t ⟨ht, htT⟩ x hx
  refine ⟨U ∩ Prod.fst ⁻¹' O, β, hU.inter (hO.preimage continuous_fst),
    ⟨hpU, htO⟩, hβ.mono inter_subset_left, ?_⟩
  intro s hs z hz hsz
  have hsT : s ∈ T := by rw [← hOT]; exact hsz.2
  exact heq s ⟨hs, hsT⟩ z hz hsz.1

/-- Pull back the actual joint germs along a smooth real parameter map.
All values of the reparametrization lie in the original parameter set. -/
theorem HasSmoothFamilyOn.reparam {S : Set Parameter} {f : Parameter → F → F}
    (h : HasSmoothFamilyOn I S f) (σ : ℝ → Parameter)
    (hσ : ContDiff ℝ ∞ (fun s => (σ s).val)) (hmem : ∀ s, σ s ∈ S) :
    HasSmoothFamilyOn I univ (fun t => f (σ t.val)) := by
  intro a ha t _ x hx
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := h a ha (σ t.val) (hmem t.val) x hx
  let q : ℝ × Model d → ℝ × Model d := fun z => ((σ z.1).val, z.2)
  have hq : ContDiff ℝ ∞ q := (hσ.comp contDiff_fst).prodMk contDiff_snd
  exact ⟨q ⁻¹' U, β ∘ q, hU.preimage hq.continuous, hpU,
    hβ.comp hq.contDiffOn (fun _ hz => hz),
    fun s _ z hz hsz => heq (σ s.val) (hmem s.val) z hz hsz⟩

variable {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace F E)]

omit [∀ t, TopologicalSpace (E t)] in
/-- Native joint continuity comes from the actual topological bundle
charts; it is not a separate smoothness assumption. -/
theorem continuousOn_coordChange (e e' : Trivialization F (π F E)) :
    ContinuousOn (fun p : Parameter × F => e.coordChange e' p.1 p.2)
      ((e.baseSet ∩ e'.baseSet) ×ˢ univ) := by
  apply continuous_snd.comp_continuousOn
  apply e'.toOpenPartialHomeomorph.continuousOn.comp
    (e.toOpenPartialHomeomorph.continuousOn_symm.mono ?_)
  · intro p hp
    rw [e'.mem_source, e.proj_symm_apply' hp.1.1]
    exact hp.1.2
  · intro p hp
    exact e.mem_target.mpr hp.1.1

omit [∀ t, TopologicalSpace (E t)] in
theorem HasSmoothTransition.hasSmoothFamilyOn {e e' : Trivialization F (π F E)}
    (h : HasSmoothTransition I e e') :
    HasSmoothFamilyOn I (e.baseSet ∩ e'.baseSet) (e.coordChange e') := h

variable [SmoothCompactBundle I (F := F) E]

/-- A chart is smoothly compatible with the designated bundle atlas when
its actual transitions in both directions have joint open extension germs. -/
def CompatibleTrivialization (I : ModelWithCorners ℝ (Model d) H)
    (E : Parameter → Type*) [∀ t, TopologicalSpace (E t)]
    [TopologicalSpace (TotalSpace F E)] [SmoothCompactBundle I (F := F) E]
    (e : Trivialization F (π F E)) : Prop :=
  ∀ e' ∈ trivializationAtlas F E,
    HasSmoothTransition I e e' ∧ HasSmoothTransition I e' e

theorem compatibleTrivialization_of_mem {e : Trivialization F (π F E)}
    (he : e ∈ trivializationAtlas F E) : CompatibleTrivialization I E e := by
  intro e' he'
  exact ⟨SmoothCompactBundle.smoothTransition e he e' he',
    SmoothCompactBundle.smoothTransition e' he' e he⟩

/-- Any two compatible charts have smooth joint transition germs. Locally
one original chart is an intermediate chart, including for self transitions. -/
theorem CompatibleTrivialization.hasSmoothTransition {e e' : Trivialization F (π F E)}
    (he : CompatibleTrivialization I E e) (he' : CompatibleTrivialization I E e') :
    HasSmoothTransition I e e' := by
  apply HasSmoothFamilyOn.of_locally
  intro t ht
  let c := trivializationAt F E t
  have hc : c ∈ trivializationAtlas F E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨c.baseSet, c.open_baseSet, htc, ?_⟩
  have hf := (he c hc).1.hasSmoothFamilyOn.mono
    (show (e.baseSet ∩ e'.baseSet) ∩ c.baseSet ⊆ e.baseSet ∩ c.baseSet
      from fun s hs => ⟨hs.1.1, hs.2⟩)
  have hg := (he' c hc).2.hasSmoothFamilyOn.mono
    (show (e.baseSet ∩ e'.baseSet) ∩ c.baseSet ⊆ c.baseSet ∩ e'.baseSet
      from fun s hs => ⟨hs.2, hs.1.2⟩)
  exact (hf.comp ((e.open_baseSet.inter e'.open_baseSet).inter c.open_baseSet) hg
    ((continuousOn_coordChange e c).mono (fun s hs => ⟨⟨hs.1.1.1, hs.1.2⟩, hs.2⟩))).congr
      (fun s hs x => e.coordChange_coordChange c e' hs.1.1 hs.2 x)

/-- Expand the bundle atlas to all compatible charts, on the unchanged
dependent fibres and total space. All pairwise smoothness is proved above. -/
@[instance_reducible]
def compatibleSmoothCompactBundle : SmoothCompactBundle I (F := F) E where
  __ := (inferInstance : SmoothCompactBundle I (F := F) E)
  trivializationAtlas' := {e | CompatibleTrivialization I E e}
  trivialization_mem_atlas' t := compatibleTrivialization_of_mem (trivialization_mem_atlas _ _ t)
  smoothTransition _ he _ he' := he.hasSmoothTransition he'

end FsFltz.Geometry.IntrinsicSmoothBundle
