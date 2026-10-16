import FsFltz.Geometry.Family
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Intrinsic compact smooth bundles on the parameter interval

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:chain`,
163–169, and `sec:lean`, 788–814. Fibres are an actual dependent family
over `[0,1]`, with Mathlib's total space and local trivializations. The
smoothness condition consists of joint open coordinate germs, including
both parameter endpoints and the spatial boundary. It does not choose a
global trivialization or a completion.

The model with corners is explicit: positive-dimensional domains and
ribbons use the half-space model; a zero-dimensional ribbon uses the
boundaryless zero-dimensional model. The lemmas below extract smooth
fibre transition diffeomorphisms from the local extension data.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  (I : ModelWithCorners ℝ (Model d) H) [ChartedSpace H F]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace F E)]

/-- Joint local coordinate extensions of an actual ordered bundle
transition. The open set lies in the full real parameter and ambient
spatial model. Agreement is required only at actual interval parameters
in the chart overlap and actual native spatial coordinates. In particular,
no compatibility or invertibility of extensions off that set is assumed. -/
def HasSmoothTransition (e e' : Trivialization F (π F E)) : Prop :=
  ∀ a : OpenPartialHomeomorph F H, a ∈ atlas H F →
    ∀ t ∈ e.baseSet ∩ e'.baseSet, ∀ x ∈ a.source,
      ∃ (U : Set (ℝ × Model d)) (β : ℝ × Model d → Model d),
        IsOpen U ∧ (t.val, a.extend I x) ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        ∀ s ∈ e.baseSet ∩ e'.baseSet, ∀ z ∈ (a.extend I).target,
          (s.val, z) ∈ U →
          β (s.val, z) = extChartAt I (e.coordChange e' t x)
            (e.coordChange e' s ((a.extend I).symm z))

/-- A compact smooth interval bundle, with its actual Mathlib fibre-bundle
atlas. Smoothness is imposed on every ordered pair of its local charts,
so reverse transitions receive the same extension condition. There is no
global fibre equivalence, presentation, marking, or completion in this
source-side object. -/
class SmoothCompactBundle (E : Parameter → Type*) [∀ t, TopologicalSpace (E t)]
    [TopologicalSpace (TotalSpace F E)] extends FiberBundle F E where
  compact_fiber : CompactSpace F
  hausdorff_fiber : T2Space F
  secondCountable_fiber : SecondCountableTopology F
  smooth_fiber : IsManifold I ∞ F
  smoothTransition : ∀ e ∈ trivializationAtlas', ∀ e' ∈ trivializationAtlas',
    HasSmoothTransition I e e'

attribute [instance] SmoothCompactBundle.compact_fiber
  SmoothCompactBundle.hausdorff_fiber SmoothCompactBundle.secondCountable_fiber
  SmoothCompactBundle.smooth_fiber

variable {I}

omit [∀ t, TopologicalSpace (E t)] in
/-- Freezing a joint open transition germ gives a native smooth fibre
map. The proof uses the actual germ agreement and bundle continuity. -/
theorem HasSmoothTransition.contMDiff {e e' : Trivialization F (π F E)}
    (h : HasSmoothTransition I e e') {t : Parameter}
    (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    ContMDiff I I ∞ (e.coordChange e' t) := by
  intro x
  let a := chartAt H x
  have hx : x ∈ a.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hxU, hβ, heq⟩ := h a (chart_mem_atlas _ x) t ht x hx
  let q : Model d → ℝ × Model d := fun z => (t.val, z)
  have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk contDiff_id
  have hβq : ContDiffAt ℝ ∞ (β ∘ q) (a.extend I x) :=
    (hβ.contDiffAt (hU.mem_nhds hxU)).comp _ hq.contDiffAt
  have hagree : β ∘ q =ᶠ[𝓝[(a.extend I).target] (a.extend I x)]
      (fun z => extChartAt I (e.coordChange e' t x)
        (e.coordChange e' t ((a.extend I).symm z))) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hU.preimage hq.continuous).mem_nhds hxU)]
      with z hz hzU
    exact heq t ht z hz hzU
  have hxTarget : a.extend I x ∈ (a.extend I).target :=
    (a.extend I).map_source (by simpa only [a.extend_source] using hx)
  have hagreePoint := hagree.eq_of_nhdsWithin hxTarget
  rw [a.nhdsWithin_extend_target_eq hx] at hagree
  apply contMDiffAt_iff.mpr
  refine ⟨(e.continuous_coordChange e' ht.1 ht.2).continuousAt, ?_⟩
  exact hβq.contDiffWithinAt.congr_of_eventuallyEq hagree.symm hagreePoint.symm

omit [∀ t, TopologicalSpace (E t)] in
/-- A smoothly varying base parameter in an overlap gives a jointly smooth
family of fibre coordinate changes. This consumes the joint germs, rather
than merely the smoothness of individual time slices, and is the local
regularity needed by base-dependent changes of bundle trivialization. -/
theorem HasSmoothTransition.contMDiff_reparam {e e' : Trivialization F (π F E)}
    (h : HasSmoothTransition I e e') (σ : ℝ → Parameter)
    (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : ℝ × F => e.coordChange e' (σ p.1) p.2) := by
  have hσc : Continuous σ := continuous_induced_rng.mpr hσ.continuous
  have hpair : Continuous (fun p : ℝ × F => (σ p.1, p.2)) :=
    (hσc.comp continuous_fst).prodMk continuous_snd
  have hcont : Continuous (fun p : ℝ × F => e.coordChange e' (σ p.1) p.2) := by
    apply continuous_snd.comp
    apply e'.toOpenPartialHomeomorph.continuousOn.comp_continuous
    · exact e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hpair
        (fun p => e.mem_target.mpr (hoverlap p.1).1)
    · intro p
      rw [e'.mem_source, e.proj_symm_apply' (hoverlap p.1).1]
      exact (hoverlap p.1).2
  intro p
  let a := chartAt H p.2
  let c := chartAt (ModelProd ℝ H) p
  have hx : p.2 ∈ a.source := mem_chart_source _ _
  have hp : p ∈ c.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hxU, hβ, heq⟩ :=
    h a (chart_mem_atlas _ p.2) (σ p.1) (hoverlap p.1) p.2 hx
  let q : ℝ × Model d → ℝ × Model d := fun z => ((σ z.1).val, z.2)
  have hq : ContDiff ℝ ∞ q := (hσ.comp contDiff_fst).prodMk contDiff_snd
  have hxU' : q (c.extend ((𝓘(ℝ, ℝ)).prod I) p) ∈ U := hxU
  have hβq : ContDiffAt ℝ ∞ (β ∘ q) (c.extend ((𝓘(ℝ, ℝ)).prod I) p) :=
    (hβ.contDiffAt (hU.mem_nhds hxU')).comp _ hq.contDiffAt
  have hagree : β ∘ q =ᶠ[𝓝[(c.extend ((𝓘(ℝ, ℝ)).prod I)).target]
      (c.extend ((𝓘(ℝ, ℝ)).prod I) p)]
      (fun z => extChartAt I (e.coordChange e' (σ p.1) p.2)
        (e.coordChange e' (σ z.1) ((a.extend I).symm z.2))) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hU.preimage hq.continuous).mem_nhds hxU')]
      with z hz hzU
    have hz2 : z.2 ∈ (a.extend I).target := by
      change z ∈ (extChartAt ((𝓘(ℝ, ℝ)).prod I) p).target at hz
      rw [extChartAt_prod] at hz
      exact hz.2
    exact heq (σ z.1) (hoverlap z.1) z.2 hz2 hzU
  have hpTarget : c.extend ((𝓘(ℝ, ℝ)).prod I) p ∈
      (c.extend ((𝓘(ℝ, ℝ)).prod I)).target :=
    (c.extend ((𝓘(ℝ, ℝ)).prod I)).map_source
      (by simpa only [c.extend_source] using hp)
  have hagreePoint := hagree.eq_of_nhdsWithin hpTarget
  rw [c.nhdsWithin_extend_target_eq hp] at hagree
  apply contMDiffAt_iff.mpr
  exact ⟨hcont.continuousAt,
    hβq.contDiffWithinAt.congr_of_eventuallyEq hagree.symm hagreePoint.symm⟩

variable [SmoothCompactBundle I (F := F) E]

/-- The native fibre transition is smooth in both directions, because the
bundle atlas supplies local extension germs for both ordered pairs. -/
def transitionDiffeomorph (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) : Diffeomorph I I F F ∞ where
  __ := (e.coordChangeHomeomorph e' ht.1 ht.2).toEquiv
  contMDiff_toFun :=
    (SmoothCompactBundle.smoothTransition e he e' he').contMDiff ht
  contMDiff_invFun :=
    (SmoothCompactBundle.smoothTransition e' he' e he).contMDiff ⟨ht.2, ht.1⟩

@[simp]
theorem transitionDiffeomorph_apply (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : F) :
    transitionDiffeomorph e e' he he' ht x = e.coordChange e' t x := rfl

@[simp]
theorem transitionDiffeomorph_symm_apply (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : F) :
    (transitionDiffeomorph e e' he he' ht).symm x = e'.coordChange e t x := rfl

/-- Boundary preservation is a consequence of transition smoothness in
both directions, not extra boundary transport data supplied to the bundle. -/
theorem transition_preimage_boundary (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    (e.coordChange e' t) ⁻¹' I.boundary F = I.boundary F :=
  Diffeomorph.preimage_boundary (by simp)
    (transitionDiffeomorph (I := I) e e' he he' ht)

end FsFltz.Geometry.IntrinsicSmoothBundle
