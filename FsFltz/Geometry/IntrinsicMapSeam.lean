import FsFltz.Geometry.IntrinsicLiouvilleSeam

/-!
# Manifold-valued map germs on the same native Liouville seam

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–161, and
`sec:lean`, lines 788–814. Native primitive extensions produce the collar
field germs, while source-map chart germs produce the extended map. Target
chart membership on the prescribed half-strip follows from continuity of
the actual source map and collar, so chart coordinate agreement recovers
literal map agreement. No two-sided collar or map germ is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_seam_vector_germ_of_primitive
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ z, Nondegenerate (exteriorDerivative α) z)
    (x : IntrinsicBoundary.Point k M)
    (hout : 0 < (show ℝ from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ y, C (0, y) = y.val)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (φ : M → F)
    (hφ : ∃ (β : Model (k + 1) → F) (A : Set (Model (k + 1))),
      IsOpen A ∧ (IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val ∈ A ∧
      ContDiffOn ℝ ∞ β A ∧
      β =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
        (fun z => φ (((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm z))) :
    ∃ (a : ℝ × IntrinsicBoundary.Point k M → F)
      (W : Set (ℝ × IntrinsicBoundary.Point k M)),
      IsOpen W ∧ (0, x) ∈ W ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞ a W ∧
      EqOn a (fun p => φ (C p)) (W ∩ (Ico 0 δ ×ˢ univ)) := by
  let c := IntrinsicBoundary.chartAt x
  have hx : x ∈ c.chart.source := IntrinsicBoundary.mem_chartAt_source x
  have hex : x.val ∈ c.ambient.source := by
    have h := hx
    rwa [c.source_eq] at h
  obtain ⟨g, V, ε, hg, hV, hxV, hVtarget, hε, _, hgzero, _, _, _, hmatch⟩ :=
    IntrinsicCollar.exists_seam_coordinate_germ_of_scalar_extensions c hx
      (fun z => -liouvilleVector α (exteriorDerivative α) z) C hδ hzero hode
      (inward_liouvilleVector_scalar_extensions_of_primitive α hα hnd
        c.ambient c.mem_atlas x.val hex)
      (inward_of_normalDefiningFunction_outward c.mem_atlas hex
        (liouvilleVector α (exteriorDerivative α)) hout)
  obtain ⟨β, A, hA, hxA, hβ, hβeq⟩ := hφ
  let S : Set (ℝ × IntrinsicBoundary.Point k M) := univ ×ˢ c.chart.source
  let P : ℝ × IntrinsicBoundary.Point k M → ℝ × Model k :=
    fun p => (p.1, c.chart p.2)
  let G : ℝ × IntrinsicBoundary.Point k M → Model (k + 1) := g ∘ P
  let a : ℝ × IntrinsicBoundary.Point k M → F := β ∘ G
  have hS : IsOpen S := isOpen_univ.prod c.chart.open_source
  have hxS : (0, x) ∈ S := ⟨mem_univ _, hx⟩
  have hc : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ c.chart c.chart.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨c, rfl⟩)
  have hP : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ × Model k) ∞ P S :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (hc.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      𝓘(ℝ, Model (k + 1)) ∞ G S := hg.contMDiff.comp_contMDiffOn hP
  have hcenter : G (0, x) = c.ambient.extend (𝓡∂ (k + 1)) x.val := by
    change g (0, c.chart x) = _
    rw [hgzero, c.toFun_eq x hx]
    apply boundaryInsert_drop
    have hex : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
    exact (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero c.mem_atlas hex).mp x.property
  have hGA : IsOpen (S ∩ G ⁻¹' A) :=
    hG.continuousOn.isOpen_inter_preimage hS hA
  have hxGA : (0, x) ∈ S ∩ G ⁻¹' A := ⟨hxS, by
    change G (0, x) ∈ A
    rwa [hcenter]⟩
  have ha : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞ a
      (S ∩ G ⁻¹' A) :=
    hβ.contMDiffOn.comp (hG.mono inter_subset_left) (fun _ hp => hp.2)
  have hβeq' : ∀ᶠ z in 𝓝 (c.ambient.extend (𝓡∂ (k + 1)) x.val),
      z ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
        β z = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm z) :=
    eventually_nhdsWithin_iff.mp hβeq
  have hGeq : ∀ᶠ p in 𝓝 (0, x),
      G p ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
        β (G p) = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm (G p)) := by
    have hh := hG.continuousOn.continuousAt (hS.mem_nhds hxS)
    have hβeq'' : ∀ᶠ z in 𝓝 (G (0, x)),
        z ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
          β z = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm z) := by
      rwa [hcenter]
    exact hh.eventually hβeq''
  obtain ⟨Q, hQeq, hQ, hxQ⟩ := mem_nhds_iff.mp hGeq
  let Y := c.chart.source ∩ c.chart ⁻¹' V
  have hY : IsOpen Y := hc.continuousOn.isOpen_inter_preimage c.chart.open_source hV
  have hxY : x ∈ Y := ⟨hx, hxV⟩
  let W := (S ∩ G ⁻¹' A) ∩ Q ∩ (Ioo (-ε) ε ×ˢ Y)
  have hW : IsOpen W := (hGA.inter hQ).inter (isOpen_Ioo.prod hY)
  have hxW : (0, x) ∈ W :=
    ⟨⟨hxGA, hxQ⟩, ⟨⟨neg_neg_of_pos hε, hε⟩, hxY⟩⟩
  refine ⟨a, W, hW, hxW, ha.mono (fun _ hp => hp.1.1), ?_⟩
  intro p hp
  have hy : p.2 ∈ Y := hp.1.2.2
  have ht : p.1 ∈ Ico 0 ε := ⟨hp.2.1.1, hp.1.2.1.2⟩
  obtain ⟨hsource, hcoord⟩ := hmatch (c.chart p.2) hy.2 p.1 ht
  rw [c.chart.left_inv hy.1] at hsource hcoord
  have hGcoord : G p = c.ambient.extend (𝓡∂ (k + 1)) (C p) := hcoord.symm
  have hGtarget : G p ∈ (c.ambient.extend (𝓡∂ (k + 1))).target := by
    rw [hGcoord]
    exact (c.ambient.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using hsource)
  change β (G p) = φ (C p)
  rw [hQeq hp.1.1.2 hGtarget, hGcoord,
    (c.ambient.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [OpenPartialHomeomorph.extend_source] using hsource)]

/-- A continuous native map with an actual smooth chart extension acquires
a smooth manifold-valued germ across the same Liouville collar. The collar
is required to be jointly smooth on its native half-strip. Its field
extensions and matching two-sided coordinate evolution are constructed
from the primitive, nondegeneracy, and outwardness. -/
theorem exists_seam_map_germ_of_primitive
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ z, Nondegenerate (exteriorDerivative α) z)
    (x : IntrinsicBoundary.Point k M)
    (hout : 0 < (show ℝ from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ y, C (0, y) = y.val)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ univ))
    (f : M → N) (hf : Continuous f)
    (hφ : ∃ (β : Model (k + 1) → F) (A : Set (Model (k + 1))),
      IsOpen A ∧ (IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val ∈ A ∧
      ContDiffOn ℝ ∞ β A ∧
      β =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
        (fun z => chartAt F (f x.val)
          (f (((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm z)))) :
    ∃ W : TopologicalSpace.Opens (ℝ × IntrinsicBoundary.Point k M),
      (0, x) ∈ W ∧ ∃ a : W → N,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞ a ∧
        ∀ p : W, (p : ℝ × IntrinsicBoundary.Point k M) ∈ Ico 0 δ ×ˢ univ →
          a p = f (C p) := by
  let e := chartAt F (f x.val)
  let H : Set (ℝ × IntrinsicBoundary.Point k M) := Ico 0 δ ×ˢ univ
  have hxH : (0, x) ∈ H := ⟨⟨le_rfl, hδ⟩, mem_univ _⟩
  obtain ⟨v, W, hWo, hxW, hv, heq⟩ :=
    exists_seam_vector_germ_of_primitive α hα hnd x hout C hδ hzero hode
      (fun z => e (f z)) hφ
  have hvzero : v (0, x) = e (f x.val) := by
    simpa only [hzero] using heq ⟨hxW, hxH⟩
  have hvtarget : v (0, x) ∈ e.target := by
    rw [hvzero]
    exact e.map_source (mem_chart_source F (f x.val))
  have hWt : IsOpen (W ∩ v ⁻¹' e.target) :=
    hv.continuousOn.isOpen_inter_preimage hWo e.open_target
  have hxWt : (0, x) ∈ W ∩ v ⁻¹' e.target := ⟨hxW, hvtarget⟩
  have hfc : ContinuousWithinAt (f ∘ C) H (0, x) :=
    hf.continuousAt.comp_continuousWithinAt (hC.continuousOn (0, x) hxH)
  have hsource : ∀ᶠ p in 𝓝[H] (0, x), f (C p) ∈ e.source := by
    apply hfc
    change e.source ∈ 𝓝 (f (C (0, x)))
    rw [hzero]
    exact e.open_source.mem_nhds (mem_chart_source F (f x.val))
  obtain ⟨Q, hQsource, hQo, hxQ⟩ :=
    mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hsource)
  let O : TopologicalSpace.Opens (ℝ × IntrinsicBoundary.Point k M) :=
    ⟨(W ∩ v ⁻¹' e.target) ∩ Q, hWt.inter hQo⟩
  have hvo : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞
      (fun p : O => v p) :=
    hv.comp_contMDiff contMDiff_subtype_val (fun p => p.property.1.1)
  let a : O → N := fun p => e.symm (v p)
  have ha : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞ a :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (x := f x.val)).comp_contMDiff hvo
      (fun p => p.property.1.2)
  refine ⟨O, ⟨hxWt, hxQ⟩, a, ha, ?_⟩
  intro p hp
  change e.symm (v p) = f (C p)
  rw [heq ⟨p.property.1.1, hp⟩]
  exact e.left_inv (hQsource p.property.2 hp)

end FsFltz.Geometry.IntrinsicLiouville
