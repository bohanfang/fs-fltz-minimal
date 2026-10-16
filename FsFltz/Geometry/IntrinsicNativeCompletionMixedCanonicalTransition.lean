import FsFltz.Geometry.IntrinsicNativeCompletionMixedCanonicalChart

/-!
# Real mixed transition germs for original canonical charts

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The produced real mixed collar germs give
smooth scalar transitions between the original canonical coframe charts,
including real neighborhoods of the two original parameter endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}

local instance mixedTransitionBandCharts : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance mixedTransitionProductCharts : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance mixedTransitionProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

include hC hinv hjoint hmix PE in
/-- A smooth real extension of the end-to-interior coordinate map and the
canonical-square scalar transition, derived on every genuine mixed overlap. -/
theorem exists_originalEndToInteriorCanonicalTransitionGerm
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (s : Parameter) (w : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain) :
    ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)))
      (g : ℝ × (Model k × ℝ) → Model (k + 1)) (f : ℝ × (Model k × ℝ) → ℂ),
      (s.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates p)) ∈ U ∧
      ContDiffOn ℝ ∞ g U ∧ ContDiffOn ℝ ∞ f U ∧
      g (s.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates p)) =
        chartAt (Model (k + 1)) c.anchor w ∧
      (U : Set (ℝ × (Model k × ℝ))) ⊆ (d.domain : Set (ℝ × (Model k × ℝ))) ∧
      (∀ z ∈ U, (z.1, g z) ∈ c.domain) ∧
      ∀ (t : Parameter) (q : Band δ (IntrinsicBoundary.Point k M)),
        endBandCoordinates q ∈ (chartAt (Model k × ℝ) d.anchor).source →
        (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates q)) ∈ U →
        ∃ v : IntrinsicInterior.Point k M,
          v ∈ (chartAt (Model (k + 1)) c.anchor).source ∧
          chartAt (Model (k + 1)) c.anchor v =
            g (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates q)) ∧
          totalInterior (fun t p => C t p.val) (t, v) =
            totalCylinder (fun t p => C t p.val) (t, q) ∧
          f (t.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates q)) =
            squaredCoframeTransition (c.nativeCoframe N (t, v)) (d.nativeCoframe N (t, q)) := by
  let ei := chartAt (Model (k + 1)) c.anchor
  let ee := chartAt (Model k × ℝ) d.anchor
  obtain ⟨_, hpos, _⟩ := (totalInterior_eq_totalCylinder_iff
    (fun t p => C t p.val) hboundary (s, w) (s, p)).mp hpoint
  obtain ⟨A, hpA, hApos, hparam, hparamInv, hforward, hreverse⟩ :=
    hmix s p.val ⟨hpos, p.property.1⟩
  let R : ℝ × (Model k × ℝ) → ℝ × (ℝ × IntrinsicBoundary.Point k M) :=
    fun z => (z.1, (-(ee.symm z.2).2, (ee.symm z.2).1))
  let U₀ : Set (ℝ × (Model k × ℝ)) := univ ×ˢ ee.target
  have hU₀ : IsOpen U₀ := isOpen_univ.prod ee.open_target
  have hR : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k))) ∞ R U₀ := by
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model k × ℝ) ∞
        (fun z : ℝ × (Model k × ℝ) => z.2) U₀ := by
      exact contDiffOn_snd.contMDiffOn
    have he : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model k × ℝ) ∞
        (fun z : ℝ × (Model k × ℝ) => ee.symm z.2) U₀ :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model k × ℝ)) (x := d.anchor)).comp
        hsnd (fun _ hz => hz.2)
    rw [modelWithCornersSelf_prod (E := Model k) (F := ℝ)] at he
    exact contDiffOn_fst.contMDiffOn.prodMk
      ((contMDiff_snd.comp_contMDiffOn he).neg.prodMk (contMDiff_fst.comp_contMDiffOn he))
  let S₀ := U₀ ∩ R ⁻¹' A.source
  have hS₀ : IsOpen S₀ := hR.continuousOn.isOpen_inter_preimage hU₀ A.open_source
  let K : ℝ × (Model k × ℝ) → IntrinsicInterior.Point k M := fun z => (A (R z)).2
  have hK : ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model (k + 1)) ∞ K S₀ :=
    contMDiff_snd.comp_contMDiffOn
      (A.contMDiffOn_toFun.comp (hR.mono inter_subset_left) inter_subset_right)
  let S := S₀ ∩ K ⁻¹' ei.source
  have hS : IsOpen S := hK.continuousOn.isOpen_inter_preimage hS₀ ei.open_source
  let g : ℝ × (Model k × ℝ) → Model (k + 1) := fun z => ei (K z)
  have hg : ContDiffOn ℝ ∞ g S :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor)).comp
      (hK.mono inter_subset_left) inter_subset_right).contDiffOn
  let Z := S ∩ d.domain
  have hZ : IsOpen Z := hS.inter d.domain.isOpen
  let V := Z ∩ (fun z => (z.1, g z)) ⁻¹' c.domain
  have hV : IsOpen V := (continuous_fst.continuousOn.prodMk
    (hg.mono inter_subset_left).continuousOn).isOpen_inter_preimage hZ c.domain.isOpen
  let U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)) := ⟨V, hV⟩
  let z₀ := (s.val, ee (endBandCoordinates p))
  have hR₀ : R z₀ = (s.val, p.val) := by
    dsimp only [R, z₀]
    rw [ee.left_inv hp.1.2]
    simp only [endBandCoordinates, neg_neg, Prod.mk.eta]
  have hK₀ : K z₀ = w := by
    have h : totalInterior (δ := δ) (fun t p => C t p.val) (s, K z₀) =
        totalInterior (δ := δ) (fun t p => C t p.val) (s, w) := by
      dsimp only [K]
      rw [hR₀]
      exact (hforward s p hpA).trans hpoint.symm
    exact congrArg Prod.snd
      ((isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective h)
  have hz₀ : z₀ ∈ U := by
    refine ⟨⟨⟨⟨⟨mem_univ _, ee.map_source hp.1.2⟩, ?_⟩, ?_⟩, hp.2⟩, ?_⟩
    · change R z₀ ∈ A.source
      rw [hR₀]; exact hpA
    · change K z₀ ∈ ei.source
      rw [hK₀]; exact hw.1.2
    · change (s.val, ei (K z₀)) ∈ c.domain
      rw [hK₀]; exact hw.2
  let f : ℝ × (Model k × ℝ) → ℂ := fun z =>
    squaredCoframeTransition
      (((c.coframe (z.1, g z)).comp (mixedSpatialDerivative g z)).comp PE.toContinuousLinearMap)
      ((d.coframe z).comp PE.toContinuousLinearMap)
  have hgU : ContDiffOn ℝ ∞ g U := hg.mono (fun _ hz => hz.1.1)
  have hf : ContDiffOn ℝ ∞ f U :=
    contDiffOn_squaredCoframeTransition
      (((c.smooth_coframe.comp (contDiffOn_fst.prodMk hgU) (fun _ hz => hz.2)).clm_comp
        (contDiffOn_mixedSpatialDerivative hgU U.isOpen)).clm_comp contDiffOn_const)
      ((d.smooth_coframe.mono (fun _ hz => hz.1.2)).clm_comp contDiffOn_const)
      (fun z hz => (d.invertible_coframe z hz.1.2).comp ⟨PE, rfl⟩)
  refine ⟨U, g, f, hz₀, hgU, hf, ?_, (fun _ hz => hz.1.2), (fun _ hz => hz.2), ?_⟩
  · change ei (K z₀) = ei w
    rw [hK₀]
  intro t q hq hqU
  let z := (t.val, ee (endBandCoordinates q))
  have hRz : R z = (t.val, q.val) := by
    dsimp only [R, z]
    rw [ee.left_inv hq]
    simp only [endBandCoordinates, neg_neg, Prod.mk.eta]
  have hzS : z ∈ S := hqU.1.1
  have hv : K z ∈ ei.source := hzS.2
  have hmatch : totalInterior (fun t p => C t p.val) (t, K z) =
      totalCylinder (fun t p => C t p.val) (t, q) := by
    dsimp only [K]
    rw [hRz]
    exact hforward t q (hRz ▸ hzS.1.2)
  refine ⟨K z, hv, rfl, hmatch, ?_⟩
  let F : (Model k × ℝ) → IntrinsicInterior.Point k M := fun y => K (t.val, y)
  have hF : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ F z.2 :=
    (hK.contMDiffAt (hS₀.mem_nhds hzS.1)).comp z.2
      (contMDiffAt_const.prodMk_space contMDiffAt_id)
  have hnear : ∀ᶠ q' in 𝓝 q,
      (t.val, ee (endBandCoordinates q')) ∈ U ∧ endBandCoordinates q' ∈ ee.source := by
    have hc := (contMDiff_endBandCoordinates (k := k) (M := M) (δ := δ)).continuous
    have he := ee.continuousOn.continuousAt (ee.open_source.mem_nhds hq)
    have hzcont : ContinuousAt
        (fun q' : Band δ (IntrinsicBoundary.Point k M) => (t.val, ee (endBandCoordinates q'))) q :=
      continuousAt_const.prodMk (he.comp hc.continuousAt)
    filter_upwards [hzcont.preimage_mem_nhds (U.isOpen.mem_nhds hqU),
      hc.continuousAt.preimage_mem_nhds (ee.open_source.mem_nhds hq)] with q' hU' hS'
    exact ⟨hU', hS'⟩
  have heq : ∀ᶠ q' in 𝓝 q,
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C t r.val)
        (F (ee (endBandCoordinates q'))) =
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C t r.val) q' := by
    filter_upwards [hnear] with q' hq'
    have hR' : R (t.val, ee (endBandCoordinates q')) = (t.val, q'.val) := by
      dsimp only [R]
      rw [ee.left_inv hq'.2]
      simp only [endBandCoordinates, neg_neg, Prod.mk.eta]
    have h := hforward t q' (hR' ▸ hq'.1.1.1.1.2)
    apply sliceIn_injective (fun t p => C t p.val) t
    rw [sliceIn_cylinder]
    change sliceIn (fun t p => C t p.val) t
      (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)
        (F (ee (endBandCoordinates q'))).val) = _
    rw [sliceIn_original]
    dsimp only [F, K]
    rw [hR']
    exact h
  have hdg : mixedSpatialDerivative g z = fderiv ℝ (ei ∘ F) z.2 :=
    mixedSpatialDerivative_eq ((hgU.contDiffAt (U.isOpen.mem_nhds hqU)).differentiableAt
      (by simp))
  have hscalar := originalMixedCanonical_squaredTransition_of_germ
    hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) N PE c.anchor d.anchor q F
    hF hq hv heq (c.coframe (z.1, g z)) (d.coframe z)
  dsimp only [f]
  rw [hdg]
  exact hscalar.symm

end FsFltz.Geometry.IntrinsicCompletionGluing
