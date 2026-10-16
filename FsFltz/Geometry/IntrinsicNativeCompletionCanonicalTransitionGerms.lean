import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalExtensionAtlas
import FsFltz.Geometry.IntrinsicNativeCompletionMixedSectionExtension

/-!
# Real-open scalar germs in actual whole-bundle coordinates

Source: `geoemtric-part-fsf.tex`, lines 119–122; `def:maslov`, lines
212–244; `sec:lean`, lines 766–836. No section is used in these producers.
The scalar extends the actual inverse tensor coordinate change. It can be
combined with a real base change by taking its reciprocal near the overlap.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

local instance germsBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance germsProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance germsProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

namespace OriginalTotalCanonicalChart

variable {hδ C hemb hboundary hzero J}

abbrev nativeCoframe (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    c.NativeBase → Model (2 * n) →L[ℝ] TangentCoordinates n :=
  match c with
  | .inl c => c.nativeCoframe N
  | .inr c => c.nativeCoframe N

end OriginalTotalCanonicalChart

include hjoint in
theorem originalTotalCanonicalTransition_native
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (q : d.NativeBase) (hpq : c.inclusion p = d.inclusion q) :
    originalTotalCanonicalTransition hδ C hemb hboundary hzero J N c d (c.inclusion p) =
      squaredCoframeTransition (c.nativeCoframe N p) (d.nativeCoframe N q) := by
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have he : p = q :=
        (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hpq
      subst q
      exact originalInteriorCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p
    | inr d =>
      exact originalEndToInteriorCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p q hpq
  | inr c =>
    cases d with
    | inl d =>
      change originalInteriorToEndCanonicalTransition hδ C hemb hboundary hzero J N d c
        (totalCylinder (fun t p => C t p.val) p) = _
      change totalCylinder (fun t p => C t p.val) p = totalInterior (fun t p => C t p.val) q at hpq
      rw [hpq]
      exact originalInteriorToEndCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N d c q p hpq.symm
    | inr d =>
      have he : p = q := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hpq
      subst q
      exact originalEndCanonicalTransition_apply hδ C hemb hboundary hzero hjoint J N c d p

include hC hinv hjoint hmix P in
/-- Each actual whole-bundle overlap has a smooth real-open scalar germ in
the source's raw coordinates. The value is the inverse coordinate change. -/
theorem exists_originalTotalCanonicalInverseScalarGerm
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (q : d.NativeBase)
    (hp : p ∈ c.nativeDomain) (hq : q ∈ d.nativeDomain)
    (hpq : c.inclusion p = d.inclusion q) :
    ∃ (U : TopologicalSpace.Opens c.RealBase) (a : c.RealBase → ℂ),
      c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ a U ∧
      (U : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ (r : c.NativeBase) (s : d.NativeBase),
        r ∈ c.nativeDomain → s ∈ d.nativeDomain → c.inclusion r = d.inclusion s →
        c.baseCoordinate r ∈ U →
        a (c.baseCoordinate r) =
          originalTotalCanonicalTransition hδ C hemb hboundary hzero J N d c (c.inclusion r) := by
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have he : p = q :=
        (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hpq
      subst q
      let U : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
        ⟨d.transitionDomain c, d.isOpen_transitionDomain c⟩
      have hpU : (p.1.val, chartAt (Model (k + 1)) c.anchor p.2) ∈ U := by
        refine ⟨⟨⟨mem_univ _, (chartAt (Model (k + 1)) c.anchor).map_source hp.1.2, ?_⟩, ?_⟩, hp.2⟩
        · change (chartAt (Model (k + 1)) c.anchor).symm
            (chartAt (Model (k + 1)) c.anchor p.2) ∈ (chartAt (Model (k + 1)) d.anchor).source
          rw [(chartAt (Model (k + 1)) c.anchor).left_inv hp.1.2]; exact hq.1.2
        · change (p.1.val, chartAt (Model (k + 1)) d.anchor
            ((chartAt (Model (k + 1)) c.anchor).symm (chartAt (Model (k + 1)) c.anchor p.2))) ∈ d.domain
          rw [(chartAt (Model (k + 1)) c.anchor).left_inv hp.1.2]; exact hq.2
      refine ⟨U, d.transitionExtension (P := N) c, hpU, d.smooth_transitionExtension c,
        inter_subset_right, ?_⟩
      intro r s hr hs hrs _
      have he : r = s :=
        (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hrs
      subst s
      rw [originalTotalCanonicalTransition_native hδ C hemb hboundary hzero J N hjoint
        (.inl d) (.inl c) r r rfl]
      dsimp only [OriginalTotalCanonicalChart.baseCoordinate, OriginalTotalCanonicalChart.nativeCoframe,
        OriginalInteriorCanonicalChart.transitionExtension]
      rw [(chartAt (Model (k + 1)) c.anchor).left_inv hr.1.2]
      exact (originalInteriorCanonical_squaredTransition hδ (C r.1) (hemb r.1) (hC r.1)
        (hboundary r.1) (hinv r.1) (hzero r.1) N c.anchor d.anchor r.2 hr.1.2 hs.1.2 _ _).symm
    | inr d =>
      rcases p with ⟨t, w⟩
      rcases q with ⟨u, b⟩
      have htu : t = u := by
        have h := congrArg (parameter (fun t p => C t p.val)) hpq
        simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
          parameter_totalCylinder] using h
      subst u
      obtain ⟨U, g, a, hpU, _, ha, _, hUc, _, hret⟩ :=
        exists_originalInteriorToEndCanonicalTransitionGerm hδ C hemb hC hboundary hinv hzero
          hjoint hmix J N c d t w b hpq hp hq
      refine ⟨U, a, hpU, ha, hUc, ?_⟩
      rintro ⟨u, v⟩ ⟨s, b'⟩ hr hs hrs hU
      have hus : u = s := by
        have h := congrArg (parameter (fun t p => C t p.val)) hrs
        simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
          parameter_totalCylinder] using h
      subst s
      obtain ⟨q, _, _, heq, hscalar⟩ := hret u v hr.1.2 hU
      have he : q = b' := congrArg Prod.snd
        ((isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective (heq.symm.trans hrs))
      subst q
      exact hscalar.trans (by
        rw [hrs]
        exact (originalTotalCanonicalTransition_native hδ C hemb hboundary hzero J N hjoint
          (.inr d) (.inl c) (u, b') (u, v) hrs.symm).symm)
  | inr c =>
    cases d with
    | inl d =>
      rcases p with ⟨t, b⟩
      rcases q with ⟨u, w⟩
      have htu : t = u := by
        have h := congrArg (parameter (fun t p => C t p.val)) hpq
        simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
          parameter_totalCylinder] using h
      subst u
      obtain ⟨U, g, a, hpU, _, ha, _, hUc, _, hret⟩ :=
        exists_originalEndToInteriorCanonicalTransitionGerm hδ C hemb hC hboundary hinv hzero
          hjoint hmix J N P d c t w b hpq.symm hq hp
      refine ⟨U, a, hpU, ha, hUc, ?_⟩
      rintro ⟨u, b'⟩ ⟨s, v⟩ hr hs hrs hU
      have hus : u = s := by
        have h := congrArg (parameter (fun t p => C t p.val)) hrs
        simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
          parameter_totalCylinder] using h
      subst s
      obtain ⟨v', _, _, heq, hscalar⟩ := hret u b' hr.1.2 hU
      have he : v' = v := congrArg Prod.snd
        ((isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective (heq.trans hrs))
      subst v'
      exact hscalar.trans (by
        rw [hrs]
        exact (originalTotalCanonicalTransition_native hδ C hemb hboundary hzero J N hjoint
          (.inl d) (.inr c) (u, v) (u, b') hrs.symm).symm)
    | inr d =>
      have he : p = q := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hpq
      subst q
      let U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)) :=
        ⟨d.transitionDomain c, d.isOpen_transitionDomain c⟩
      have hpU : (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)) ∈ U := by
        refine ⟨⟨⟨mem_univ _, (chartAt (Model k × ℝ) c.anchor).map_source hp.1.2, ?_⟩, ?_⟩, hp.2⟩
        · change (chartAt (Model k × ℝ) c.anchor).symm
            (chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)) ∈
              (chartAt (Model k × ℝ) d.anchor).source
          rw [(chartAt (Model k × ℝ) c.anchor).left_inv hp.1.2]; exact hq.1.2
        · change (p.1.val, chartAt (Model k × ℝ) d.anchor
            ((chartAt (Model k × ℝ) c.anchor).symm
              (chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)))) ∈ d.domain
          rw [(chartAt (Model k × ℝ) c.anchor).left_inv hp.1.2]; exact hq.2
      refine ⟨U, d.transitionExtension (P := P) c, hpU, d.smooth_transitionExtension (P := P) c,
        inter_subset_right, ?_⟩
      intro r s hr hs hrs _
      have he : r = s := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hrs
      subst s
      rw [originalTotalCanonicalTransition_native hδ C hemb hboundary hzero J N hjoint
        (.inr d) (.inr c) r r rfl]
      dsimp only [OriginalTotalCanonicalChart.baseCoordinate, OriginalTotalCanonicalChart.nativeCoframe,
        OriginalEndCanonicalChart.transitionExtension]
      rw [(chartAt (Model k × ℝ) c.anchor).left_inv hr.1.2]
      exact (originalEndCanonical_squaredTransition hδ (C r.1) (hemb r.1) (hC r.1)
        (hboundary r.1) (hinv r.1) (hzero r.1) N P c.anchor d.anchor r.2 hr.1.2 hs.1.2 _ _).symm

end FsFltz.Geometry.IntrinsicCompletionGluing
