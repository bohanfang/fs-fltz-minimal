import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalTransitionGerms
import FsFltz.Geometry.RealOpenCanonicalTransition

/-!
# Real-open changes of the actual whole canonical bundle charts

Source: `geoemtric-part-fsf.tex`, lines 119–122; `def:maslov`, lines
212–244; `sec:lean`, lines 766–836. The base changes come from actual
spatial charts and the original mixed collar germs. An independent smooth
inverse scalar germ is reciprocated on its nonzero locus. The resulting
forward and inverse maps belong to the same partial diffeomorphism.
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

local instance changesProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance changesProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

include hjoint hmix in
/-- All four actual base changes have real-open mutually inverse germs. -/
theorem exists_originalTotalCanonicalBaseChangeGerm
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (q : d.NativeBase)
    (hp : p ∈ c.nativeDomain) (hq : q ∈ d.nativeDomain)
    (hpq : c.inclusion p = d.inclusion q) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, c.RealBase) 𝓘(ℝ, d.RealBase) c.RealBase d.RealBase ∞,
      c.baseCoordinate p ∈ B.source ∧ B (c.baseCoordinate p) = d.baseCoordinate q ∧
      (∀ (r : c.NativeBase) (s : d.NativeBase),
        r ∈ c.nativeDomain → s ∈ d.nativeDomain → c.inclusion r = d.inclusion s →
        c.baseCoordinate r ∈ B.source → B (c.baseCoordinate r) = d.baseCoordinate s) ∧
      (∀ (r : c.NativeBase) (s : d.NativeBase),
        r ∈ c.nativeDomain → s ∈ d.nativeDomain → c.inclusion r = d.inclusion s →
        d.baseCoordinate s ∈ B.target → B.symm (d.baseCoordinate s) = c.baseCoordinate r) := by
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have he : p = q :=
        (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hpq
      subst q
      obtain ⟨B, hpB, hB, hf, hi⟩ :=
        exists_realParameterChartChange c.anchor d.anchor p.2 p.1.val hp.1.2 hq.1.2
      refine ⟨B, hpB, hB, ?_, ?_⟩
      · intro r s hr hs hrs _
        have he : r = s :=
          (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hrs
        subst s
        exact hf r.1.val r.2 hr.1.2 hs.1.2
      · intro r s hr hs hrs _
        have he : r = s :=
          (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective hrs
        subst s
        exact hi r.1.val r.2 hr.1.2 hs.1.2
    | inr d =>
      rcases p with ⟨t, w⟩
      rcases q with ⟨u, b⟩
      have htu : t = u := by
        have h := congrArg (parameter (fun t p => C t p.val)) hpq
        simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
          parameter_totalCylinder] using h
      subst u
      obtain ⟨B, hqB, hB, hf, hi⟩ :=
        exists_realMixedChartChange hδ C hboundary hzero hjoint hmix c.anchor d.anchor
          t w b hp.1.2 hq.1.2 hpq
      have hpB : (t.val, chartAt (Model (k + 1)) c.anchor w) ∈ B.target := hB ▸ B.map_source hqB
      refine ⟨B.symm, hpB, ?_, ?_, ?_⟩
      · exact hi t w b hp.1.2 hq.1.2 hpq hpB
      · rintro ⟨u, v⟩ ⟨s, b'⟩ hr hs hrs hB'
        have hus : u = s := by
          have h := congrArg (parameter (fun t p => C t p.val)) hrs
          simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
            parameter_totalCylinder] using h
        subst s
        exact hi u v b' hr.1.2 hs.1.2 hrs hB'
      · rintro ⟨u, v⟩ ⟨s, b'⟩ hr hs hrs hB'
        have hus : u = s := by
          have h := congrArg (parameter (fun t p => C t p.val)) hrs
          simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
            parameter_totalCylinder] using h
        subst s
        exact hf u v b' hr.1.2 hs.1.2 hrs hB'
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
      obtain ⟨B, hpB, hB, hf, hi⟩ :=
        exists_realMixedChartChange hδ C hboundary hzero hjoint hmix d.anchor c.anchor
          t w b hq.1.2 hp.1.2 hpq.symm
      refine ⟨B, hpB, hB, ?_, ?_⟩
      · rintro ⟨u, b'⟩ ⟨s, v⟩ hr hs hrs hB'
        have hus : u = s := by
          have h := congrArg (parameter (fun t p => C t p.val)) hrs
          simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
            parameter_totalCylinder] using h
        subst s
        exact hf u v b' hs.1.2 hr.1.2 hrs.symm hB'
      · rintro ⟨u, b'⟩ ⟨s, v⟩ hr hs hrs hB'
        have hus : u = s := by
          have h := congrArg (parameter (fun t p => C t p.val)) hrs
          simpa only [OriginalTotalCanonicalChart.inclusion, totalInterior, parameter_original,
            parameter_totalCylinder] using h
        subst s
        exact hi u v b' hs.1.2 hr.1.2 hrs.symm hB'
    | inr d =>
      have he : p = q := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hpq
      subst q
      obtain ⟨B, hpB, hB, hf, hi⟩ := exists_realParameterChartChange (E := Model k × ℝ) c.anchor d.anchor
        (endBandCoordinates p.2) p.1.val hp.1.2 hq.1.2
      refine ⟨B, hpB, hB, ?_, ?_⟩
      · intro r s hr hs hrs _
        have he : r = s := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hrs
        subst s
        exact hf r.1.val (endBandCoordinates r.2) hr.1.2 hs.1.2
      · intro r s hr hs hrs _
        have he : r = s := (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).injective hrs
        subst s
        exact hi r.1.val (endBandCoordinates r.2) hr.1.2 hs.1.2

include hjoint hC hinv hmix P in
/-- Real-open changes of the independently constructed actual total-bundle
charts. Both directions recover every retained tensor in the overlap. -/
theorem exists_originalTotalCanonicalChartChangeGerm
    (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (z : Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hc : z.proj ∈ c.totalDomain) (hd : z.proj ∈ d.totalDomain) :
    ∃ A : PartialDiffeomorph 𝓘(ℝ, c.RealModel) 𝓘(ℝ, d.RealModel)
        c.RealModel d.RealModel ∞,
      c.coordinateAt N hjoint hC hinv z hc ∈ A.source ∧
      A (c.coordinateAt N hjoint hC hinv z hc) = d.coordinateAt N hjoint hC hinv z hd ∧
      (∀ (w : Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
        (hwc : w.proj ∈ c.totalDomain) (hwd : w.proj ∈ d.totalDomain),
        c.coordinateAt N hjoint hC hinv w hwc ∈ A.source →
        A (c.coordinateAt N hjoint hC hinv w hwc) = d.coordinateAt N hjoint hC hinv w hwd) ∧
      (∀ (w : Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
        (hwc : w.proj ∈ c.totalDomain) (hwd : w.proj ∈ d.totalDomain),
        d.coordinateAt N hjoint hC hinv w hwd ∈ A.target →
        A.symm (d.coordinateAt N hjoint hC hinv w hwd) = c.coordinateAt N hjoint hC hinv w hwc) := by
  have hpq : c.inclusion hc.choose = d.inclusion hd.choose :=
    hc.choose_spec.2.trans hd.choose_spec.2.symm
  obtain ⟨B, hpB, hB, hf, hi⟩ := exists_originalTotalCanonicalBaseChangeGerm
    hδ C hemb hboundary hzero J hjoint hmix c d hc.choose hd.choose
      hc.choose_spec.1 hd.choose_spec.1 hpq
  obtain ⟨U, a, hpU, ha, hUc, hret⟩ := exists_originalTotalCanonicalInverseScalarGerm
    hδ C hemb hboundary hzero J N hjoint hC hinv hmix P c d hc.choose hd.choose
      hc.choose_spec.1 hd.choose_spec.1 hpq
  let V : TopologicalSpace.Opens c.RealBase :=
    ⟨{r | r ∈ U ∧ a r ≠ 0},
      ha.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ne⟩
  have hav : ContDiffOn ℝ ∞ (fun r => (a r)⁻¹) V :=
    (ha.mono (fun _ hr => hr.1)).inv (fun _ hr => hr.2)
  let A := RealOpenCanonicalTransition.skewProduct B V (fun r => (a r)⁻¹) hav
  have hfA : ∀ (w : Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
      (hwc : w.proj ∈ c.totalDomain) (hwd : w.proj ∈ d.totalDomain),
      c.coordinateAt N hjoint hC hinv w hwc ∈ A.source →
      A (c.coordinateAt N hjoint hC hinv w hwc) = d.coordinateAt N hjoint hC hinv w hwd := by
    intro w hwc hwd hwA
    have hw := (RealOpenCanonicalTransition.mem_skewProduct_source B V _ hav _).mp hwA
    have hpq' : c.inclusion hwc.choose = d.inclusion hwd.choose :=
      hwc.choose_spec.2.trans hwd.choose_spec.2.symm
    have hab := hret hwc.choose hwd.choose hwc.choose_spec.1 hwd.choose_spec.1 hpq' hw.2.1.1
    rw [hwc.choose_spec.2] at hab
    have hiab := inv_eq_of_mul_eq_one_right
      (originalTotalCanonicalTransition_mul_reverse hδ C hemb hboundary hzero J N
        hjoint hC hinv c d ⟨hwc, hwd⟩)
    apply Prod.ext
    · exact hf hwc.choose hwd.choose hwc.choose_spec.1 hwd.choose_spec.1 hpq' hw.1
    · change (a (c.baseCoordinate hwc.choose))⁻¹ * _ = _
      rw [hab, hiab]
      exact (originalTotalCanonicalCoefficient_transition hδ C hemb hboundary hzero J N
        hjoint hC hinv c d ⟨hwc, hwd⟩ w.snd).symm
  have hpaz : a (c.baseCoordinate hc.choose) ≠ 0 := by
    rw [hret hc.choose hd.choose hc.choose_spec.1 hd.choose_spec.1 hpq hpU,
      hc.choose_spec.2]
    exact originalTotalCanonicalTransition_ne_zero hδ C hemb hboundary hzero J N
      hjoint hC hinv d c ⟨hd, hc⟩
  have hzA : c.coordinateAt N hjoint hC hinv z hc ∈ A.source := by
    exact RealOpenCanonicalTransition.mk_mem_skewProduct_source B V _ hav hpB
      ⟨hpU, hpaz⟩ (inv_ne_zero hpaz) _
  refine ⟨A, hzA, hfA z hc hd hzA, hfA, ?_⟩
  intro w hwc hwd hwA
  have hw := (RealOpenCanonicalTransition.mem_skewProduct_target B V _ hav _).mp hwA
  have hpq' : c.inclusion hwc.choose = d.inclusion hwd.choose :=
    hwc.choose_spec.2.trans hwd.choose_spec.2.symm
  have hb := hi hwc.choose hwd.choose hwc.choose_spec.1 hwd.choose_spec.1 hpq' hw.1
  have hwcA : c.coordinateAt N hjoint hC hinv w hwc ∈ A.source := by
    exact RealOpenCanonicalTransition.mk_mem_skewProduct_source B V _ hav
      (hb ▸ B.map_target hw.1) (hb ▸ hw.2.1) (hb ▸ hw.2.2) _
  rw [← hfA w hwc hwd hwcA]
  exact A.left_inv hwcA

end FsFltz.Geometry.IntrinsicCompletionGluing
