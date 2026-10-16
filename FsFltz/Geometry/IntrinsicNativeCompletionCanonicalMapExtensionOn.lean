import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalMapExtensionExtraction

/-!
# Real-open map extensions on retained source subsets

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (788–814). The source subset is
independent of the map. Coordinate matching and regularity are required only
there; in particular a local completion's auxiliary cutoff family need not
carry an extension of a prescribed section on its whole parameter interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
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

/-- The arbitrary full map has real-open extensions only at points of `A`,
with coordinate matching only on `A`. The charts precede the map. -/
def HasOriginalTotalLocalMapExtensionsOn
    (A : Set (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N)) : Prop :=
  ∀ x ∈ A, ∃ (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase), p ∈ c.nativeDomain ∧ c.inclusion p = x ∧
    (f x).proj ∈ d.totalDomain ∧
    ∃ (U : TopologicalSpace.Opens c.RealBase) (G : c.RealBase → d.RealModel),
      c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      (U : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain → c.inclusion q ∈ A →
        c.baseCoordinate q ∈ U →
        ∃ hd : (f (c.inclusion q)).proj ∈ d.totalDomain,
          G (c.baseCoordinate q) =
            d.coordinateAt N hjoint hC hinv (f (c.inclusion q)) hd

/-- The same retained-source condition in every covering chart. -/
def HasOriginalTotalChartMapExtensionsOn
    (A : Set (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N)) : Prop :=
  ∀ (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase), p ∈ c.nativeDomain → c.inclusion p ∈ A →
    (f (c.inclusion p)).proj ∈ d.totalDomain →
    ∃ (U : TopologicalSpace.Opens c.RealBase) (G : c.RealBase → d.RealModel),
      c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      (U : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain → c.inclusion q ∈ A →
        c.baseCoordinate q ∈ U →
        ∃ hd : (f (c.inclusion q)).proj ∈ d.totalDomain,
          G (c.baseCoordinate q) =
            d.coordinateAt N hjoint hC hinv (f (c.inclusion q)) hd

variable (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

include hjoint hC hinv hmix P in
/-- Actual real chart changes transfer an arbitrary map on the retained
subset. No regularity or matching is added outside that subset. -/
theorem originalTotalChartMapExtensionsOn_of_localMapExtensionsOn
    (A : Set (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hf : Continuous (fun x => (f x).proj))
    (hlocal : HasOriginalTotalLocalMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv A f) :
    HasOriginalTotalChartMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv A f := by
  intro c d p hp hpA hdp
  obtain ⟨e, j, r, hr, hrp, hfj, U, G, hrU, hG, hUe, hret⟩ := hlocal (c.inclusion p) hpA
  obtain ⟨B₁, hpB₁, hB₁r, hB₁f, _⟩ := exists_originalTotalCanonicalBaseChangeGerm
    hδ C hemb hboundary hzero J hjoint hmix c e p r hp hr hrp.symm
  obtain ⟨B₂, hfjB₂, _, hB₂f, _⟩ := exists_originalTotalCanonicalChartChangeGerm
    hδ C hemb hboundary hzero J N hjoint hC hinv hmix P j d (f (c.inclusion p)) hfj hdp
  have hGr : G (e.baseCoordinate r) =
      j.coordinateAt N hjoint hC hinv (f (c.inclusion p)) hfj := by
    obtain ⟨hj, hgj⟩ := hret r hr (hrp.symm ▸ hpA) hrU
    simpa only [hrp] using hgj
  obtain ⟨V, hpV, hVB₁, hVU, hHV⟩ := RealOpenMapExtension.exists_composition_domain
    B₁ B₂ U G hG hpB₁ (hB₁r.symm ▸ hrU) (by rw [hB₁r, hGr]; exact hfjB₂)
  have hOe : IsOpen e.totalDomain := by
    rw [e.totalDomain_eq_baseSet N hjoint hC hinv]
    exact (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero
      hjoint J N hC hinv e).open_baseSet
  have hOd : IsOpen d.totalDomain := by
    rw [d.totalDomain_eq_baseSet N hjoint hC hinv]
    exact (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero
      hjoint J N hC hinv d).open_baseSet
  obtain ⟨Ve, hpVe, hVec, hVe⟩ := c.exists_rawCoordinate_neighborhood hjoint p hp hOe
    (show c.inclusion p ∈ e.totalDomain from ⟨r, hr, hrp⟩)
  obtain ⟨Vd, hpVd, hVdc, hVd⟩ := c.exists_rawCoordinate_neighborhood hjoint p hp
    (hOd.preimage hf) hdp
  let W : TopologicalSpace.Opens c.RealBase := (V ⊓ Ve) ⊓ Vd
  refine ⟨W, fun y => B₂ (G (B₁ y)), ⟨⟨hpV, hpVe⟩, hpVd⟩,
    hHV.mono (fun _ hy => hy.1.1), (fun _ hy => hVec hy.1.2), ?_⟩
  intro q hq hqA hqW
  have hqe : c.inclusion q ∈ e.totalDomain := hVe q hq hqW.1.2
  have hqd : (f (c.inclusion q)).proj ∈ d.totalDomain := hVd q hq hqW.2
  have hB₁q : B₁ (c.baseCoordinate q) = e.baseCoordinate hqe.choose :=
    hB₁f q hqe.choose hq hqe.choose_spec.1 hqe.choose_spec.2.symm (hVB₁ hqW.1.1)
  have hqU : e.baseCoordinate hqe.choose ∈ U := hB₁q ▸ (hVU _ hqW.1.1).1
  obtain ⟨hqj, hGq⟩ := hret hqe.choose hqe.choose_spec.1 (hqe.choose_spec.2.symm ▸ hqA) hqU
  have hGq' : G (e.baseCoordinate hqe.choose) =
      j.coordinateAt N hjoint hC hinv (f (c.inclusion q))
        (hqe.choose_spec.2 ▸ hqj) := by
    simpa only [hqe.choose_spec.2] using hGq
  refine ⟨hqd, ?_⟩
  change B₂ (G (B₁ (c.baseCoordinate q))) = _
  rw [hB₁q, hGq']
  apply hB₂f
  have hB₂q := (hVU _ hqW.1.1).2
  rwa [hB₁q, hGq'] at hB₂q

local instance retainedMapProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

/-- Extraction from the actual graph on a retained parameter base. Matching
of the coefficient is restricted to the same base as the full map. -/
theorem originalInteriorCoefficientExtensionOn_of_chartMapExtensionsOn
    (B : Set Parameter) (σ : OriginalNativeCanonicalSection C J N)
    (hmap : HasOriginalTotalChartMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv
      {x | parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) x ∈ B}
      (originalTotalSectionGraph C J N σ))
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain) (hpB : p.1 ∈ B) :
    ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1))) (q : ℝ × Model (k + 1) → ℂ),
      (p.1.val, chartAt (Model (k + 1)) c.anchor p.2) ∈ U ∧
      (U : Set (ℝ × Model (k + 1))) ⊆ c.domain ∧ ContDiffOn ℝ ∞ q U ∧
      ∀ (s : Parameter), s ∈ B → ∀ (w : IntrinsicInterior.Point k M),
        w ∈ (chartAt (Model (k + 1)) c.anchor).source →
        (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ U →
        q (s.val, chartAt (Model (k + 1)) c.anchor w) =
          c.tensorCoordinateLinearMap (P := N) (s, w) (originalInteriorSection C J N σ (s, w)) := by
  let cT : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n) := .inl c
  have hpA : cT.inclusion p ∈
      {x | parameter (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val) x ∈ B} := by
    simpa only [cT, OriginalTotalCanonicalChart.inclusion, Set.mem_ofPred_eq,
      totalInterior, parameter_original] using hpB
  obtain ⟨U, G, hpU, hG, hU, heG⟩ := hmap cT cT p hp hpA ⟨p, hp, rfl⟩
  refine ⟨U, fun z => (G z).2, hpU, hU,
    contDiff_snd.contDiffOn.comp hG (fun _ _ => mem_univ _), ?_⟩
  intro s hs w hw hz
  have hq : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hw⟩, hU hz⟩
  have hqA : cT.inclusion (s, w) ∈
      {x | parameter (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val) x ∈ B} := by
    simpa only [cT, OriginalTotalCanonicalChart.inclusion, Set.mem_ofPred_eq,
      totalInterior, parameter_original] using hs
  obtain ⟨hd, he⟩ := heG (s, w) hq hqA hz
  have h := congrArg Prod.snd he
  change (G _).2 = (c.totalTensorPretrivialization N hjoint hC hinv
    ⟨totalInterior (fun t q => C t q.val) (s, w),
      originalTotalSection C J N σ (totalInterior (fun t q => C t q.val) (s, w))⟩).2 at h
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq, originalTotalSection_interior] at h
  exact h

/-- The retained-base extraction keeps the entire signed cylinder,
including its seam and all outward radii. -/
theorem originalEndCoefficientExtensionOn_of_chartMapExtensionsOn
    (B : Set Parameter) (σ : OriginalNativeCanonicalSection C J N)
    (hmap : HasOriginalTotalChartMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv
      {x | parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) x ∈ B}
      (originalTotalSectionGraph C J N σ))
    (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain) (hpB : p.1 ∈ B) :
    ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ))) (q : ℝ × (Model k × ℝ) → ℂ),
      (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)) ∈ U ∧
      (U : Set (ℝ × (Model k × ℝ))) ⊆ c.domain ∧ ContDiffOn ℝ ∞ q U ∧
      ∀ (s : Parameter), s ∈ B → ∀ (w : Band δ (IntrinsicBoundary.Point k M)),
        endBandCoordinates w ∈ (chartAt (Model k × ℝ) c.anchor).source →
        (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) ∈ U →
        q (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) =
          c.tensorCoordinateLinearMap (N := N) (s, w) (originalEndSection C J N σ (s, w)) := by
  let cT : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n) := .inr c
  have hpA : cT.inclusion p ∈
      {x | parameter (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val) x ∈ B} := by
    simpa only [cT, OriginalTotalCanonicalChart.inclusion, Set.mem_ofPred_eq,
      parameter_totalCylinder] using hpB
  obtain ⟨U, G, hpU, hG, hU, heG⟩ := hmap cT cT p hp hpA ⟨p, hp, rfl⟩
  refine ⟨U, fun z => (G z).2, hpU, hU,
    contDiff_snd.contDiffOn.comp hG (fun _ _ => mem_univ _), ?_⟩
  intro s hs w hw hz
  have hq : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hw⟩, hU hz⟩
  have hqA : cT.inclusion (s, w) ∈
      {x | parameter (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val) x ∈ B} := by
    simpa only [cT, OriginalTotalCanonicalChart.inclusion, Set.mem_ofPred_eq,
      parameter_totalCylinder] using hs
  obtain ⟨hd, he⟩ := heG (s, w) hq hqA hz
  have h := congrArg Prod.snd he
  change (G _).2 = (c.totalTensorPretrivialization N hjoint hC hinv
    ⟨totalCylinder (fun t q => C t q.val) (s, w),
      originalTotalSection C J N σ (totalCylinder (fun t q => C t q.val) (s, w))⟩).2 at h
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hq, originalTotalSection_end] at h
  exact h

end FsFltz.Geometry.IntrinsicCompletionGluing
