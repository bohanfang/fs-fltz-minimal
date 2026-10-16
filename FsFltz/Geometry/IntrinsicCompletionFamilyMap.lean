import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas

/-!
# Smooth maps from the original completion family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. A map is smooth when its native interior formula
is smooth and its cylinder formula is smooth on an end strip containing
the seam. Positive inward radii use the actual mixed chart germs, so the
original collar width is retained.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Topology

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

local instance : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞
    (Band δ (IntrinsicBoundary.Point k M)) := band_isManifold δ

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H N]

include hboundary hmix in
/-- Real end germs and smooth native interiors suffice on the entire
original atlas; no cutoff of the original collar width is needed. -/
theorem contMDiff_totalFamily_of_end_strip
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → N)
    {ε : ℝ} (hε : 0 < ε)
    (hi : ContMDiff (familyModel (k + 1)) I ∞
      (f ∘ totalInterior (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hc : ContMDiffOn (familyModel (k + 1)) I ∞
      (f ∘ totalCylinder (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
      {p | p.2.val.1 < ε}) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) I ∞ f := by
  apply (contMDiff_totalFamily_iff hδ C hboundary hzero hjoint hmix f).mpr
  refine ⟨hi, ?_⟩
  intro p
  by_cases hp : p.2.val.1 < ε
  · have hr : Continuous (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
        p.2.val.1) := continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    exact (hc p hp).contMDiffAt ((isOpen_lt hr continuous_const).mem_nhds hp)
  · have hs : 0 < p.2.val.1 := lt_of_lt_of_le hε (le_of_not_gt hp)
    let u : Half δ (IntrinsicBoundary.Point k M) := halfOfNonneg p.2 hs.le
    have hnot : ¬(𝓡∂ (k + 1)).IsBoundaryPoint (C p.1 u.val) := by
      rw [hboundary]
      exact ne_of_gt hs
    let x : Parameter × IntrinsicInterior.Point k M :=
      (p.1, ⟨C p.1 u.val,
        ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mpr hnot⟩)
    have he : totalCylinder (fun t p => C t p.val) p =
        totalInterior (fun t p => C t p.val) x := by
      apply (totalInterior_eq_totalCylinder_iff (fun t p => C t p.val) hboundary x p).mpr
        ⟨rfl, hs, rfl⟩ |>.symm
    obtain ⟨g, hg, hgx, hgeq⟩ :=
      totalCylinder_interior_germ hδ C hboundary hzero hjoint hmix p x he
    apply ((hi _).comp p hg).congr_of_eventuallyEq
    filter_upwards [hgeq] with q hq
    exact congrArg f hq

end FsFltz.Geometry.IntrinsicCompletionGluing
