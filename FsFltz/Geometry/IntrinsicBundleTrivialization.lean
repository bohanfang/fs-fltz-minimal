import FsFltz.Geometry.IntrinsicBundleSplice

/-!
# Global trivialization of intrinsic smooth interval bundles

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. The compact bundle in a pair deformation can be presented on a
fixed fibre. The interval argument below retains a property of actual
trivializations, provided that property holds locally and survives smooth
splicing at interior seams. Its smooth application uses joint extension
germs in both directions against the original bundle atlas.

This is a foundation for compact family presentations. Transport of all
pair data and the corresponding completed families remains a separate
bridge; this module does not assert the geometric target `thm:target`.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {F : Type*} [TopologicalSpace F] {E : Parameter → Type*}
  [TopologicalSpace (TotalSpace F E)]

/-- A property of bundle trivializations which holds on a chart near
each parameter and survives interior splicing holds on a global chart.
The supremum construction only splices strictly before a missing
supremum, so it never needs a cutoff at a parameter endpoint. -/
theorem exists_global_trivialization_of_splice
    (P : Trivialization F (π F E) → Prop)
    (hlocal : ∀ t : Parameter, ∃ e : Trivialization F (π F E), P e ∧ t ∈ e.baseSet)
    (hsplice : ∀ eL eR : Trivialization F (π F E), P eL → P eR →
      ∀ c : Parameter, c ∈ eL.baseSet → c ∈ eR.baseSet →
      0 < c.val → c.val < 1 →
      ∃ T : Trivialization F (π F E), P T ∧
        T.baseSet = (Iic c).ite eL.baseSet eR.baseSet) :
    ∃ e : Trivialization F (π F E), P e ∧ e.baseSet = univ := by
  let a := parameterZero
  let b := parameterOne
  have hab : a ≤ b := by change (0 : ℝ) ≤ 1; norm_num
  obtain ⟨ea, heaP, hea⟩ := hlocal a
  let s : Set Parameter := {x ∈ Icc a b |
    ∃ e : Trivialization F (π F E), P e ∧ Icc a x ⊆ e.baseSet}
  have ha : a ∈ s := ⟨left_mem_Icc.mpr hab, ea, heaP, by simp [hea]⟩
  have sne : s.Nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have hcs : c ∈ s := by
    by_cases hcs : c ∈ s
    · exact hcs
    rcases hc.1.eq_or_lt with heq | hac
    · exact (hcs (heq ▸ ha)).elim
    obtain ⟨ec, hecP, hec⟩ := hlocal c
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.baseSet :=
      (mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset hac).mp
        (mem_nhdsWithin_of_mem_nhds (ec.open_baseSet.mem_nhds hec))
    obtain ⟨d, hdS, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    have hdc : d < c := lt_of_le_of_ne hd.2 (fun heq => hcs (heq ▸ hdS))
    obtain ⟨hdab, ead, headP, had⟩ := hdS
    have hd0 : 0 < d.val := by
      change a < d
      exact hc'.1.trans_lt hd.1
    have hd1 : d.val < 1 := by
      change d < b
      exact hdc.trans_le hc.2
    obtain ⟨T, hTP, hTbase⟩ := hsplice ead ec headP hecP d
      (had ⟨hdab.1, le_rfl⟩) (hc'e hd) hd0 hd1
    refine ⟨hc, T, hTP, ?_⟩
    rw [hTbase]
    apply subset_ite.mpr
    exact ⟨fun x hx => had ⟨hx.1.1, hx.2⟩,
      fun x hx => hc'e ⟨hd.1.trans (not_le.mp hx.2), hx.1.2⟩⟩
  obtain ⟨_, ec, hecP, hec⟩ := hcs
  have hcb : c = b := by
    rcases hc.2.eq_or_lt with heq | hcb
    · exact heq
    obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.baseSet :=
      (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hcb).mp
        (mem_nhdsWithin_of_mem_nhds
          (ec.open_baseSet.mem_nhds (hec ⟨hc.1, le_rfl⟩)))
    have had : Ico a d ⊆ ec.baseSet :=
      Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
    obtain ⟨d', hcd', hd'd⟩ := exists_between hdcb.1
    have hd's : d' ∈ s :=
      ⟨⟨hc.1.trans hcd'.le, hd'd.le.trans hdcb.2⟩, ec, hecP,
        (Icc_subset_Ico_right hd'd).trans had⟩
    exact ((hsc.1 hd's).not_gt hcd').elim
  refine ⟨ec, hecP, eq_univ_of_forall ?_⟩
  intro t
  apply hec
  rw [hcb]
  exact t.property

variable {d : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]
  [∀ t, TopologicalSpace (E t)] [SmoothCompactBundle I (F := F) E]

/-- An intrinsic smooth compact bundle over the parameter interval has
an actual global trivialization. Its transitions against every original
atlas chart have joint open smooth extension germs in both directions,
including at the parameter endpoints and at the spatial boundary.
The proof constructs the chart from the local atlas and the smoothly
corrected splice; a global chart is not part of the input bundle. -/
theorem exists_global_smooth_trivialization :
    ∃ e : Trivialization F (π F E), e.baseSet = univ ∧
      ∀ e' ∈ trivializationAtlas F E,
        HasSmoothTransition I e e' ∧ HasSmoothTransition I e' e := by
  obtain ⟨e, he, hbase⟩ := exists_global_trivialization_of_splice
    (CompatibleTrivialization I E)
    (fun t => ⟨trivializationAt F E t,
      compatibleTrivialization_of_mem (trivialization_mem_atlas F E t),
      mem_baseSet_trivializationAt F E t⟩)
    (fun eL eR heL heR c hcL hcR hc0 hc1 =>
      exists_compatible_splice eL eR heL heR c hcL hcR hc0 hc1)
  exact ⟨e, hbase, he⟩

end FsFltz.Geometry.IntrinsicSmoothBundle
