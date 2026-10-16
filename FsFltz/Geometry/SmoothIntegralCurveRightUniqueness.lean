import FsFltz.Geometry.FlowBridge
import FsFltz.Geometry.IntrinsicCollarUniqueness
import Mathlib.Topology.Order.IntermediateValue

/-!
# Right interval uniqueness on a boundaryless smooth manifold

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 153–158, and
`sec:lean`, lines 805–813. Native inward collar curves have a right derivative
at their initial time. Smooth chart coefficients give a local Lipschitz ball;
right ODE uniqueness and continuous induction retain that initial time.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.SmoothManifold

private theorem exists_pos_eqOn_integralCurveOn {d : ℕ} (N : SmoothManifold d)
    {Z : (x : N.Point) → N.Tangent x} (hZ : N.IsSmoothVectorField Z)
    {γ η : ℝ → N.Point} {δ : ℝ} (hδ : 0 < δ)
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ))
    (hη : IsMIntegralCurveOn η Z (Ico 0 δ)) (hzero : γ 0 = η 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ EqOn γ η (Icc 0 ε) := by
  let a := γ 0
  let e := chartAt (Model d) a
  let W := N.vectorInChart a Z
  have ha : a ∈ e.source := mem_chart_source _ _
  obtain ⟨r, hr, hsub, K, hK⟩ :=
    IntrinsicCollar.exists_closedBall_lipschitzOnWith_of_contDiffOn
      e.open_target (hZ a) (e.map_source ha)
  let B : Set N.Point := e.source ∩ e ⁻¹' Metric.closedBall (e a) r
  have hB : B ∈ 𝓝 a := inter_mem (e.open_source.mem_nhds ha)
    ((e.continuousAt ha).preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr))
  have hBη : B ∈ 𝓝 (η 0) := by rw [← hzero]; exact hB
  have hboth : γ ⁻¹' B ∩ η ⁻¹' B ∈ 𝓝[Ico 0 δ] (0 : ℝ) :=
    inter_mem ((hγ.continuousOn 0 ⟨le_rfl, hδ⟩).preimage_mem_nhdsWithin hB)
      ((hη.continuousOn 0 ⟨le_rfl, hδ⟩).preimage_mem_nhdsWithin hBη)
  obtain ⟨s, hs, hssub⟩ := Metric.mem_nhdsWithin_iff.mp hboth
  let ε := min s δ / 2
  have hε : 0 < ε := half_pos (lt_min hs hδ)
  have hεs : ε < s := (half_lt_self (lt_min hs hδ)).trans_le (min_le_left _ _)
  have hεδ : ε < δ := (half_lt_self (lt_min hs hδ)).trans_le (min_le_right _ _)
  have hinterval : Icc 0 ε ⊆ Ico 0 δ := fun t ht => ⟨ht.1, ht.2.trans_lt hεδ⟩
  have hmem : ∀ t ∈ Icc (0 : ℝ) ε, γ t ∈ B ∧ η t ∈ B := by
    intro t ht
    apply hssub
    refine ⟨?_, hinterval ht⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hεs
  have hder {c : ℝ → N.Point} (hc : IsMIntegralCurveOn c Z (Ico 0 δ))
      {t : ℝ} (ht : t ∈ Ico 0 δ) (hx : c t ∈ e.source) :
      HasDerivWithinAt (fun s => e (c s)) (W (e (c t))) (Ici t) t := by
    have he' := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt hx
    have hd := hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp
      (he'.hasMFDerivAt.comp_hasMFDerivWithinAt t ((hc t ht).mono_of_mem_nhdsWithin
          (mem_of_superset (Ico_mem_nhdsGE ht.2) (Ico_subset_Ico_left ht.1))))
    apply hd.hasDerivWithinAt.congr_deriv
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e (c t) ((1 : ℝ) • Z (c t)) = _
    rw [one_smul]
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e (c t) (Z (c t)) =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) e (e.symm (e (c t)))
        (Z (e.symm (e (c t))))
    rw [e.left_inv hx]
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => W)
    (s := fun _ => Metric.closedBall (e a) r) (fun _ _ => hK)
    (e.continuousOn.comp (hγ.continuousOn.mono hinterval) (fun t ht => (hmem t ht).1.1))
    (fun t ht => hder hγ (hinterval (Ico_subset_Icc_self ht)) (hmem t (Ico_subset_Icc_self ht)).1.1)
    (fun t ht => (hmem t (Ico_subset_Icc_self ht)).1.2)
    (e.continuousOn.comp (hη.continuousOn.mono hinterval) (fun t ht => (hmem t ht).2.1))
    (fun t ht => hder hη (hinterval (Ico_subset_Icc_self ht)) (hmem t (Ico_subset_Icc_self ht)).2.1)
    (fun t ht => (hmem t (Ico_subset_Icc_self ht)).2.2) (congrArg e hzero)
  exact ⟨ε, hε, hεδ, fun t ht => e.injOn (hmem t ht).1.1 (hmem t ht).2.1 (heq ht)⟩

/-- Smooth boundaryless fields have unique native integral curves on a
right half-open interval, including its initial time. -/
theorem eqOn_of_isMIntegralCurveOn_Ico {d : ℕ} (N : SmoothManifold d)
    {Z : (x : N.Point) → N.Tangent x} (hZ : N.IsSmoothVectorField Z)
    {γ η : ℝ → N.Point} {δ : ℝ}
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ))
    (hη : IsMIntegralCurveOn η Z (Ico 0 δ)) (hzero : γ 0 = η 0) :
    EqOn γ η (Ico 0 δ) := by
  intro b hb
  let S : Set ℝ := {t | γ t = η t}
  have hs : Icc 0 b ⊆ Ico 0 δ := fun t ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  have hclosed : IsClosed (S ∩ Icc 0 b) := by
    convert isClosed_Icc.isClosed_eq (hγ.continuousOn.mono hs) (hη.continuousOn.mono hs) using 1
    ext t
    simp only [S, mem_inter_iff, mem_ofPred_eq, and_comm]
  have hsub : Icc 0 b ⊆ S := hclosed.Icc_subset_of_forall_mem_nhdsWithin hzero (by
    intro t ht
    have htδ : t < δ := ht.2.2.trans hb.2
    have hγshift : IsMIntegralCurveOn (fun s => γ (s + t)) Z (Ico 0 (δ - t)) :=
      (hγ.comp_add t).mono (by
        intro s hs'
        exact ⟨by linarith [hs'.1, ht.2.1], by linarith [hs'.2]⟩)
    have hηshift : IsMIntegralCurveOn (fun s => η (s + t)) Z (Ico 0 (δ - t)) :=
      (hη.comp_add t).mono (by
        intro s hs'
        exact ⟨by linarith [hs'.1, ht.2.1], by linarith [hs'.2]⟩)
    obtain ⟨ε, hε, _, heq⟩ := exists_pos_eqOn_integralCurveOn N hZ
      (sub_pos.mpr htδ) hγshift hηshift
        (by simpa only [zero_add] using (show γ t = η t from ht.1))
    apply mem_of_superset (Ioc_mem_nhdsGT (show t < t + ε by linarith))
    intro s hs'
    have heq' := heq (show s - t ∈ Icc 0 ε by constructor <;> linarith [hs'.1, hs'.2])
    change γ s = η s
    simpa only [sub_add_cancel] using heq')
  exact hsub ⟨hb.1, le_rfl⟩

end FsFltz.Geometry.SmoothManifold
