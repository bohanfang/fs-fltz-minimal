import FsFltz.Geometry.IntrinsicCollar
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Order.IntermediateValue

/-!
# Native uniqueness on the full common forward interval

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Smooth extension across a native boundary is the convention
at lines 119–122 and 141. The Hausdorff hypothesis is the convention at
line 120. Only local Euclidean coefficient extensions are used here.

Right-sided local uniqueness at each common-image point, after translating
time, propagates equality by continuous induction. No trajectory is required
to extend to negative native time, and no common chart for the whole
interval is assumed. This is the overlap-compatibility producer for assembling
one-sided collars, not a construction of a completed flow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native right integral curves agree on their entire common interval.
Smooth local coefficient extensions are needed only at points where the
two images agree. They are geometric local regularity hypotheses, rather
than an assumed agreement or a chart bound along the whole trajectory. -/
theorem eqOn_of_native_integralCurveOn_of_common_local_coefficients
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {γ η : ℝ → M} {δ T : ℝ}
    (hcoeff : ∀ t ∈ Ico 0 (min δ T), γ t = η t →
      ∃ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
        e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ γ t ∈ e.source ∧
        ∃ (f : Model (k + 1) → Model (k + 1)) (U : Set (Model (k + 1))),
          IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧
          e.extend (𝓡∂ (k + 1)) (γ t) ∈ U ∧
          ∀ x ∈ e.source, e.extend (𝓡∂ (k + 1)) x ∈ U →
            f (e.extend (𝓡∂ (k + 1)) x) =
              mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
                (e.extend (𝓡∂ (k + 1))) x (Z x))
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ))
    (hη : IsMIntegralCurveOn η Z (Ico 0 T))
    (hzero : γ 0 = η 0) : EqOn γ η (Ico 0 (min δ T)) := by
  intro b hb
  let S : Set ℝ := {t | γ t = η t}
  have hsδ : Icc 0 b ⊆ Ico 0 δ := fun t ht =>
    ⟨ht.1, lt_of_le_of_lt ht.2 (lt_of_lt_of_le hb.2 (min_le_left _ _))⟩
  have hsT : Icc 0 b ⊆ Ico 0 T := fun t ht =>
    ⟨ht.1, lt_of_le_of_lt ht.2 (lt_of_lt_of_le hb.2 (min_le_right _ _))⟩
  have hclosed : IsClosed (S ∩ Icc 0 b) := by
    convert isClosed_Icc.isClosed_eq
      (hγ.continuousOn.mono hsδ) (hη.continuousOn.mono hsT) using 1
    ext t
    simp only [S, mem_inter_iff, mem_ofPred_eq, and_comm]
  have hsub : Icc 0 b ⊆ S := hclosed.Icc_subset_of_forall_mem_nhdsWithin hzero (by
    intro t ht
    have htcommon : t ∈ Ico 0 (min δ T) :=
      ⟨ht.2.1, lt_trans ht.2.2 hb.2⟩
    obtain ⟨e, he, hx, f, U, hU, hf, hxU, hfcoeff⟩ := hcoeff t htcommon ht.1
    have htδ : t < δ := lt_of_lt_of_le htcommon.2 (min_le_left _ _)
    have htT : t < T := lt_of_lt_of_le htcommon.2 (min_le_right _ _)
    have hγshift : IsMIntegralCurveOn (fun s => γ (s + t)) Z (Ico 0 (δ - t)) :=
      (hγ.comp_add t).mono (by
        intro s hs
        exact ⟨by linarith [hs.1, htcommon.1], by linarith [hs.2]⟩)
    have hηshift : IsMIntegralCurveOn (fun s => η (s + t)) Z (Ico 0 (T - t)) :=
      (hη.comp_add t).mono (by
        intro s hs
        exact ⟨by linarith [hs.1, htcommon.1], by linarith [hs.2]⟩)
    obtain ⟨ε, hε, _, heq⟩ := exists_pos_eqOn_of_native_integralCurveOn he hU hf hfcoeff
      (sub_pos.mpr htδ) (sub_pos.mpr htT) hγshift hηshift
      (by simpa only [zero_add] using hx)
      (by simpa only [zero_add] using hxU)
      (by simpa only [zero_add] using (show γ t = η t from ht.1))
    apply mem_of_superset (Ioc_mem_nhdsGT (show t < t + ε by linarith))
    intro s hs
    have heq' := heq (show s - t ∈ Icc 0 ε by constructor <;> linarith [hs.1, hs.2])
    change γ s = η s
    simpa only [sub_add_cancel] using heq')
  exact hsub ⟨hb.1, le_rfl⟩

/-- The pointwise smooth-extension convention for a native vector field
implies uniqueness on the full overlap of two forward integral curves. -/
theorem eqOn_of_native_integralCurveOn
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    (hcoeff : ∀ x : M,
      ∃ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
        e ∈ atlas (EuclideanHalfSpace (k + 1)) M ∧ x ∈ e.source ∧
        ∃ (f : Model (k + 1) → Model (k + 1)) (U : Set (Model (k + 1))),
          IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧
          ∀ y ∈ e.source, e.extend (𝓡∂ (k + 1)) y ∈ U →
            f (e.extend (𝓡∂ (k + 1)) y) =
              mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
                (e.extend (𝓡∂ (k + 1))) y (Z y))
    {γ η : ℝ → M} {δ T : ℝ}
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ))
    (hη : IsMIntegralCurveOn η Z (Ico 0 T))
    (hzero : γ 0 = η 0) : EqOn γ η (Ico 0 (min δ T)) :=
  eqOn_of_native_integralCurveOn_of_common_local_coefficients
    (fun t _ _ => hcoeff (γ t)) hγ hη hzero

end FsFltz.Geometry.IntrinsicCollar
