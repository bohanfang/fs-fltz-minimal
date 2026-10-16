import FsFltz.Geometry.LiouvilleLocalFlow
import Mathlib.Analysis.ODE.Gronwall

/-!
# Complete smooth flows of fields with linear growth

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 799–818;
`geoemtric-part-fsf.tex`, `thm:target` / `g:complete`, lines 353–361,
and `sec:lean`, lines 805–840. This is the Euclidean continuation producer
used for the original field's cover. A smooth compact cutoff has a constructed
global flow. Gronwall bounds its trajectories in both time directions, so a
cutoff equal to one on a sufficiently large ball solves the original equation
on any prescribed finite time interval. Native uniqueness glues these curves
to all real times; native smooth dependence gives the resulting smooth flow.

Neither a global solution nor completeness is among the hypotheses.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function Metric

namespace FsFltz.Geometry.LinearGrowthCompleteFlow

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- For a vector space, the native manifold ODE is the ordinary derivative equation. -/
theorem hasDerivAt_of_isMIntegralCurve {V : E → E} {γ : ℝ → E}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ V) (t : ℝ) :
    HasDerivAt γ (V (γ t)) t := by
  apply (hasMFDerivAt_iff_hasFDerivAt.mp (hγ t)).hasDerivAt.congr_deriv
  change (1 : ℝ) • V (γ t) = V (γ t)
  simp

/-- Linear growth controls every bounded time interval in both directions. -/
theorem norm_le_of_linear_growth {V : E → E} {γ : ℝ → E} {C : ℝ}
    (hC : 0 < C) (hV : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖))
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) (t : ℝ) :
    ‖γ t‖ ≤ (‖γ 0‖ + 1) * Real.exp (C * |t|) - 1 := by
  have hforward {α : ℝ → E} (hα : ∀ s, HasDerivAt α (V (α s)) s)
      {s : ℝ} (hs : 0 ≤ s) :
      ‖α s‖ ≤ gronwallBound ‖α 0‖ C C s := by
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (fun r _ => (hα r).continuousAt.continuousWithinAt)
      (fun r _ => (hα r).hasDerivWithinAt)
      (le_refl ‖α 0‖)
      (fun r _ => by simpa only [mul_add, mul_one, add_comm] using hV (α r))
      s (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)
    simpa only [sub_zero] using hb
  have hbackward {s : ℝ} (hs : 0 ≤ s) :
      ‖γ (-s)‖ ≤ gronwallBound ‖γ 0‖ C C s := by
    have hd : ∀ r, HasDerivAt (fun u => γ (-u)) (-V (γ (-r))) r := by
      intro r
      simpa only [Function.comp_def, neg_one_smul] using
        (hγ (-r)).scomp r (hasDerivAt_neg r)
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le
      (fun r _ => (hd r).continuousAt.continuousWithinAt)
      (fun r _ => (hd r).hasDerivWithinAt)
      (by simp : ‖γ (-0)‖ ≤ ‖γ 0‖)
      (fun r _ => by simpa only [norm_neg, mul_add, mul_one, add_comm] using hV (γ (-r)))
      s (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)
    simpa only [sub_zero] using hb
  have hb : ‖γ t‖ ≤ gronwallBound ‖γ 0‖ C C |t| := by
    by_cases ht : 0 ≤ t
    · simpa only [abs_of_nonneg ht] using hforward hγ ht
    · have ht' : 0 ≤ -t := by linarith
      simpa only [neg_neg, abs_of_neg (lt_of_not_ge ht)] using hbackward ht'
  rw [gronwallBound_of_K_ne_0 hC.ne', div_self hC.ne'] at hb
  simpa only [one_mul] using hb.trans_eq (by ring)

variable [CompleteSpace E] [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Every prescribed finite symmetric time interval has a solution of the
original field. The compact cutoff is constructed large enough using the
two-sided Gronwall bound; its trajectory is proved to remain where it is one. -/
theorem exists_integralCurveOn {V : E → E} (hV : ContDiff ℝ ∞ V)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖))
    (x : E) (a : ℝ) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ V (Ioo (-a) a) := by
  let R : ℝ := (‖x‖ + 1) * Real.exp (C * |a|) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  let V' : E → E := fun y => χ y • V y
  have hV' : ContDiff ℝ ∞ V' := χ.contDiff.smul hV
  have hgrowth : ∀ y, ‖V' y‖ ≤ C * (1 + ‖y‖) := by
    intro y
    calc
      ‖V' y‖ = χ y * ‖V y‖ := by
        simp only [V', norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      _ ≤ ‖V y‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
      _ ≤ C * (1 + ‖y‖) := hbound y
  obtain ⟨F, _, hF⟩ := CollarFlow.exists_supported_smoothFlow
    (I := 𝓘(ℝ, E)) V' (contMDiff_vectorSpace_iff_contDiff.mpr hV')
    χ.hasCompactSupport (fun y hy => by
      simp only [V', image_eq_zero_of_notMem_tsupport hy, zero_smul])
  have hcurve : ∀ t, HasDerivAt (fun s => F s x) (V' (F t x)) t :=
    hasDerivAt_of_isMIntegralCurve (hF x)
  refine ⟨fun t => F t x, F.map_zero_apply x, ?_⟩
  intro t ht
  have htabs : |t| ≤ |a| :=
    (abs_lt.mpr ht).le.trans (le_abs_self a)
  have hnorm : ‖F t x‖ ≤ R := by
    have hb := norm_le_of_linear_growth hC hgrowth hcurve t
    rw [F.map_zero_apply] at hb
    calc
      ‖F t x‖ ≤ (‖x‖ + 1) * Real.exp (C * |t|) - 1 := hb
      _ ≤ (‖x‖ + 1) * Real.exp (C * |a|) - 1 := by gcongr
      _ ≤ R := by dsimp [R]; linarith
  have hone : χ (F t x) = 1 :=
    χ.one_of_mem_closedBall (by simpa only [χ, mem_closedBall, dist_zero_right] using hnorm)
  simpa only [V', hone, one_smul] using (hF x t).hasMFDerivWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- A smooth finite-dimensional field with global linear growth has actual
integral curves through every point for all real times. Native uniqueness
glues the constructed finite-horizon curves. -/
theorem exists_integralCurve {V : E → E} (hV : ContDiff ℝ ∞ V)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖)) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (V (γ t)) t := by
  have hv := contMDiff_vectorSpace_iff_contDiff.mpr hV
  obtain ⟨γ, hγ₀, hγ⟩ :=
    (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo
      (hv.of_le (by simp)) x).mpr (exists_integralCurveOn hV hC hbound x)
  exact ⟨γ, hγ₀, hasDerivAt_of_isMIntegralCurve hγ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Linear growth constructs a jointly smooth all-real flow of the actual
field. The action law follows from native uniqueness and the joint smoothness
from the existing smooth-dependence producer. -/
theorem exists_smooth_flow {V : E → E} (hV : ContDiff ℝ ∞ V)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, ‖V x‖ ≤ C * (1 + ‖x‖)) :
    ∃ F : Flow ℝ E,
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ∀ x t, HasDerivAt (fun s => F s x) (V (F t x)) t := by
  have hv := contMDiff_vectorSpace_iff_contDiff.mpr hV
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hglobal := fun x =>
    (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv₁ x).mpr
      (exists_integralCurveOn hV hC hbound x)
  choose γ hγ₀ hγ using hglobal
  let φ : ℝ → E → E := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hcomp : ∀ s t x, φ (s + t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := CollarFlow.contMDiff_joint_of_isMIntegralCurve hv φ hself hγ
  have hs' : ContDiff ℝ ∞ (fun p : ℝ × E => φ p.1 p.2) :=
    (hs.comp (contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff)).contDiff
  exact ⟨⟨φ, hs.continuous, hcomp, hself⟩, hs',
    fun x => hasDerivAt_of_isMIntegralCurve (hγ x)⟩

end FsFltz.Geometry.LinearGrowthCompleteFlow
