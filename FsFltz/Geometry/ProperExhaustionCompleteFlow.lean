import FsFltz.Geometry.LinearGrowthCompleteFlow
import FsFltz.Geometry.FlowAbsorption

/-!
# Complete flow from a proper exhaustion estimate

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 803–812;
`geoemtric-part-fsf.tex`, `g:initial`, lines 373–379. A smooth nonnegative
exhaustion with compact sublevels and at most linear derivative growth
prevents escape in finite time in either direction. Compactly supported
cutoffs construct the finite-interval solutions; uniqueness and smooth
dependence then construct the actual complete flow.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function Metric

namespace FsFltz.Geometry

private theorem scalar_gronwall_two_sided {g g' : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hnonneg : ∀ t, 0 ≤ g t) (hbound : ∀ t, |g' t| ≤ C * (1 + g t))
    (t : ℝ) : g t ≤ (g 0 + 1) * Real.exp (C * |t|) - 1 := by
  have hforward {a a' : ℝ → ℝ} (ha : ∀ s, HasDerivAt a (a' s) s)
      (ha0 : ∀ s, 0 ≤ a s) (hb : ∀ s, |a' s| ≤ C * (1 + a s))
      {s : ℝ} (hs : 0 ≤ s) : a s ≤ gronwallBound (a 0) C C s := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (fun r _ => (ha r).continuousAt.continuousWithinAt)
      (fun r _ => (ha r).hasDerivWithinAt)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (ha0 0)] using le_refl (a 0))
      (fun r _ => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (ha0 r), mul_add, mul_one, add_comm]
          using hb r)
      s (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (ha0 s)] using h
  have hb : g t ≤ gronwallBound (g 0) C C |t| := by
    by_cases ht : 0 ≤ t
    · simpa only [abs_of_nonneg ht] using hforward hg hnonneg hbound ht
    · have hrev : ∀ r, HasDerivAt (fun u => g (-u)) (-g' (-r)) r := by
        intro r
        simpa only [Function.comp_def, mul_neg_one] using
          (hg (-r)).comp r (hasDerivAt_neg r)
      have h := hforward hrev (fun r => hnonneg (-r))
        (fun r => by simpa only [abs_neg] using hbound (-r)) (le_of_lt (neg_pos.mpr (lt_of_not_ge ht)))
      simpa only [neg_neg, neg_zero, abs_of_neg (lt_of_not_ge ht)] using h
  rw [gronwallBound_of_K_ne_0 hC.ne', div_self hC.ne'] at hb
  simpa only [one_mul] using hb.trans_eq (by ring)

namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- A proper nonnegative exhaustion and a linear scalar derivative bound
construct an integral curve on every prescribed finite time interval. -/
theorem exists_integralCurveOn_of_proper_exhaustion {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorField Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hnonneg : ∀ x, 0 ≤ ρ x)
    (hcompact : ∀ A : ℝ, 0 ≤ A → IsCompact {x | ρ x ≤ A})
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x, |M.scalarDerivative ρ x (Z x)| ≤ C * (1 + ρ x))
    (x : M.Point) (a : ℝ) :
    ∃ γ : ℝ → M.Point, γ 0 = x ∧ IsMIntegralCurveOn γ Z (Ioo (-a) a) := by
  let R := (ρ x + 1) * Real.exp (C * |a|) + 1
  have hR : 0 < R := by
    have hx := hnonneg x
    dsimp [R]
    positivity
  let χ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  let V : (y : M.Point) → M.Tangent y := fun y => χ (ρ y) • Z y
  have hV : M.IsSmoothVectorField V :=
    M.isSmoothVectorField_of_contMDiff_section
      ((χ.contDiff.contMDiff.comp hρ).smul_section hZ.contMDiff_section)
  obtain ⟨F, hF, hode⟩ := M.exists_supported_smoothFlow V hV
    (hcompact (R + 1) (by linarith)) (fun y hy => by
      have hzero : χ (ρ y) = 0 := by
        apply Function.notMem_support.mp
        rw [χ.support_eq]
        simp only [χ, mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg y)]
        exact not_lt_of_ge (le_of_lt (lt_of_not_ge hy))
      simp only [V, hzero, zero_smul])
  let F' : CompleteLiouvilleFlow M V := {
    flow := F
    smooth_action := hF
    solves := fun y => (isMIntegralCurve_iff_chart_solves M V _
      ((hF.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp (hode y) }
  have hder := F'.hasDerivAt_scalar_orbit ρ hρ x
  have hscalar (t : ℝ) : |M.scalarDerivative ρ (F t x) (V (F t x))| ≤
      C * (1 + ρ (F t x)) := by
    simp only [V, scalarDerivative, map_smul, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg _) χ.le_one).trans (hbound _)
  refine ⟨fun t => F t x, F.map_zero_apply x, ?_⟩
  intro t ht
  have htabs : |t| ≤ |a| := (abs_lt.mpr ht).le.trans (le_abs_self a)
  have hrho : ρ (F t x) ≤ R := by
    have hb := scalar_gronwall_two_sided hC hder (fun s => hnonneg (F s x)) hscalar t
    change ρ (F t x) ≤ (ρ (F 0 x) + 1) * Real.exp (C * |t|) - 1 at hb
    rw [F.map_zero_apply] at hb
    calc
      ρ (F t x) ≤ (ρ x + 1) * Real.exp (C * |t|) - 1 := hb
      _ ≤ (ρ x + 1) * Real.exp (C * |a|) - 1 := by
        gcongr
        linarith [hnonneg x]
      _ ≤ R := by dsimp [R]; linarith
  have hone : χ (ρ (F t x)) = 1 := χ.one_of_mem_closedBall (by
    simpa only [χ, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg _)] using hrho)
  simpa only [V, hone, one_smul] using (hode x t).hasMFDerivWithinAt

/-- Proper exhaustion control constructs an actual all-real jointly smooth
flow of the supplied smooth vector field, with its native differential ODE. -/
theorem exists_completeFlow_of_proper_exhaustion {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorField Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hnonneg : ∀ x, 0 ≤ ρ x)
    (hcompact : ∀ A : ℝ, 0 ≤ A → IsCompact {x | ρ x ≤ A})
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x, |M.scalarDerivative ρ x (Z x)| ≤ C * (1 + ρ x)) :
    Nonempty (CompleteLiouvilleFlow M Z) := by
  have hv := hZ.contMDiff_section
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hglobal := fun x =>
    (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv₁ x).mpr
      (M.exists_integralCurveOn_of_proper_exhaustion Z hZ ρ hρ hnonneg hcompact hC hbound x)
  choose γ hγ₀ hγ using hglobal
  let φ : ℝ → M.Point → M.Point := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hcomp : ∀ s t x, φ (s + t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := CollarFlow.contMDiff_joint_of_isMIntegralCurve hv φ hself hγ
  let F : Flow ℝ M.Point := ⟨φ, hs.continuous, hcomp, hself⟩
  refine ⟨⟨F, hs, ?_⟩⟩
  intro x
  exact (isMIntegralCurve_iff_chart_solves M Z _
    ((hs.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp (hγ x)

end SmoothManifold
end FsFltz.Geometry
