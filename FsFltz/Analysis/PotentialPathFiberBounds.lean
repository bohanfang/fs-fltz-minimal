import FsFltz.Analysis.PotentialPathMargin

/-!
# Logarithmic full-fiber end bounds for the chosen potential path

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 770–795,
and matching truncations, lines 1011–1049. The actual inverse-Hessian
scalar and the metric radial square are used throughout. Coefficient and
potential parameters are independent. These local estimates do not assert
flow completeness, a completion marking, or a compact pair family.
-/

noncomputable section

namespace FsFltz

open scoped ContDiff Topology
open Filter

variable {n : ℕ}

/-- A half-radius bound gives the source's intrinsic margin in any positive
potential metric. It includes the empty bounded-value end in rank one. -/
theorem potentialMetricFiberDefect_lower_of_half_radial_bound
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n)
    (hr : 0 ≤ metricRadialSq H y.1) (ha : 0 < toricInverseMetricSq H I y)
    (hb : ‖b0 I y‖ ≤
      Real.sqrt (metricRadialSq H y.1) * Real.sqrt (toricInverseMetricSq H I y) / 2) :
    metricRadialSq H y.1 / 2 ≤ potentialMetricFiberDefect H I y := by
  have hr2 := Real.sq_sqrt hr
  have hg2 := Real.sq_sqrt ha.le
  have hsq : Complex.normSq (b0 I y) ≤
      metricRadialSq H y.1 * toricInverseMetricSq H I y / 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have hprod : 0 ≤ Real.sqrt (metricRadialSq H y.1) *
        Real.sqrt (toricInverseMetricSq H I y) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [norm_nonneg (b0 I y), sq_nonneg
      (Real.sqrt (metricRadialSq H y.1) * Real.sqrt (toricInverseMetricSq H I y) / 2 - ‖b0 I y‖)]
  have hdiv : Complex.normSq (b0 I y) / toricInverseMetricSq H I y ≤
      metricRadialSq H y.1 / 4 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hsq]
  dsimp [potentialMetricFiberDefect]
  linarith

/-- One logarithmic metric radius multiplier works for the coefficient
path and every positive symmetric metric with the fixed Hessian bounds.
The coefficient error, metric dominance, and exponential growth are all
proved producers; no fiber-end estimate is supplied as a hypothesis. -/
theorem ToricInput.coefficientPath_metric_logarithmic_fiber_end_estimate
    (I : ToricInput n) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        (∀ v, inner ℝ (H v) v ≤ C * ‖v‖ ^ 2) →
        F * β ≤ Real.sqrt (metricRadialSq H y.1) →
        ‖W (I.alongCoefficientPath t) y‖ ≤ Real.exp β →
          0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
            metricRadialSq H y.1 / 2 ≤
              potentialMetricFiberDefect H (I.alongCoefficientPath t) y := by
  obtain ⟨d, hd, L, hL, hgrad⟩ := I.coefficientPath_inverseMetric_dominant_lowerBound hC
  obtain ⟨B, hB, hnorm⟩ := I.coefficientPath_norm_b0_bound_by_W
  obtain ⟨_, _, D, hD, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨A, hA, e, he, hgrowth⟩ :=
    I.coefficientPath_maxMonomialMagnitude_exponential_lowerBound
  let k := Real.sqrt c
  let U := Real.sqrt C
  have hk : 0 < k := Real.sqrt_pos.mpr hc
  have hU : 0 < U := Real.sqrt_pos.mpr hC
  let D' := D / k
  let e' := e / U
  have hD' : 0 < D' := div_pos hD hk
  have he' : 0 < e' := div_pos he hU
  let F := 2 / e'
  have hF : 0 < F := div_pos (by norm_num) he'
  let z := 4 * D' / (d * A)
  have hz : 0 < z := div_pos (by positivity) (mul_pos hd hA)
  let β₀ := max 1 (max (U * L / F) (max (4 * B / (d * F)) (Real.log z))) + 1
  have hβ₀ : 0 < β₀ := by
    dsimp [β₀]
    exact add_pos_of_pos_of_nonneg (zero_lt_one.trans_le (le_max_left _ _)) zero_le_one
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ t ht y H hsymm hlower hupper hy hW
  let J := I.alongCoefficientPath t
  let r := Real.sqrt (metricRadialSq H y.1)
  let ρ := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (toricInverseMetricSq H J y)
  let M := maxMonomialMagnitude J y
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hM : 0 < M := J.maxMonomialMagnitude_pos y
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower v)
  obtain ⟨hradlo, hradup⟩ := metricRadialSq_radius_bounds H hc hC hlower hupper y.1
  have hβmax : max 1 (max (U * L / F) (max (4 * B / (d * F)) (Real.log z))) ≤ β :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hβ
  have hLβ : U * L / F ≤ β :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hβmax)
  have hBβ : 4 * B / (d * F) ≤ β :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβmax))
  have hzβ : Real.log z ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβmax))
  have hLrad : L ≤ ρ := by
    have hLF := (div_le_iff₀ hF).mp hLβ
    have hUL : U * L ≤ U * ρ := by nlinarith only [hLF, hy, hradup]
    exact (mul_le_mul_iff_right₀ hU).mp hUL
  have hBrad : 4 * B ≤ d * r := by
    have hBF := (div_le_iff₀ (mul_pos hd hF)).mp hBβ
    have hm := mul_le_mul_of_nonneg_left hy hd.le
    nlinarith only [hBF, hm]
  have hgrad' : d * M ≤ g := hgrad t ht y hLrad H hsymm hpos hupper
  have ha : 0 < toricInverseMetricSq H J y :=
    Real.sqrt_pos.mp ((mul_pos hd hM).trans_le hgrad')
  have htwobeta : 2 * β ≤ e' * r := by
    have hm := mul_le_mul_of_nonneg_left hy he'.le
    have hFe : e' * F = 2 := by dsimp [F]; field_simp
    change e' * (F * β) ≤ e' * r at hm
    rw [← mul_assoc, hFe] at hm
    exact hm
  have hexp : e' * r ≤ e * ρ := by
    have hm := mul_le_mul_of_nonneg_left hradup he'.le
    have hcancel : e' * (U * ρ) = e * ρ := by dsimp [e', U]; field_simp
    exact hm.trans_eq hcancel
  have hMlarge : 4 * D' * Real.exp β ≤ d * M := by
    have hcomp := Real.exp_le_exp.mpr (show β + Real.log z ≤ e * ρ by linarith)
    rw [Real.exp_add, Real.exp_log hz] at hcomp
    have hscaled := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hcomp hA.le).trans (hgrowth t ht y)) hd.le
    have heq : d * (A * (Real.exp β * z)) = 4 * D' * Real.exp β := by
      dsimp [z]
      field_simp
    rw [heq] at hscaled
    exact hscaled
  have hfirst : 4 * (D' * r * Real.exp β) ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_left (hMlarge.trans hgrad') hr
    nlinarith only [hm]
  have hsecond : 4 * B * M ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_right hBrad hM.le
    have hgg := mul_le_mul_of_nonneg_left hgrad' hr
    nlinarith only [hm, hgg]
  have hheight' : supportHeight I y.1 ≤ D' * r := by
    have hρ : ρ ≤ r / k := (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hradlo)
    exact (hheight y.1).2.trans (by
      simpa only [D', div_mul_eq_mul_div, mul_div_assoc, ρ] using
        mul_le_mul_of_nonneg_left hρ hD.le)
  have hnorm' : ‖b0 J y‖ ≤ D' * r * Real.exp β + B * M := by
    apply (hnorm t ht y).trans
    refine add_le_add ?_ le_rfl
    calc
      supportHeight I y.1 * ‖W J y‖ ≤ D' * r * ‖W J y‖ :=
        mul_le_mul_of_nonneg_right hheight' (norm_nonneg _)
      _ ≤ D' * r * Real.exp β :=
        mul_le_mul_of_nonneg_left hW (mul_nonneg hD'.le hr)
  have hb : ‖b0 J y‖ ≤ r * g / 2 := by nlinarith only [hnorm', hfirst, hsecond]
  exact ⟨ha, potentialMetricFiberDefect_lower_of_half_radial_bound H J y
    (hpos (WithLp.toLp 2 y.1)) ha hb⟩

/-- The logarithmic fiber estimate uses the literal Hessian of the fixed
chosen affine potential path, uniformly in independent `t` and `s`. -/
theorem ToricInput.coefficientPath_potentialPath_logarithmic_fiber_end_estimate
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
        let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)
        F * β ≤ Real.sqrt (metricRadialSq H y.1) →
        ‖W (I.alongCoefficientPath t) y‖ ≤ Real.exp β →
          0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
            metricRadialSq H y.1 / 2 ≤
              potentialMetricFiberDefect H (I.alongCoefficientPath t) y := by
  obtain ⟨F, hF, β₀, hβ₀, hbound⟩ := I.coefficientPath_metric_logarithmic_fiber_end_estimate
    (lt_min zero_lt_one hc) (zero_lt_one.trans_le (le_max_left (1 : ℝ) C))
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ t ht s hs y
  obtain ⟨hsymm, hl, hu⟩ := potentialPathHessianEquiv_bounds hφ hc hlower hupper s hs
    (WithLp.toLp 2 y.1)
  exact hbound β hβ t ht y _ hsymm hl hu

section HomogeneousEnd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Hessian radial square equals twice the potential on its
open homogeneous end. The identity is derived from agreement and Euler's
theorem; it is not part of a margin hypothesis. -/
theorem inner_hessian_self_eq_two_mul_on_homogeneous_end
    {φ φEnd : E → ℝ} (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    {R : ℝ} (hR : 0 < R) (hend : ∀ x, R ≤ ‖x‖ → φ x = φEnd x)
    {x : E} (hx : R < ‖x‖) :
    inner ℝ ((fderiv ℝ (gradient φ) x) x) x = 2 * φ x := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx; linarith
  have he : φ =ᶠ[𝓝 x] φEnd := by
    filter_upwards [continuous_const.continuousAt.eventually_lt
      continuous_norm.continuousAt hx] with y hy
    exact hend y hy.le
  have hg : gradient φ =ᶠ[𝓝 x] gradient φEnd := he.gradient
  have hEuler : fderiv ℝ (gradient φ) x x = gradient φ x := by
    rw [hg.fderiv_eq, hg.eq_of_nhds]
    exact fderiv_self_of_homogeneous_one
      ((contDiffAt_gradient (hEnds x hx0)).differentiableAt (by simp))
      (fun r hr => gradient_smul_of_homogeneous_two
        (hEnd1.differentiable (by simp)) hhom hr x)
  rw [hEuler]
  have hgrad : inner ℝ (gradient φ x) x = fderiv ℝ φ x x := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L x) (toDual_gradient (f := φ) (x := x))
  rw [hgrad, he.fderiv_eq, hend x hx.le]
  exact fderiv_self_of_homogeneous_two
    ((hEnd1.differentiable (by simp)) x) (fun r hr => hhom r hr x)

end HomogeneousEnd

/-- Every member of the retained affine path has the same homogeneous end
region and the literal radius `sqrt (2 φ_s)`. -/
theorem metricRadialSq_potentialPath_eq_two_mul
    {φ φEnd : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    {R : ℝ} (hR : 0 < R) (hend : ∀ x, R ≤ ‖x‖ → φ x = φEnd x)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (u : RealSpace n)
    (hu : R < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖) :
    metricRadialSq (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 u)) u =
      2 * potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 u) := by
  have hq : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2) :=
    (contDiff_id.norm_sq ℝ).div_const 2
  have hqhom : ∀ r : ℝ, 0 < r → ∀ x : EuclideanSpace ℝ (Fin n),
      ‖r • x‖ ^ 2 / 2 = r ^ 2 * (‖x‖ ^ 2 / 2) := by
    intro r hr x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    ring
  apply inner_hessian_self_eq_two_mul_on_homogeneous_end
    (show ContDiff ℝ 1 (potentialPath (fun z => ‖z‖ ^ 2 / 2) φEnd s) from
      (contDiff_const.mul (hq.of_le (by simp))).add (contDiff_const.mul hEnd1))
    (fun x hx => (contDiffAt_const.mul hq.contDiffAt).add
      (contDiffAt_const.mul (hEnds x hx)))
    (potentialPath_homogeneous_two hqhom hhom s) hR
    (fun x hx => potentialPath_eq_of_eq_right (hend x hx) s) hu

/-- The source's literal logarithmic potential level is a common full-fiber
end level for the retained chosen interpolation. It lies above any supplied
ambient level and forces entry into the same homogeneous end before the
inverse-Hessian estimate is applied. No independent potential is chosen. -/
theorem ToricInput.coefficientPath_potentialPath_logarithmic_potential_level
    (I : ToricInput n) {φ φEnd : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    {R : ℝ} (hR : 0 < R) (hend : ∀ x, R ≤ ‖x‖ → φ x = φEnd x)
    (Aamb : ℝ) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      Aamb ≤ F ^ 2 * β ^ 2 / 2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
        F ^ 2 * β ^ 2 / 2 ≤
          potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 y.1) →
        ‖W (I.alongCoefficientPath t) y‖ ≤ Real.exp β →
        let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)
        R < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ ∧
          0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
          potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 y.1) ≤
            potentialMetricFiberDefect H (I.alongCoefficientPath t) y := by
  obtain ⟨F, hF, β₁, hβ₁, hbound⟩ :=
    I.coefficientPath_potentialPath_logarithmic_fiber_end_estimate hφ hc hlower hupper
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  let B := max (R ^ 2 / 2) D
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ ≤ R → potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s x ≤ B := by
    intro s hs x hx
    have hq : ‖x‖ ^ 2 / 2 ≤ B :=
      (show ‖x‖ ^ 2 / 2 ≤ R ^ 2 / 2 by nlinarith [norm_nonneg x]).trans (le_max_left _ _)
    have hφx : φ x ≤ B := (Real.le_norm_self _).trans
      ((hD x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)).trans (le_max_right _ _))
    have hq' := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hs.2)
    have hφ' := mul_le_mul_of_nonneg_left hφx hs.1
    dsimp [potentialPath]
    nlinarith only [hq', hφ']
  let β₀ := max β₁ (max (Real.sqrt (2 * max Aamb 0) / F)
    ((Real.sqrt (2 * max B 0) + 1) / F)) + 1
  have hβ₀ : 0 < β₀ := hβ₁.trans_le ((le_max_left _ _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ
  have hβmax : max β₁ (max (Real.sqrt (2 * max Aamb 0) / F)
      ((Real.sqrt (2 * max B 0) + 1) / F)) ≤ β :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hβ
  have hβ₁β : β₁ ≤ β := (le_max_left _ _).trans hβmax
  have hβpos : 0 < β := hβ₁.trans_le hβ₁β
  have hFβ : 0 < F * β := mul_pos hF hβpos
  have hAbound : Real.sqrt (2 * max Aamb 0) ≤ F * β := by
    have h := (div_le_iff₀ hF).mp
      ((le_max_left _ _).trans ((le_max_right _ _).trans hβmax))
    simpa only [mul_comm] using h
  have hBbound : Real.sqrt (2 * max B 0) + 1 ≤ F * β := by
    have h := (div_le_iff₀ hF).mp
      ((le_max_right _ _).trans ((le_max_right _ _).trans hβmax))
    simpa only [mul_comm] using h
  have hlevel : Aamb ≤ F ^ 2 * β ^ 2 / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * max Aamb 0 by positivity)
    have hsq := sq_le_sq₀ (Real.sqrt_nonneg _) hFβ.le |>.mpr hAbound
    nlinarith [le_max_left Aamb 0]
  have hBout : B < F ^ 2 * β ^ 2 / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * max B 0 by positivity)
    have hsq := sq_le_sq₀ (show 0 ≤ Real.sqrt (2 * max B 0) + 1 by positivity)
      hFβ.le |>.mpr hBbound
    nlinarith [Real.sqrt_nonneg (2 * max B 0), le_max_left B 0]
  refine ⟨hlevel, ?_⟩
  intro t ht s hs y hy hW
  have hyend : R < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra h
    have hψ := hinner s hs (WithLp.toLp 2 y.1) (le_of_not_gt h)
    linarith
  have hrad := metricRadialSq_potentialPath_eq_two_mul hφ hEnd1 hEnds hhom hc hlower
    hR hend s hs y.1 hyend
  have hr : F * β ≤ Real.sqrt (metricRadialSq
      (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)) y.1) := by
    rw [hrad]
    have hψ : 0 ≤ 2 * potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 y.1) := by
      nlinarith [sq_nonneg F, sq_nonneg β]
    have hsqrt := Real.sq_sqrt hψ
    nlinarith [Real.sqrt_nonneg
      (2 * potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 y.1))]
  obtain ⟨ha, hdef⟩ := hbound β hβ₁β t ht s hs y hr hW
  rw [hrad] at hdef
  exact ⟨hyend, ha, by simpa using hdef⟩

end FsFltz
