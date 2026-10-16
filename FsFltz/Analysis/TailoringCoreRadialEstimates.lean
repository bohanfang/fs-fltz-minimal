import FsFltz.Analysis.TailoringFamily
import FsFltz.Analysis.SupportHeightBounds

/-!
# The real radial equation and its quantitative derivative

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1597–1618.
The function below uses the actual all-pairs cutoffs. Its radial positivity
will be derived from the cutoff estimates, rather than assumed.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

/-- The real equation `Rβ` in the proof of the compact radial section. -/
def tailoringRadialFunction (I : ToricInput n) (β : ℝ) (u : RealSpace n) : ℝ :=
  1 - tailoringCutoff I β 0 u +
    ∑ v ∈ I.vertices, tailoringCutoff I β v u * Real.exp (pairing v u - β)

theorem contDiff_tailoringRadialFunction (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (tailoringRadialFunction I β) := by
  apply (contDiff_const.sub (tailoringCutoff_contDiff I β 0)).add
  apply ContDiff.sum
  intro v _
  apply (tailoringCutoff_contDiff I β v).mul
  unfold pairing
  fun_prop

theorem tailoringRadialFunction_nonneg (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    0 ≤ tailoringRadialFunction I β u := by
  exact add_nonneg (sub_nonneg.mpr (tailoringCutoff_le_one I β 0 u))
    (Finset.sum_nonneg fun v _ => mul_nonneg (tailoringCutoff_nonneg I β v u)
      (Real.exp_pos _).le)

theorem tailoringRadialFunction_le_of_height_le (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (hh : supportHeight I u ≤ β) :
    tailoringRadialFunction I β u ≤ I.vertices.card * Real.exp (supportHeight I u - β) := by
  have hc : tailoringCutoff I β 0 u = 1 := by
    apply tailoringCutoff_eq_one_of_maximal
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    rw [tailoringWeight_zero, tailoringWeight_vertex I β ⟨a, ha⟩]
    linarith [I.pairing_le_supportHeight u ⟨a, ha⟩]
  unfold tailoringRadialFunction
  rw [hc, sub_self, zero_add]
  calc
    _ ≤ ∑ _v ∈ I.vertices, Real.exp (supportHeight I u - β) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (mul_le_of_le_one_left (Real.exp_pos _).le
        (tailoringCutoff_le_one I β v u)).trans
        (Real.exp_le_exp.mpr (sub_le_sub_right (I.pairing_le_supportHeight u ⟨v, hv⟩) β))
    _ = _ := by simp

theorem tailoringRadialFunction_max_term_lower (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (hh : β - Real.sqrt β ≤ supportHeight I u) :
    Real.exp (supportHeight I u - β) ≤ tailoringRadialFunction I β u := by
  obtain ⟨v, hv⟩ := I.supportHeight_attained u
  have hc : tailoringCutoff I β v.val u = 1 := by
    apply tailoringCutoff_eq_one_of_gap
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [tailoringWeight_zero, tailoringWeight_vertex I β v, hv]
      linarith
    · rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_vertex I β v, hv]
      linarith [I.pairing_le_supportHeight u ⟨a, ha⟩, Real.sqrt_nonneg β]
  have hs := Finset.single_le_sum
    (f := fun a => tailoringCutoff I β a u * Real.exp (pairing a u - β))
    (fun a _ => mul_nonneg (tailoringCutoff_nonneg I β a u) (Real.exp_pos _).le) v.property
  rw [hc, one_mul, hv] at hs
  exact hs.trans (le_add_of_nonneg_left
    (sub_nonneg.mpr (tailoringCutoff_le_one I β 0 u)))

/-- Exact decomposition into positive exponential slopes and cutoff error. -/
theorem fderiv_tailoringRadialFunction_self (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) :
    fderiv ℝ (tailoringRadialFunction I β) u u =
      (∑ v ∈ I.vertices, tailoringCutoff I β v u *
        Real.exp (pairing v u - β) * pairing v u) +
      (-(fderiv ℝ (tailoringCutoff I β 0) u u) +
        ∑ v ∈ I.vertices, (fderiv ℝ (tailoringCutoff I β v) u u) *
          Real.exp (pairing v u - β)) := by
  have hd (v : Lattice n) : HasFDerivAt (fun x : RealSpace n =>
      Real.exp (pairing v x - β)) (Real.exp (pairing v u - β) • pairingCLM v) u := by
    exact (Real.hasDerivAt_exp _).comp_hasFDerivAt u
      (by simpa only [pairingCLM_apply] using (pairingCLM v).hasFDerivAt.sub_const β)
  have he := (((tailoringCutoff_contDiff I β 0).differentiable (by simp) u).hasFDerivAt.const_sub 1).add
    (HasFDerivAt.fun_sum (u := I.vertices) fun v _ =>
      ((tailoringCutoff_contDiff I β v).differentiable (by simp) u).hasFDerivAt.mul (hd v))
  rw [show fderiv ℝ (tailoringRadialFunction I β) u = _ from he.fderiv]
  simp only [add_apply, sum_apply, smul_apply, neg_apply, smul_eq_mul, pairingCLM_apply]
  rw [Finset.sum_add_distrib]
  have he₁ : (∑ v ∈ I.vertices, tailoringCutoff I β v u *
      (Real.exp (pairing v u - β) * pairing v u)) =
      ∑ v ∈ I.vertices, tailoringCutoff I β v u * Real.exp (pairing v u - β) * pairing v u := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  have he₂ : (∑ v ∈ I.vertices, Real.exp (pairing v u - β) *
      fderiv ℝ (tailoringCutoff I β v) u u) =
      ∑ v ∈ I.vertices, fderiv ℝ (tailoringCutoff I β v) u u * Real.exp (pairing v u - β) := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he₁, he₂]
  ring

theorem tailoringRadialFunction_slope_lower (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (hh : β - Real.sqrt β ≤ supportHeight I u)
    (hs : 0 ≤ supportHeight I u - Real.sqrt β - 2) :
    supportHeight I u * Real.exp (supportHeight I u - β) ≤
      ∑ v ∈ I.vertices, tailoringCutoff I β v u *
        Real.exp (pairing v u - β) * pairing v u := by
  have hn (v : Lattice n) (hv : v ∈ I.vertices) :
      0 ≤ tailoringCutoff I β v u * Real.exp (pairing v u - β) * pairing v u := by
    by_cases hc : tailoringCutoff I β v u = 0
    · simp [hc]
    have hret : 0 < tailoringCutoff I β v u :=
      lt_of_le_of_ne (tailoringCutoff_nonneg I β v u) (Ne.symm hc)
    have hg := tailoringCutoff_retained_gap I β v u hret
      (I.supportHeight_attained u).choose.val
      (Finset.mem_insert_of_mem (I.supportHeight_attained u).choose.property)
    rw [tailoringWeight_vertex I β ⟨v, hv⟩,
      tailoringWeight_vertex I β (I.supportHeight_attained u).choose,
      (I.supportHeight_attained u).choose_spec] at hg
    exact mul_nonneg (mul_nonneg hret.le (Real.exp_pos _).le) (by linarith)
  obtain ⟨v, hv⟩ := I.supportHeight_attained u
  have hc : tailoringCutoff I β v.val u = 1 := by
    apply tailoringCutoff_eq_one_of_gap
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [tailoringWeight_zero, tailoringWeight_vertex I β v, hv]
      linarith
    · rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_vertex I β v, hv]
      linarith [I.pairing_le_supportHeight u ⟨a, ha⟩, Real.sqrt_nonneg β]
  simpa only [hc, one_mul, hv, mul_comm] using Finset.single_le_sum hn v.property

/-- The total cutoff derivative error is exponentially small at every radius. -/
theorem tailoringRadialFunction_exists_cutoff_error_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (u : RealSpace n),
      |-(fderiv ℝ (tailoringCutoff I β 0) u u) +
        ∑ v ∈ I.vertices, (fderiv ℝ (tailoringCutoff I β v) u u) *
          Real.exp (pairing v u - β)| ≤
      C * ‖u‖ * Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I u - β)) := by
  obtain ⟨D, hD, hb⟩ := tailoringCutoffs_exists_uniform_bound_iteratedFDeriv I 1
  have hd (β : ℝ) (a : Lattice n) (ha : a ∈ tailoringExponents I) (u : RealSpace n) :
      |fderiv ℝ (tailoringCutoff I β a) u u| ≤ D * ‖u‖ := by
    exact ((fderiv ℝ (tailoringCutoff I β a) u).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [norm_iteratedFDeriv_one] using hb β a ha u) (norm_nonneg u))
  refine ⟨(I.vertices.card + 1) * D, mul_nonneg (by positivity) hD, ?_⟩
  intro β u
  let E := Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I u - β))
  have hE : 0 ≤ E := mul_nonneg (Real.exp_pos _).le (le_max_of_le_left zero_le_one)
  have ht (v : Lattice n) (hv : v ∈ I.vertices) :
      |(fderiv ℝ (tailoringCutoff I β v) u u) * Real.exp (pairing v u - β)| ≤
      D * ‖u‖ * E := by
    by_cases hz : fderiv ℝ (tailoringCutoff I β v) u = 0
    · simp only [hz, zero_apply, zero_mul, abs_zero]
      positivity
    have he := tailoringCutoff_changed_exp_bound I β v u (Or.inr hz)
    rw [tailoringWeight_vertex I β ⟨v, hv⟩] at he
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hd β v (Finset.mem_insert_of_mem hv) u) he (Real.exp_pos _).le
      (mul_nonneg hD (norm_nonneg u))
  have ht₀ : |fderiv ℝ (tailoringCutoff I β 0) u u| ≤ D * ‖u‖ * E := by
    by_cases hz : fderiv ℝ (tailoringCutoff I β 0) u = 0
    · simp only [hz, zero_apply, abs_zero]
      positivity
    have he := tailoringCutoff_changed_exp_bound I β 0 u (Or.inr hz)
    simp only [tailoringWeight_zero, Real.exp_zero] at he
    exact (hd β 0 (Finset.mem_insert_self _ _) u).trans
      (le_mul_of_one_le_right (mul_nonneg hD (norm_nonneg u)) he)
  calc
    _ ≤ |fderiv ℝ (tailoringCutoff I β 0) u u| +
        ∑ v ∈ I.vertices, |(fderiv ℝ (tailoringCutoff I β v) u u) *
          Real.exp (pairing v u - β)| := by
      exact (abs_add_le _ _).trans (add_le_add (by simp) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ D * ‖u‖ * E + ∑ _v ∈ I.vertices, D * ‖u‖ * E :=
      add_le_add ht₀ (Finset.sum_le_sum ht)
    _ = _ := by simp [E]; ring

private theorem native_norm_le_radius (u : RealSpace n) :
    ‖u‖ ≤ Real.sqrt (realSquaredNorm u) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  rw [Real.norm_eq_abs]
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
  simpa only [sq_abs] using Finset.single_le_sum (fun k _ => sq_nonneg (u k))
    (Finset.mem_univ j)

/-- The radial derivative is positive on the whole unbounded region
`h ≥ β − L`, for one threshold independent of the radius and direction. -/
theorem tailoringRadialFunction_eventually_radial_positive (I : ToricInput n)
    {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ β in atTop, ∀ u : RealSpace n, β - L ≤ supportHeight I u →
      0 < fderiv ℝ (tailoringRadialFunction I β) u u := by
  obtain ⟨c, hc, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨C, hC, herror⟩ := tailoringRadialFunction_exists_cutoff_error_bound I
  let D := C * Real.exp L / c
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he : Tendsto (fun β : ℝ => D * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (2 * (L + 3)),
    eventually_ge_atTop (L ^ 2), he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with β hβ hβL hβsq heβ
  intro u hu
  have hsqrt : Real.sqrt β ≤ β / 2 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ β / 2)).mpr
    nlinarith
  have hLs : L ≤ Real.sqrt β := (Real.le_sqrt hL (by linarith)).mpr hβsq
  have hh : 0 < supportHeight I u := by linarith
  have hgap : β - Real.sqrt β ≤ supportHeight I u := by linarith
  have hs : 0 ≤ supportHeight I u - Real.sqrt β - 2 := by linarith
  have hnorm : ‖u‖ ≤ supportHeight I u / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      ‖u‖ * c ≤ Real.sqrt (realSquaredNorm u) * c :=
        mul_le_mul_of_nonneg_right (native_norm_le_radius u) hc.le
      _ ≤ supportHeight I u := by simpa only [mul_comm] using (hheight u).1
  let M := Real.exp (supportHeight I u - β)
  have hM : 0 < M := Real.exp_pos _
  have hmax : max 1 M ≤ Real.exp L * M := by
    apply max_le
    · rw [show Real.exp L * M = Real.exp (L + supportHeight I u - β) by
        dsimp [M]; rw [← Real.exp_add]; congr 1; ring]
      exact Real.one_le_exp_iff.mpr (by linarith)
    · exact le_mul_of_one_le_left hM.le (Real.one_le_exp_iff.mpr hL)
  have hbound := herror β u
  have hbound' : |-(fderiv ℝ (tailoringCutoff I β 0) u u) +
      ∑ v ∈ I.vertices, (fderiv ℝ (tailoringCutoff I β v) u u) *
        Real.exp (pairing v u - β)| < supportHeight I u * M := by
    calc
      _ ≤ C * ‖u‖ * Real.exp (-Real.sqrt β) * max 1 M := hbound
      _ ≤ C * (supportHeight I u / c) * Real.exp (-Real.sqrt β) * (Real.exp L * M) := by
        gcongr
      _ = (D * Real.exp (-Real.sqrt β)) * (supportHeight I u * M) := by dsimp [D]; ring
      _ < 1 * (supportHeight I u * M) :=
        mul_lt_mul_of_pos_right heβ (mul_pos hh hM)
      _ = _ := one_mul _
  rw [fderiv_tailoringRadialFunction_self]
  have hmain := tailoringRadialFunction_slope_lower I β u hgap hs
  have hneg := (abs_lt.mp hbound').1
  dsimp only [M] at hneg
  linarith

end FsFltz
