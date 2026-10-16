import FsFltz.Analysis.TailoringCriticalDifferential

/-!
# Limits of actual transition exponents

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1404–1417.
A fixed vertex with a strictly intermediate cutoff has vanishing retained
coefficient, but belongs to the active face of every normalized radial limit.
These are the two distinct conclusions used in the bad-region contradiction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- A transition weight lies in the explicit strip of width `B + 2`. -/
theorem tailoringCutoff_transition_weight_bounds (I : ToricInput n)
    (β : ℝ) (a : Lattice n) (u : RealSpace n) (B : ℝ)
    (hB : tailoringMaxWeight I β u ≤ B)
    (hpos : 0 < tailoringCutoff I β a u)
    (hlt : tailoringCutoff I β a u < 1) :
    -Real.sqrt β - 2 < tailoringWeight β a u ∧
      tailoringWeight β a u < B - Real.sqrt β := by
  have hlo := tailoringCutoff_retained_deficit I β a u hpos
  have hhi := tailoringCutoff_changed_deficit I β a u (Or.inl hlt.ne)
  have hmax : 0 ≤ tailoringMaxWeight I β u := le_max_left _ _
  constructor <;> linarith

/-- The actual retained coefficient of a changed vertex tends to zero
whenever the augmented maximal weight stays bounded. -/
theorem tailoringRetainedMonomial_tendsto_zero_of_transition
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ)
    (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (hchange : ∀ᶠ j in atTop, tailoringCutoff I (β j) a (y j).1 < 1) :
    Tendsto (fun j => tailoringRetainedMonomial I (β j) a (y j)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun j => Real.exp B * Real.exp (-Real.sqrt (β j)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_sqrt_atTop.comp hβ))
  apply squeeze_zero_norm' _ hexp
  filter_upwards [hB, hchange] with j hj hjc
  have hw := tailoringCutoff_changed_deficit I (β j) a (y j).1 (Or.inl hjc.ne)
  calc
    ‖tailoringRetainedMonomial I (β j) a (y j)‖
        ≤ ‖monomial (Real.exp (-β j) : ℂ) a (y j)‖ := by
      rw [tailoringRetainedMonomial, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (tailoringCutoff_nonneg I (β j) a (y j).1)]
      exact mul_le_of_le_one_left (norm_nonneg _) (tailoringCutoff_le_one I (β j) a (y j).1)
    _ = Real.exp (tailoringWeight (β j) a (y j).1) :=
      norm_tailoring_monomial I (β j) ⟨a, ha⟩ (y j)
    _ ≤ Real.exp (B - Real.sqrt (β j)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]

/-- Transition exponents become active at every normalized radial limit,
despite their retained coefficients tending to zero. -/
theorem pairing_limit_eq_one_of_tailoring_transition
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (u : ℕ → RealSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ)
    (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (u j) ≤ B)
    (htransition : ∀ᶠ j in atTop,
      0 < tailoringCutoff I (β j) a (u j) ∧ tailoringCutoff I (β j) a (u j) < 1)
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • u j) atTop (𝓝 x)) :
    pairing a x = 1 := by
  have hinv : Tendsto (fun j => (β j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hβ
  have hsqrt : Tendsto (fun j => Real.sqrt (β j) / β j) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hβ)
  have hlo : Tendsto (fun j => (-Real.sqrt (β j) - 2) / β j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, sub_mul, neg_mul, neg_zero, mul_zero, sub_zero]
      using hsqrt.neg.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
  have hhi : Tendsto (fun j => (B - Real.sqrt (β j)) / β j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, sub_mul, mul_zero, sub_zero]
      using ((tendsto_const_nhds (x := B)).mul hinv).sub hsqrt
  have hweight : Tendsto (fun j => tailoringWeight (β j) a (u j) / β j)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [hB, htransition, hβ.eventually (eventually_gt_atTop 0)] with j hj ht hp
      exact div_le_div_of_nonneg_right
        (tailoringCutoff_transition_weight_bounds I (β j) a (u j) B hj ht.1 ht.2).1.le hp.le
    · filter_upwards [hB, htransition, hβ.eventually (eventually_gt_atTop 0)] with j hj ht hp
      exact div_le_div_of_nonneg_right
        (tailoringCutoff_transition_weight_bounds I (β j) a (u j) B hj ht.1 ht.2).2.le hp.le
  have hp : Tendsto (fun j => pairing a ((β j)⁻¹ • u j)) atTop (𝓝 1) := by
    have hw : Tendsto (fun j => 1 + tailoringWeight (β j) a (u j) / β j)
        atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hweight
    apply hw.congr'
    filter_upwards [hβ.eventually (eventually_gt_atTop 0)] with j hj
    rw [tailoringWeight_vertex I (β j) ⟨a, ha⟩]
    rw [← pairingCLM_apply a ((β j)⁻¹ • u j)]
    rw [map_smul, smul_eq_mul]
    rw [pairingCLM_apply]
    field_simp [hj.ne']
    ring
  have hp' : Tendsto (fun j => pairing a ((β j)⁻¹ • u j)) atTop (𝓝 (pairing a x)) := by
    simpa only [Function.comp_def, pairingCLM_apply] using (pairingCLM a).continuous.tendsto x |>.comp hx
  exact tendsto_nhds_unique hp' hp

end FsFltz
