import FsFltz.Analysis.TailoringTransitionLimits

/-!
# Active faces of normalized tailored limits

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1401–1409.
The limiting retained coefficients are supported on the actual active
polar facets and still sum to one. Subsequences and conormal separation
are separate consumers of these limit calculations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology BigOperators

variable {n : ℕ}

theorem pairing_normalized_tendsto (a : Lattice n) (β : ℕ → ℝ)
    (u : ℕ → RealSpace n) (x : RealSpace n)
    (hx : Tendsto (fun j => (β j)⁻¹ • u j) atTop (𝓝 x)) :
    Tendsto (fun j => pairing a ((β j)⁻¹ • u j)) atTop (𝓝 (pairing a x)) := by
  simpa only [Function.comp_def, pairingCLM_apply] using
    (pairingCLM a).continuous.tendsto x |>.comp hx

/-- Bounded augmented weights force every normalized radial limit into
the prescribed polar halfspaces. -/
theorem pairing_limit_le_one_of_bounded_tailoringMaxWeight
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (u : ℕ → RealSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (u j) ≤ B)
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • u j) atTop (𝓝 x)) :
    pairing a x ≤ 1 := by
  have hp := pairing_normalized_tendsto a β u x hx
  have hinv := tendsto_inv_atTop_zero.comp hβ
  have hh : Tendsto (fun j => pairing a ((β j)⁻¹ • u j) - B * (β j)⁻¹)
      atTop (𝓝 (pairing a x)) := by
    simpa using hp.sub ((tendsto_const_nhds (x := B)).mul hinv)
  apply le_of_tendsto hh
  filter_upwards [hB, hβ.eventually (eventually_gt_atTop 0)] with j hj hpos
  have hw := (tailoringWeight_le_max I (β j) a (Finset.mem_insert_of_mem ha) (u j)).trans hj
  rw [tailoringWeight_vertex I (β j) ⟨a, ha⟩] at hw
  rw [pairing_smul_real]
  have hb := mul_le_mul_of_nonneg_left hw (inv_pos.mpr hpos).le
  have he : (β j)⁻¹ * β j = 1 := inv_mul_cancel₀ hpos.ne'
  nlinarith

/-- A vertex strictly below the limiting polar face has vanishing actual
retained coefficient, independently of its changing cutoff. -/
theorem tailoringRetainedMonomial_tendsto_zero_of_pairing_limit_lt_one
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (ha_lt : pairing a x < 1) :
    Tendsto (fun j => tailoringRetainedMonomial I (β j) a (y j)) atTop (𝓝 0) := by
  let d := (1 - pairing a x) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hgap : pairing a x < 1 - d := by dsimp [d]; linarith
  have hevent := (pairing_normalized_tendsto a β (fun j => (y j).1) x hx).eventually_lt_const hgap
  have hexp : Tendsto (fun j => Real.exp (-d * β j)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hβ.const_mul_atTop_of_neg (neg_neg_of_pos hd))
  apply squeeze_zero_norm' _ hexp
  filter_upwards [hevent, hβ.eventually (eventually_gt_atTop 0)] with j hj hp
  have hweight : tailoringWeight (β j) a (y j).1 ≤ -d * β j := by
    rw [tailoringWeight_vertex I (β j) ⟨a, ha⟩]
    rw [pairing_smul_real] at hj
    have hmul := mul_le_mul_of_nonneg_left hj.le hp.le
    have hcancel : β j * ((β j)⁻¹ * pairing a (y j).1) = pairing a (y j).1 := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    rw [hcancel] at hmul
    nlinarith
  calc
    ‖tailoringRetainedMonomial I (β j) a (y j)‖ ≤
        ‖monomial (Real.exp (-β j) : ℂ) a (y j)‖ := by
      rw [tailoringRetainedMonomial, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (tailoringCutoff_nonneg I (β j) a (y j).1)]
      exact mul_le_of_le_one_left (norm_nonneg _) (tailoringCutoff_le_one I (β j) a (y j).1)
    _ = Real.exp (tailoringWeight (β j) a (y j).1) :=
      norm_tailoring_monomial I (β j) ⟨a, ha⟩ (y j)
    _ ≤ _ := Real.exp_le_exp.mpr hweight

/-- Nonzero limiting coefficients occur only at the active polar facets. -/
theorem pairing_eq_one_of_retained_limit_ne_zero
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (q : ℂ) (hq : Tendsto (fun j => tailoringRetainedMonomial I (β j) a (y j)) atTop (𝓝 q))
    (hqne : q ≠ 0) : pairing a x = 1 := by
  have hle := pairing_limit_le_one_of_bounded_tailoringMaxWeight I a ha β
    (fun j => (y j).1) hβ B hB x hx
  apply hle.eq_or_lt.resolve_right
  intro hlt
  exact hqne (tendsto_nhds_unique hq
    (tailoringRetainedMonomial_tendsto_zero_of_pairing_limit_lt_one I a ha β y hβ x hx hlt))

/-- The literal endpoint equation survives passage to finite coefficient
limits when the constant term is uncut. -/
theorem sum_retained_limits_eq_one
    (I : ToricInput n) (β : ℕ → ℝ) (y : ℕ → LGSpace n)
    (hy : ∀ᶠ j in atTop, tailoringFamily I (β j) 1 (y j) = 1)
    (hzero : ∀ᶠ j in atTop, tailoringCutoff I (β j) 0 (y j).1 = 1)
    (q : Lattice n → ℂ)
    (hq : ∀ a ∈ I.vertices, Tendsto (fun j => tailoringRetainedMonomial I (β j) a (y j))
      atTop (𝓝 (q a))) : ∑ a ∈ I.vertices, q a = 1 := by
  have hsum := tendsto_finsetSum I.vertices hq
  have he : (fun j => ∑ a ∈ I.vertices, tailoringRetainedMonomial I (β j) a (y j))
      =ᶠ[atTop] (fun _ => (1 : ℂ)) := by
    filter_upwards [hy, hzero] with j hj hz
    rw [sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I (β j) (y j) hj, hz,
      Complex.ofReal_one]
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' he.symm)

end FsFltz
