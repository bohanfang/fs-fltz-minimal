import FsFltz.Analysis.TailoringDifferentialBridge
import FsFltz.Analysis.SupportHeightBounds

/-!
# Radial localization of the actual tailoring family

Source: `geometric-part-fsf-proof.tex`, `eq:C1` and its consequences,
lines 1107–1114. The radial coordinate here is literally
`sqrt (realSquaredNorm u)`, the based Euclidean length. The support statement
uses the prescribed small-monomial cutoff. The fiber lower bound consumes
the proved C¹ estimate through its quotient C⁰ consequence.
-/

noncomputable section

namespace FsFltz

open Set
open scoped BigOperators

variable {n : ℕ}

theorem norm_tailoringOriginal_le_card_mul_max (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    ‖tailoringOriginal I β y‖ ≤ I.vertices.card * Real.exp (supportHeight I y.1 - β) := by
  calc
    ‖tailoringOriginal I β y‖ ≤ ∑ v ∈ I.vertices,
        ‖monomial (Real.exp (-β) : ℂ) v y‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ I.vertices, Real.exp (supportHeight I y.1 - β) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_tailoring_monomial I β ⟨v, hv⟩ y, tailoringWeight_vertex I β ⟨v, hv⟩]
      exact Real.exp_le_exp.mpr (sub_le_sub_right (I.pairing_le_supportHeight y.1 ⟨v, hv⟩) β)
    _ = _ := by simp

/-- The literal source lower bound on the maximum monomial, uniformly on
every level-one fiber and throughout the closed parameter interval. -/
theorem tailoringFamily_exists_uniform_fiber_max_lower_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β s : ℝ), s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 →
        1 / (I.vertices.card + C * Real.exp (-Real.sqrt β)) ≤
          Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨C, hC, herror⟩ := tailoringFamily_exists_uniform_C0_bound I
  refine ⟨C, hC, fun β s hs y hy => ?_⟩
  have htri : ‖tailoringFamily I β s y‖ ≤ ‖tailoringOriginal I β y‖ +
      ‖tailoringFamily I β s y - tailoringOriginal I β y‖ := by
    have hadd : tailoringOriginal I β y +
        (tailoringFamily I β s y - tailoringOriginal I β y) = tailoringFamily I β s y := by ring
    have h := norm_add_le (tailoringOriginal I β y)
      (tailoringFamily I β s y - tailoringOriginal I β y)
    rwa [hadd] at h
  rw [hy, norm_one] at htri
  have hbound := herror β s hs y
  rw [hy] at hbound
  have horig := norm_tailoringOriginal_le_card_mul_max I β y
  apply (div_le_iff₀ (show 0 < (I.vertices.card : ℝ) + C * Real.exp (-Real.sqrt β) by
    positivity)).mpr
  nlinarith

/-- A growing closed Euclidean ball on which the actual homotopy is
literally unchanged. No restriction on the homotopy parameter is needed. -/
theorem tailoringFamily_exists_growing_unchanged_ball (I : ToricInput n) :
    ∃ d : ℝ, 0 < d ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ s : ℝ, ∀ y : LGSpace n,
        Real.sqrt (realSquaredNorm y.1) ≤ d * β →
          tailoringEta I β y = 0 ∧ tailoringFamily I β s y = tailoringOriginal I β y := by
  obtain ⟨_c, _hc, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  have hN : 0 < (I.vertices.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let d : ℝ := 1 / (2 * H)
  let β₀ : ℝ := max 1 (-2 * Real.log (tailoringSmallConstant I / I.vertices.card))
  have hd : 0 < d := by dsimp [d]; positivity
  have hHd : H * d = 1 / 2 := by dsimp [d]; field_simp
  refine ⟨d, hd, β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ s y hy
  have hβlog : -2 * Real.log (tailoringSmallConstant I / I.vertices.card) ≤ β :=
    (le_max_right _ _).trans hβ
  have hh : supportHeight I y.1 ≤ β / 2 := by
    have hrad := mul_le_mul_of_nonneg_left hy hH.le
    rw [← mul_assoc, hHd] at hrad
    linarith [(hheight y.1).2]
  have hexp : Real.exp (supportHeight I y.1 - β) ≤
      tailoringSmallConstant I / I.vertices.card := by
    rw [← Real.exp_log (div_pos (tailoringSmallConstant_pos I) hN)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hS : tailoringMonomialSize I β y ≤ tailoringSmallConstant I :=
    (tailoringMonomialSize_le_card_mul_max I β y).trans (by
      convert mul_le_mul_of_nonneg_left hexp hN.le using 1
      field_simp)
  have hη := (tailoringEta_eq_zero_iff I β y).mpr hS
  refine ⟨hη, ?_⟩
  simp [tailoringFamily, hη]

/-- A linear Euclidean radial lower bound on the entire level-one fiber,
derived from the uniform error estimate rather than from chosen markings. -/
theorem tailoringFamily_exists_growing_fiber_radius (I : ToricInput n) :
    ∃ d : ℝ, 0 < d ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
        tailoringFamily I β s y = 1 → d * β ≤ Real.sqrt (realSquaredNorm y.1) := by
  obtain ⟨C, hC, hmax⟩ := tailoringFamily_exists_uniform_fiber_max_lower_bound I
  obtain ⟨_c, _hc, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  let d : ℝ := 1 / (2 * H)
  let β₀ : ℝ := max 1 (-2 * Real.log (1 / ((I.vertices.card : ℝ) + C)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hHd : H * d = 1 / 2 := by dsimp [d]; field_simp
  refine ⟨d, hd, β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ s hs y hy
  have heps : Real.exp (-Real.sqrt β) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  have hdenom : (I.vertices.card : ℝ) + C * Real.exp (-Real.sqrt β) ≤
      I.vertices.card + C := by nlinarith
  have hcoarse : 1 / ((I.vertices.card : ℝ) + C) ≤
      Real.exp (supportHeight I y.1 - β) :=
    (one_div_le_one_div_of_le (by positivity) hdenom).trans
        (hmax β s hs y hy)
  have hlog := (Real.log_le_iff_le_exp (show 0 < 1 / ((I.vertices.card : ℝ) + C) by
    positivity)).mpr hcoarse
  have hβlog : -2 * Real.log (1 / ((I.vertices.card : ℝ) + C)) ≤ β :=
    (le_max_right _ _).trans hβ
  have hrad : β / 2 ≤ H * Real.sqrt (realSquaredNorm y.1) := by
    linarith [(hheight y.1).2]
  apply (mul_le_mul_iff_right₀ hH).mp
  rw [← mul_assoc, hHd]
  linarith

/-- Uniformly in the homotopy parameter, every point of the full marked
fiber eventually lies beyond any prescribed fixed Euclidean radius. -/
theorem tailoringFamily_exists_fiber_outside_radius (I : ToricInput n) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 →
        R ≤ Real.sqrt (realSquaredNorm y.1) := by
  obtain ⟨d, hd, B, hB, hb⟩ := tailoringFamily_exists_growing_fiber_radius I
  refine ⟨max B (R / d), lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro β hβ s hs y hy
  have hR : R ≤ d * β := by
    have := (le_max_right B (R / d)).trans hβ
    exact (div_le_iff₀ hd).mp this |>.trans_eq (mul_comm β d)
  exact hR.trans (hb β ((le_max_left _ _).trans hβ) s hs y hy)

/-- For any chosen global extension that agrees with its homogeneous end
outside a fixed Euclidean ball, that equality holds on every full level-one
fiber for sufficiently large `β`. The end-agreement premise is exactly the
conclusion supplied by the compatible-potential extension theorem. -/
theorem tailoringFamily_exists_fiber_in_homogeneous_end (I : ToricInput n)
    {φ φEnd : RealSpace n → ℝ} {R : ℝ}
    (hEnd : ∀ u : RealSpace n,
      R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 → φ y.1 = φEnd y.1 := by
  obtain ⟨β₀, hβ₀, hb⟩ := tailoringFamily_exists_fiber_outside_radius I R
  refine ⟨β₀, hβ₀, fun β hβ s hs y hy => hEnd y.1 ?_⟩
  have he : Real.sqrt (realSquaredNorm y.1) =
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [realSquaredNorm, Real.norm_eq_abs]
  exact he ▸ hb β hβ s hs y hy

end FsFltz
