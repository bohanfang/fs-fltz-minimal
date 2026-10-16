import FsFltz.Analysis.SupportHeightBounds
import FsFltz.Analysis.DominantFace

/-!
# Quantitative ambient margin for the original quadratic potential

Source: `geometric-part-fsf-proof.tex`, `lem:margin`, lines 746–768.
The scalar estimate is transferred to the native `QW`, `b0`, `a`, support
height, and maximum monomial magnitude. Its immediate geometric consumer is
`lem:originalends`, lines 770–822, in item G1 of the target.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- The scalar algebra in `lem:margin`, retaining its sharp denominator.
The hypotheses are elementary norm bounds on the displayed scalars. -/
theorem quadratic_ambient_margin {r g h C M : ℝ} {b W : ℂ}
    (hh : 1 / 2 ≤ h) (hC : 0 ≤ C) (hM : 0 ≤ M) (hb : ‖b‖ ≤ r * g)
    (hdef : ‖b - (h : ℂ) * W‖ ≤ C * M) :
    r * g * (r * g - C * M) / (2 * h) ≤
      r ^ 2 * g ^ 2 - Complex.normSq b + (conj W * b).re / 2 := by
  have hhpos : 0 < 2 * h := by linarith
  have he : (conj (b - (h : ℂ) * W) * b).re ≤ C * M * ‖b‖ := by
    calc
      (conj (b - (h : ℂ) * W) * b).re ≤
          ‖conj (b - (h : ℂ) * W) * b‖ := Complex.re_le_norm _
      _ = ‖b - (h : ℂ) * W‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ C * M * ‖b‖ := mul_le_mul_of_nonneg_right hdef (norm_nonneg _)
  have heq : (conj (b - (h : ℂ) * W) * b).re =
      Complex.normSq b - h * (conj W * b).re := by
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  rw [heq, Complex.normSq_eq_norm_sq] at he
  have hsquare : ‖b‖ ^ 2 ≤ (r * g) ^ 2 := by
    nlinarith [norm_nonneg b]
  have hfirst : 0 ≤ (2 * h - 1) * ((r * g) ^ 2 - ‖b‖ ^ 2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hsquare)
  have hsecond : 0 ≤ C * M * (r * g - ‖b‖) :=
    mul_nonneg (mul_nonneg hC hM) (sub_nonneg.mpr hb)
  apply (div_le_iff₀ hhpos).mpr
  rw [Complex.normSq_eq_norm_sq]
  nlinarith only [he, hfirst, hsecond]

/-- Cauchy–Schwarz for the actual original logarithmic derivative scalar.
Both vector lengths use the based Euclidean sums in the specification. -/
theorem norm_b0_le_euclidean_radius_mul_sqrt_a (I : ToricInput n) (y : LGSpace n) :
    ‖b0 I y‖ ≤ Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) := by
  calc
    ‖b0 I y‖ ≤ ∑ j, ‖(y.1 j : ℂ) * G I y j‖ := norm_sum_le _ _
    _ = ∑ j, |y.1 j| * ‖G I y j‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j, |y.1 j| ^ 2) * Real.sqrt (∑ j, ‖G I y j‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) := by
      simp only [sq_abs, ← Complex.normSq_eq_norm_sq, realSquaredNorm, a]

/-- The sharp source estimate for the literal `QW` and the native finite
support height, using the proved Cauchy bound rather than assuming it. -/
theorem QW_supportHeight_lower_bound (I : ToricInput n) (y : LGSpace n)
    {C : ℝ} (hC : 0 ≤ C) (hh : 1 / 2 ≤ supportHeight I y.1)
    (hdef : ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
      C * maxMonomialMagnitude I y) :
    Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) *
        (Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) -
          C * maxMonomialMagnitude I y) / (2 * supportHeight I y.1) ≤ QW I y := by
  have h := quadratic_ambient_margin hh hC
    (I.maxMonomialMagnitude_pos y).le (norm_b0_le_euclidean_radius_mul_sqrt_a I y) hdef
  simpa only [Real.sq_sqrt (realSquaredNorm_nonneg y.1), Real.sq_sqrt (a_nonneg I y),
    QW, Complex.star_def] using h

/-- Finite coefficients construct one actual defect constant, hence one
sharp margin estimate valid everywhere the native height is at least `1/2`.
This theorem assumes neither an ambient end bound nor a positivity conclusion. -/
theorem ToricInput.exists_QW_supportHeight_lower_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n, 1 / 2 ≤ supportHeight I y.1 →
      Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) *
        (Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) -
          C * maxMonomialMagnitude I y) / (2 * supportHeight I y.1) ≤ QW I y := by
  obtain ⟨C, hC, hdef⟩ := I.exists_b0_sub_supportHeight_mul_W_bound
  exact ⟨C, hC, fun y hh => QW_supportHeight_lower_bound I y hC.le hh (hdef y)⟩

/-- The source's sharp bound gives a quantitative positive ambient margin
once the native gradient dominates the maximum monomial, the height is at
most linear in the Euclidean radius, and that radius exceeds the defect
threshold. All displayed quantities are the original toric formulas. -/
theorem QW_quantitative_lower_of_gradient_height_bounds (I : ToricInput n)
    (y : LGSpace n) {C c H : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hH : 0 < H)
    (hh : 1 / 2 ≤ supportHeight I y.1)
    (hheight : supportHeight I y.1 ≤ H * Real.sqrt (realSquaredNorm y.1))
    (hgrad : c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y))
    (hradius : 2 * C ≤ c * Real.sqrt (realSquaredNorm y.1))
    (hdef : ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
      C * maxMonomialMagnitude I y) :
    c ^ 2 / (4 * H) * Real.sqrt (realSquaredNorm y.1) *
      maxMonomialMagnitude I y ^ 2 ≤ QW I y := by
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a I y)
  let M := maxMonomialMagnitude I y
  let h := supportHeight I y.1
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hM : 0 < M := I.maxMonomialMagnitude_pos y
  have hq : 0 ≤ c ^ 2 / (4 * H) := div_nonneg (sq_nonneg _) (by positivity)
  have hrg : 0 ≤ r * g := mul_nonneg hr hg
  have hcg : r * (c * M) ≤ r * g := mul_le_mul_of_nonneg_left hgrad hr
  have hdefsmall : C * M ≤ r * g / 2 := by
    have hcM := mul_le_mul_of_nonneg_right hradius hM.le
    nlinarith only [hcM, hcg]
  have hnumer : (r * g) ^ 2 / 2 ≤ r * g * (r * g - C * M) := by
    have hm := mul_le_mul_of_nonneg_left hdefsmall hrg
    nlinarith only [hm]
  have hcgSq : (r * (c * M)) ^ 2 ≤ (r * g) ^ 2 := by
    have hleft : 0 ≤ r * (c * M) := mul_nonneg hr (mul_nonneg hc.le hM.le)
    nlinarith only [hleft, hcg]
  have hden : 0 < 2 * h := by dsimp [h]; linarith
  have hbound : c ^ 2 / (4 * H) * r * M ^ 2 ≤
      r * g * (r * g - C * M) / (2 * h) := by
    apply (le_div_iff₀ hden).mpr
    calc
      c ^ 2 / (4 * H) * r * M ^ 2 * (2 * h) ≤
          c ^ 2 / (4 * H) * r * M ^ 2 * (2 * (H * r)) :=
        mul_le_mul_of_nonneg_left (by dsimp [h, r]; linarith [hheight])
          (mul_nonneg (mul_nonneg hq hr) (sq_nonneg _))
      _ = (r * (c * M)) ^ 2 / 2 := by field_simp; ring
      _ ≤ (r * g) ^ 2 / 2 := div_le_div_of_nonneg_right hcgSq (by norm_num)
      _ ≤ r * g * (r * g - C * M) := hnumer
  exact hbound.trans (QW_supportHeight_lower_bound I y hC hh hdef)

/-- Reduction of `lem:margin` to the native dominant-gradient estimate.
Support-height bounds and the defect constant are constructed from the finite
input. The sole extra analytic premise is the displayed gradient estimate,
whose independent producer is `lem:dominant`. -/
theorem ToricInput.exists_QW_margin_of_gradient_lowerBound (I : ToricInput n)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hgrad : ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
      c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y)) :
    ∃ q : ℝ, 0 < q ∧ ∃ R : ℝ, 0 < R ∧ ∀ y : LGSpace n,
      R ≤ Real.sqrt (realSquaredNorm y.1) →
        0 < a I y ∧ q * Real.sqrt (realSquaredNorm y.1) *
          maxMonomialMagnitude I y ^ 2 ≤ QW I y := by
  obtain ⟨C, hC, hdef⟩ := I.exists_b0_sub_supportHeight_mul_W_bound
  obtain ⟨m, hm, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  let R := max L (max (1 / (2 * m)) (2 * C / c)) + 1
  have hR : 0 < R := hL.trans_le ((le_max_left L _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨c ^ 2 / (4 * H), div_pos (sq_pos_of_pos hc) (by positivity), R, hR, ?_⟩
  intro y hy
  have hmaxrad : max L (max (1 / (2 * m)) (2 * C / c)) ≤
      Real.sqrt (realSquaredNorm y.1) :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hy
  have hLrad : L ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_left L _).trans hmaxrad
  have hmrad : 1 / (2 * m) ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_left _ _).trans ((le_max_right L _).trans hmaxrad)
  have hCrad : 2 * C / c ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_right _ _).trans ((le_max_right L _).trans hmaxrad)
  have hh : 1 / 2 ≤ supportHeight I y.1 := by
    have hmr := (div_le_iff₀ (show 0 < 2 * m by positivity)).mp hmrad
    nlinarith [(hheight y.1).1]
  have hgrad' := hgrad y hLrad
  have ha : 0 < a I y := Real.sqrt_pos.mp
    ((mul_pos hc (I.maxMonomialMagnitude_pos y)).trans_le hgrad')
  refine ⟨ha, QW_quantitative_lower_of_gradient_height_bounds I y hC.le hc hH hh
    (hheight y.1).2 hgrad' ?_ (hdef y)⟩
  simpa only [mul_comm] using (div_le_iff₀ hc).mp hCrad

/-- The quantitative margin constructs the target's explicit ambient end
bound, conditional only on the independent native dominant-gradient estimate.
No conclusion about the Liouville flow or its completion is folded into this
local analytic deduction. -/
theorem ToricInput.exists_ambientEndBound_of_gradient_lowerBound (I : ToricInput n)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hgrad : ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
      c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y)) :
    ∃ Aamb : ℝ, AmbientEndBound I Aamb := by
  obtain ⟨q, hq, R, hR, hmargin⟩ := I.exists_QW_margin_of_gradient_lowerBound hc hL hgrad
  refine ⟨R ^ 2 / 2, div_pos (sq_pos_of_pos hR) (by norm_num), ?_⟩
  intro y hy
  have hrad : R ≤ Real.sqrt (realSquaredNorm y.1) := by
    have hs := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
    have hr := Real.sqrt_nonneg (realSquaredNorm y.1)
    change R ^ 2 / 2 ≤ realSquaredNorm y.1 / 2 at hy
    nlinarith
  obtain ⟨ha, hQ⟩ := hmargin y hrad
  exact ⟨ha, (mul_pos (mul_pos hq (hR.trans_le hrad))
    (sq_pos_of_pos (I.maxMonomialMagnitude_pos y))).trans_le hQ⟩

/-- `lem:margin` for the original quadratic potential, proved from the finite
toric input. The dominant-face producer supplies the independent gradient
estimate; no end bound or ambient-positivity conclusion is assumed. -/
theorem ToricInput.QW_quantitative_ambient_margin (I : ToricInput n) :
    ∃ q : ℝ, 0 < q ∧ ∃ R : ℝ, 0 < R ∧ ∀ y : LGSpace n,
      R ≤ Real.sqrt (realSquaredNorm y.1) →
        0 < a I y ∧ q * Real.sqrt (realSquaredNorm y.1) *
          maxMonomialMagnitude I y ^ 2 ≤ QW I y := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.G_dominant_lowerBound
  exact I.exists_QW_margin_of_gradient_lowerBound hc hL hgrad

/-- The explicit ambient end bound of `sec:initial` exists for every original
finite input, as required by the analytic clause of G1. Flow completeness and
finite Liouville type remain separate geometric obligations. -/
theorem ToricInput.exists_original_ambientEndBound (I : ToricInput n) :
    ∃ Aamb : ℝ, AmbientEndBound I Aamb := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.G_dominant_lowerBound
  exact I.exists_ambientEndBound_of_gradient_lowerBound hc hL hgrad

end FsFltz
