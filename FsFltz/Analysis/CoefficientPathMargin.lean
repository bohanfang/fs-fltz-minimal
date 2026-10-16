import FsFltz.Analysis.CoefficientPathEstimates
import FsFltz.Analysis.OriginalFiberEndBounds

/-!
# Uniform quadratic margins and logarithmic truncations along the coefficient path

Source: `geometric-part-fsf-proof.tex`, `lem:margin`, lines 746–768,
`lem:originalends`, lines 770–795, and matching truncations, lines 1011–1049.
All coefficients follow the actual prescribed path. The potential in this
module is the original quadratic potential, so the scalar is the native `QW`.
The common constants are constructed from the preceding compact-path producers.
For nonidentity Hessians, the inverse-Hessian scalar and metric Cauchy identity
still require their own bridge; no assertion about such scalars is made here.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- One quantitative quadratic ambient margin holds on a common radial end
for every coefficient-path member. The conclusion uses the actual `a` and
`QW`; it assumes neither positivity nor a separately supplied end estimate. -/
theorem ToricInput.coefficientPath_QW_quantitative_ambient_margin (I : ToricInput n) :
    ∃ q : ℝ, 0 < q ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
        0 < a (I.alongCoefficientPath t) y ∧
          q * Real.sqrt (realSquaredNorm y.1) *
            maxMonomialMagnitude (I.alongCoefficientPath t) y ^ 2 ≤
              QW (I.alongCoefficientPath t) y := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.coefficientPath_G_dominant_lowerBound
  obtain ⟨C, hC, hdef⟩ := I.coefficientPath_b0_sub_supportHeight_mul_W_bound
  obtain ⟨m, hm, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  let S := max L (max (1 / (2 * m)) (2 * C / c)) + 1
  have hS : 0 < S := hL.trans_le ((le_max_left L _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨c ^ 2 / (4 * H), div_pos (sq_pos_of_pos hc) (by positivity), S, hS, ?_⟩
  intro t ht y hy
  have hmaxrad : max L (max (1 / (2 * m)) (2 * C / c)) ≤
      Real.sqrt (realSquaredNorm y.1) :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hy
  have hLrad : L ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_left L _).trans hmaxrad
  have hmrad : 1 / (2 * m) ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_left _ _).trans ((le_max_right L _).trans hmaxrad)
  have hCrad : 2 * C / c ≤ Real.sqrt (realSquaredNorm y.1) :=
    (le_max_right _ _).trans ((le_max_right L _).trans hmaxrad)
  have hh : 1 / 2 ≤ supportHeight (I.alongCoefficientPath t) y.1 := by
    rw [supportHeight_alongCoefficientPath]
    have hmr := (div_le_iff₀ (show 0 < 2 * m by positivity)).mp hmrad
    nlinarith [(hheight y.1).1]
  have hgrad' := hgrad t ht y hLrad
  have ha : 0 < a (I.alongCoefficientPath t) y := Real.sqrt_pos.mp
    ((mul_pos hc ((I.alongCoefficientPath t).maxMonomialMagnitude_pos y)).trans_le hgrad')
  refine ⟨ha, QW_quantitative_lower_of_gradient_height_bounds
    (I.alongCoefficientPath t) y hC.le hc hH hh (hheight y.1).2 hgrad' ?_ (hdef t ht y)⟩
  simpa only [mul_comm] using (div_le_iff₀ hc).mp hCrad

/-- The same positive potential level is an ambient end bound for every
member of the actual coefficient path with the quadratic potential. -/
theorem ToricInput.coefficientPath_exists_common_ambientEndBound (I : ToricInput n) :
    ∃ Aamb : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, AmbientEndBound (I.alongCoefficientPath t) Aamb := by
  obtain ⟨q, hq, L, hL, hmargin⟩ := I.coefficientPath_QW_quantitative_ambient_margin
  refine ⟨L ^ 2 / 2, ?_⟩
  intro t ht
  refine ⟨div_pos (sq_pos_of_pos hL) (by norm_num), ?_⟩
  intro y hy
  have hrad : L ≤ Real.sqrt (realSquaredNorm y.1) := by
    have hs := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
    have hr := Real.sqrt_nonneg (realSquaredNorm y.1)
    change L ^ 2 / 2 ≤ realSquaredNorm y.1 / 2 at hy
    nlinarith
  obtain ⟨ha, hQ⟩ := hmargin t ht y hrad
  exact ⟨ha, (mul_pos (mul_pos hq (hL.trans_le hrad))
    (sq_pos_of_pos ((I.alongCoefficientPath t).maxMonomialMagnitude_pos y))).trans_le hQ⟩

/-- The radial derivative bound used for common full-fiber truncations.
The coefficient error is uniform and the support height is unchanged. -/
theorem ToricInput.coefficientPath_norm_b0_bound_by_W (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      ‖b0 (I.alongCoefficientPath t) y‖ ≤
        supportHeight I y.1 * ‖W (I.alongCoefficientPath t) y‖ +
          C * maxMonomialMagnitude (I.alongCoefficientPath t) y := by
  obtain ⟨C, hC, hdef⟩ := I.coefficientPath_b0_sub_supportHeight_mul_W_bound
  obtain ⟨m, hm, _, _, hheight⟩ := I.exists_supportHeight_linear_bounds
  refine ⟨C, hC, ?_⟩
  intro t ht y
  have hh : 0 ≤ supportHeight I y.1 :=
    (mul_nonneg hm.le (Real.sqrt_nonneg _)).trans (hheight y.1).1
  calc
    ‖b0 (I.alongCoefficientPath t) y‖ =
        ‖(b0 (I.alongCoefficientPath t) y - (supportHeight I y.1 : ℂ) *
          W (I.alongCoefficientPath t) y) +
            (supportHeight I y.1 : ℂ) * W (I.alongCoefficientPath t) y‖ := by congr 1; ring
    _ ≤ ‖b0 (I.alongCoefficientPath t) y - (supportHeight I y.1 : ℂ) *
        W (I.alongCoefficientPath t) y‖ +
          ‖(supportHeight I y.1 : ℂ) * W (I.alongCoefficientPath t) y‖ := norm_add_le _ _
    _ ≤ C * maxMonomialMagnitude (I.alongCoefficientPath t) y +
        supportHeight I y.1 * ‖W (I.alongCoefficientPath t) y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
      exact add_le_add (hdef t ht y) le_rfl
    _ = _ := add_comm _ _

/-- A fixed radius multiplier gives uniform full-fiber end estimates at
`r ≥ Cfib β` and base radius `exp β`. This is the literal logarithmic
truncation scale in the source's matching-truncation paragraph. Rank one is
included; there the bounded-value region is necessarily empty on this end. -/
theorem ToricInput.coefficientPath_logarithmic_fiber_end_estimate (I : ToricInput n) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
        Cfib * β ≤ Real.sqrt (realSquaredNorm y.1) →
        ‖W (I.alongCoefficientPath t) y‖ ≤ Real.exp β →
          0 < a (I.alongCoefficientPath t) y ∧
            realSquaredNorm y.1 / 2 ≤ realSquaredNorm y.1 -
              Complex.normSq (b0 (I.alongCoefficientPath t) y) /
                a (I.alongCoefficientPath t) y := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.coefficientPath_G_dominant_lowerBound
  obtain ⟨C, hC, hnorm⟩ := I.coefficientPath_norm_b0_bound_by_W
  obtain ⟨_, _, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨A, hA, d, hd, hgrowth⟩ :=
    I.coefficientPath_maxMonomialMagnitude_exponential_lowerBound
  let F : ℝ := 2 / d
  have hF : 0 < F := div_pos (by norm_num) hd
  let k : ℝ := 4 * H / (c * A)
  have hk : 0 < k := div_pos (by positivity) (mul_pos hc hA)
  let β₀ := max 1 (max (L / F) (max (4 * C / (c * F)) (Real.log k))) + 1
  have hβ₀ : 0 < β₀ := by
    dsimp [β₀]
    exact add_pos_of_pos_of_nonneg (zero_lt_one.trans_le (le_max_left _ _)) zero_le_one
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ t ht y hy hW
  let J := I.alongCoefficientPath t
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a J y)
  let M := maxMonomialMagnitude J y
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hMpos : 0 < M := J.maxMonomialMagnitude_pos y
  have hβmax : max 1 (max (L / F) (max (4 * C / (c * F)) (Real.log k))) ≤ β :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hβ
  have hLβ : L / F ≤ β :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hβmax)
  have hCβ : 4 * C / (c * F) ≤ β :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβmax))
  have hkβ : Real.log k ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβmax))
  have hLrad : L ≤ r := by
    have hLF := (div_le_iff₀ hF).mp hLβ
    dsimp [r]
    nlinarith only [hLF, hy]
  have hCrad : 4 * C ≤ c * r := by
    have hCF := (div_le_iff₀ (mul_pos hc hF)).mp hCβ
    have hm := mul_le_mul_of_nonneg_left hy hc.le
    nlinarith only [hCF, hm]
  have hgrad' : c * M ≤ g := hgrad t ht y hLrad
  have ha : 0 < a J y := Real.sqrt_pos.mp ((mul_pos hc hMpos).trans_le hgrad')
  have htwobeta : 2 * β ≤ d * r := by
    have hm := mul_le_mul_of_nonneg_left hy hd.le
    have hFd : d * F = 2 := by dsimp [F]; field_simp
    change d * (F * β) ≤ d * r at hm
    rw [← mul_assoc, hFd] at hm
    exact hm
  have hMlarge : 4 * H * Real.exp β ≤ c * M := by
    have he := Real.exp_le_exp.mpr (show β + Real.log k ≤ d * r by linarith)
    rw [Real.exp_add, Real.exp_log hk] at he
    have hgrowth' : A * Real.exp (d * r) ≤ M := hgrowth t ht y
    have hscaled := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left he hA.le).trans hgrowth') hc.le
    have heq : c * (A * (Real.exp β * k)) = 4 * H * Real.exp β := by
      dsimp [k]
      field_simp
    rw [heq] at hscaled
    exact hscaled
  have hfirst : 4 * (H * r * Real.exp β) ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_left (hMlarge.trans hgrad') hr
    nlinarith only [hm]
  have hsecond : 4 * C * M ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_right hCrad hMpos.le
    have hgg := mul_le_mul_of_nonneg_left hgrad' hr
    nlinarith only [hm, hgg]
  have hnorm' : ‖b0 J y‖ ≤ H * r * Real.exp β + C * M := by
    apply (hnorm t ht y).trans
    refine add_le_add ?_ le_rfl
    calc
      supportHeight I y.1 * ‖W J y‖ ≤ H * r * ‖W J y‖ :=
        mul_le_mul_of_nonneg_right (hheight y.1).2 (norm_nonneg _)
      _ ≤ H * r * Real.exp β :=
        mul_le_mul_of_nonneg_left hW (mul_nonneg hH.le hr)
  have hb : ‖b0 J y‖ ≤ r * g / 2 := by nlinarith only [hnorm', hfirst, hsecond]
  exact ⟨ha, fiberDefect_lower_of_half_radial_bound J y ha hb⟩

/-- The logarithmic estimate produces one literal fiber end level
`Cfib² β² / 2`, above any supplied ambient level, for the entire compact
coefficient path. This is a producer of bounds used to choose common
truncations, not an assumed marking or compact pair. -/
theorem ToricInput.coefficientPath_exists_logarithmic_fiberEndBound
    (I : ToricInput n) (Aamb : ℝ) :
    ∃ Cfib : ℝ, 0 < Cfib ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        FiberEndBound (I.alongCoefficientPath t) Aamb (Real.exp β)
          (Cfib ^ 2 * β ^ 2 / 2) := by
  obtain ⟨F, hF, β₁, hβ₁, hbound⟩ := I.coefficientPath_logarithmic_fiber_end_estimate
  let T := max β₁ (Real.sqrt (2 * max Aamb 0) / F) + 1
  have hT : 0 < T := hβ₁.trans_le ((le_max_left _ _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨F, hF, T, hT, ?_⟩
  intro β hβ t ht
  have hβmax : max β₁ (Real.sqrt (2 * max Aamb 0) / F) ≤ β :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hβ
  have hβ₁β : β₁ ≤ β := (le_max_left _ _).trans hβmax
  have hβpos : 0 < β := hβ₁.trans_le hβ₁β
  have hFβ : 0 < F * β := mul_pos hF hβpos
  have hAbound : Real.sqrt (2 * max Aamb 0) ≤ F * β := by
    have h := (div_le_iff₀ hF).mp ((le_max_right _ _).trans hβmax)
    simpa only [mul_comm] using h
  have hlevel : Aamb ≤ F ^ 2 * β ^ 2 / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * max Aamb 0 by positivity)
    have hsq := sq_le_sq₀ (Real.sqrt_nonneg _) hFβ.le |>.mpr hAbound
    nlinarith [le_max_left Aamb 0]
  refine ⟨hlevel, ?_⟩
  intro y hy hW
  have hr : F * β ≤ Real.sqrt (realSquaredNorm y.1) := by
    have hs := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
    have hnonneg := Real.sqrt_nonneg (realSquaredNorm y.1)
    change F ^ 2 * β ^ 2 / 2 ≤ realSquaredNorm y.1 / 2 at hy
    nlinarith
  obtain ⟨ha, hdef⟩ := hbound β hβ₁β t ht y hr hW
  have hnormpos : 0 < realSquaredNorm y.1 :=
    Real.sqrt_pos.mp (hFβ.trans_le hr)
  exact ⟨ha, (half_pos hnormpos).trans_le hdef⟩

end FsFltz
