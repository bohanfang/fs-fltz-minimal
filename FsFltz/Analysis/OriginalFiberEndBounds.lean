import FsFltz.Analysis.OriginalAmbientMargin

/-!
# Original full-fiber end estimates

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 770–810,
and `geoemtric-part-fsf.tex`, `eq:fiberbound`, lines 277–289. These estimates
are for the literal quadratic potential and finite toric input. They are
local analytic producers for G2 and `prop:allinitial`; no full-fiber
completion marking is asserted.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- The native deficit identity bounds the radial derivative by the base
value plus a maximum-monomial error. All constants come from the input. -/
theorem ToricInput.exists_norm_b0_bound_by_W (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n,
      ‖b0 I y‖ ≤ supportHeight I y.1 * ‖W I y‖ + C * maxMonomialMagnitude I y := by
  obtain ⟨C, hC, hdef⟩ := I.exists_b0_sub_supportHeight_mul_W_bound
  obtain ⟨m, hm, _, _, hheight⟩ := I.exists_supportHeight_linear_bounds
  refine ⟨C, hC, ?_⟩
  intro y
  have hh : 0 ≤ supportHeight I y.1 :=
    (mul_nonneg hm.le (Real.sqrt_nonneg _)).trans (hheight y.1).1
  calc
    ‖b0 I y‖ = ‖(b0 I y - (supportHeight I y.1 : ℂ) * W I y) +
        (supportHeight I y.1 : ℂ) * W I y‖ := by congr 1; ring
    _ ≤ ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ +
        ‖(supportHeight I y.1 : ℂ) * W I y‖ := norm_add_le _ _
    _ ≤ C * maxMonomialMagnitude I y + supportHeight I y.1 * ‖W I y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
      exact add_le_add (hdef y) le_rfl
    _ = supportHeight I y.1 * ‖W I y‖ + C * maxMonomialMagnitude I y := add_comm _ _

/-- A half-radius bound on the actual scalar yields a strict fiber-end
margin as soon as the Euclidean radius is positive. -/
theorem fiberDefect_lower_of_half_radial_bound (I : ToricInput n) (y : LGSpace n)
    (ha : 0 < a I y)
    (hb : ‖b0 I y‖ ≤ Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) / 2) :
    realSquaredNorm y.1 / 2 ≤
      realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y := by
  have hr := Real.sqrt_nonneg (realSquaredNorm y.1)
  have hg := Real.sqrt_nonneg (a I y)
  have hr2 := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
  have hg2 := Real.sq_sqrt ha.le
  have hsq : Complex.normSq (b0 I y) ≤ realSquaredNorm y.1 * a I y / 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have hprod : 0 ≤ Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) :=
      mul_nonneg hr hg
    nlinarith [norm_nonneg (b0 I y), sq_nonneg
      (Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y) / 2 - ‖b0 I y‖)]
  have hdiv : Complex.normSq (b0 I y) / a I y ≤ realSquaredNorm y.1 / 4 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hsq]
  nlinarith [realSquaredNorm_nonneg y.1]

/-- The whole bounded-value fiber end has the source's strict Cauchy defect.
All height, error and exponential-growth constants are derived from the
input; the sole independent premise is the native dominant-gradient bound.
The statement permits every real base radius and ambient level, including
the cases where the bounded-value region is empty. -/
theorem ToricInput.exists_fiberEndBound_of_gradient_lowerBound (I : ToricInput n)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hgrad : ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
      c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y))
    (Aamb R : ℝ) : ∃ Afib : ℝ, FiberEndBound I Aamb R Afib := by
  obtain ⟨C, hC, hnorm⟩ := I.exists_norm_b0_bound_by_W
  obtain ⟨_, _, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨A, hA, d, hd, hgrowth⟩ := I.maxMonomialMagnitude_exponential_lowerBound
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  let S := max L (max (4 * C / c) (4 * H * B / (c * A * d))) + 1
  have hS : 0 < S := hL.trans_le ((le_max_left L _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨max Aamb (S ^ 2 / 2), le_max_left _ _, ?_⟩
  intro y hy hW
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a I y)
  let M := maxMonomialMagnitude I y
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = realSquaredNorm y.1 := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
  have hrad : S ≤ r := by
    have hphi := (le_max_right Aamb (S ^ 2 / 2)).trans hy
    change S ^ 2 / 2 ≤ realSquaredNorm y.1 / 2 at hphi
    nlinarith
  have hmaxrad : max L (max (4 * C / c) (4 * H * B / (c * A * d))) ≤ r :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hrad
  have hLrad : L ≤ r := (le_max_left L _).trans hmaxrad
  have hCrad : 4 * C / c ≤ r :=
    (le_max_left _ _).trans ((le_max_right L _).trans hmaxrad)
  have hMrad : 4 * H * B / (c * A * d) ≤ r :=
    (le_max_right _ _).trans ((le_max_right L _).trans hmaxrad)
  have hMpos : 0 < M := I.maxMonomialMagnitude_pos y
  have hgrad' : c * M ≤ g := hgrad y hLrad
  have ha : 0 < a I y := Real.sqrt_pos.mp ((mul_pos hc hMpos).trans_le hgrad')
  have hMlin : A * d * r ≤ M := by
    have he : d * r ≤ Real.exp (d * r) := by
      linarith [Real.add_one_le_exp (d * r)]
    calc
      A * d * r = A * (d * r) := mul_assoc _ _ _
      _ ≤ A * Real.exp (d * r) := mul_le_mul_of_nonneg_left he hA.le
      _ ≤ M := hgrowth y
  have hMlarge : 4 * H * B ≤ c * M := by
    have hbound := (div_le_iff₀ (mul_pos (mul_pos hc hA) hd)).mp hMrad
    have hlin := mul_le_mul_of_nonneg_left hMlin hc.le
    nlinarith only [hbound, hlin]
  have hfirst : 4 * (H * r * B) ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_left (hMlarge.trans hgrad') hr
    nlinarith only [hm]
  have hsecond : 4 * C * M ≤ r * g := by
    have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hCrad) hMpos.le
    have hgg := mul_le_mul_of_nonneg_left hgrad' hr
    nlinarith only [hm, hgg]
  have hnorm' : ‖b0 I y‖ ≤ H * r * B + C * M := by
    apply (hnorm y).trans
    refine add_le_add ?_ le_rfl
    calc
      supportHeight I y.1 * ‖W I y‖ ≤ H * r * ‖W I y‖ :=
        mul_le_mul_of_nonneg_right (hheight y.1).2 (norm_nonneg _)
      _ ≤ H * r * B := mul_le_mul_of_nonneg_left (hW.trans (le_max_left _ _))
        (mul_nonneg hH.le hr)
  have hb : ‖b0 I y‖ ≤ r * g / 2 := by nlinarith only [hnorm', hfirst, hsecond]
  have hdef := fiberDefect_lower_of_half_radial_bound I y ha hb
  have hrpos : 0 < r := hS.trans_le hrad
  have hnormpos : 0 < realSquaredNorm y.1 := by nlinarith
  exact ⟨ha, (half_pos hnormpos).trans_le hdef⟩

/-- The prescribed fiber end bound exists for every finite toric input and
every base radius. The ambient level is arbitrary, so this applies to every
valid choice of ambient end bound without changing the target's quantifiers.
In rank one the end is empty by `fiberEnd_empty_rank_one`; this theorem
asserts no positive derivative on a nonempty zero-dimensional fiber end. -/
theorem ToricInput.exists_original_fiberEndBound (I : ToricInput n) (Aamb R : ℝ) :
    ∃ Afib : ℝ, FiberEndBound I Aamb R Afib := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.G_dominant_lowerBound
  exact I.exists_fiberEndBound_of_gradient_lowerBound hc hL hgrad Aamb R

end FsFltz
