import FsFltz.Analysis.OriginalAmbientMargin
import FsFltz.Analysis.OriginalFiberEndBounds
import FsFltz.Analysis.DominantFace
import FsFltz.Analysis.LaurentSurjectivity
import FsFltz.Compactness

/-!
# Boundedness of the original literal ratio set

Source: `geometric-part-fsf-proof.tex`, `eq:Kthreshold` and the adjoining
ratio estimate, lines 857–869; `geoemtric-part-fsf.tex`, `sec:initial`,
lines 263–276. The proof combines the actual Cauchy estimate for `b0`,
dominant-gradient control, exponential monomial growth, and the attained
maximum of the original quadratic sublevel. No end bound or comparison
data are assumed.
-/

noncomputable section

namespace FsFltz

variable {n : ℕ}

/-- The source's first literal ratio inequality, before exponential decay
is used: Cauchy and gradient dominance give `r/(c*M*R)`. -/
theorem endRatio_le_radius_div_monomialMagnitude (I : ToricInput n) (y : LGSpace n)
    (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (hgrad : c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y))
    (hy : R ≤ ‖W I y‖) :
    endRatio I y ≤ Real.sqrt (realSquaredNorm y.1) /
      (c * maxMonomialMagnitude I y * R) := by
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a I y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hM := I.maxMonomialMagnitude_pos y
  have hg : 0 < g := (mul_pos hc hM).trans_le hgrad
  have ha : 0 < a I y := Real.sqrt_pos.mp hg
  have hW : 0 < ‖W I y‖ := hR.trans_le hy
  have hgg : c * maxMonomialMagnitude I y * g ≤ a I y := by
    calc
      c * maxMonomialMagnitude I y * g ≤ g * g :=
        mul_le_mul_of_nonneg_right hgrad hg.le
      _ = a I y := Real.mul_self_sqrt (a_nonneg I y)
  change ‖b0 I y‖ / (a I y * ‖W I y‖) ≤ r / (c * maxMonomialMagnitude I y * R)
  apply (div_le_div_iff₀ (mul_pos ha hW) (mul_pos (mul_pos hc hM) hR)).mpr
  calc
    ‖b0 I y‖ * (c * maxMonomialMagnitude I y * R) ≤
        (r * g) * (c * maxMonomialMagnitude I y * R) :=
      mul_le_mul_of_nonneg_right (norm_b0_le_euclidean_radius_mul_sqrt_a I y)
        (mul_pos (mul_pos hc hM) hR).le
    _ = (r * (c * maxMonomialMagnitude I y * g)) * R := by ring
    _ ≤ (r * a I y) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgg hr) hR.le
    _ ≤ (r * a I y) * ‖W I y‖ :=
      mul_le_mul_of_nonneg_left hy (mul_nonneg hr ha.le)
    _ = r * (a I y * ‖W I y‖) := by ring

/-- Pointwise ratio estimate from the literal gradient and growth inequalities.
The elementary `d*r ≤ exp(d*r)` estimate gives a finite uniform bound. -/
theorem endRatio_le_of_gradient_and_growth (I : ToricInput n) (y : LGSpace n)
    (c A d R : ℝ) (hc : 0 < c) (hA : 0 < A) (hd : 0 < d) (hR : 0 < R)
    (hgrad : c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y))
    (hgrowth : A * Real.exp (d * Real.sqrt (realSquaredNorm y.1)) ≤
      maxMonomialMagnitude I y) (hy : R ≤ ‖W I y‖) :
    endRatio I y ≤ 1 / (c * A * d * R) := by
  let r := Real.sqrt (realSquaredNorm y.1)
  have hlinear : A * d * r ≤ maxMonomialMagnitude I y := by
    calc
      A * d * r = A * (d * r) := by ring
      _ ≤ A * Real.exp (d * r) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (d * r)])
          hA.le
      _ ≤ maxMonomialMagnitude I y := hgrowth
  apply (endRatio_le_radius_div_monomialMagnitude I y c R hc hR hgrad hy).trans
  apply (div_le_div_iff₀
    (mul_pos (mul_pos hc (I.maxMonomialMagnitude_pos y)) hR)
    (mul_pos (mul_pos (mul_pos hc hA) hd) hR)).mpr
  calc
    r * (c * A * d * R) = (A * d * r) * (c * R) := by ring
    _ ≤ maxMonomialMagnitude I y * (c * R) :=
      mul_le_mul_of_nonneg_right hlinear (mul_pos hc hR).le
    _ = 1 * (c * maxMonomialMagnitude I y * R) := by ring

private theorem ratioSet_bddAbove_threshold_of_gradient_bound (I : ToricInput n)
    (c L : ℝ) (hc : 0 < c) (hL : 0 < L)
    (hgrad : ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
      c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y)) :
    ∃ A : ℝ, 0 < A ∧ ∀ Aamb : ℝ, A ≤ Aamb → ∀ R : ℝ,
      max 1 (sublevelMagnitudeSup I Aamb) < R → BddAbove (ratioSet I R) := by
  obtain ⟨B, hB, d, hd, hgrowth⟩ := I.maxMonomialMagnitude_exponential_lowerBound
  refine ⟨L ^ 2 / 2 + 1, by positivity, ?_⟩
  intro Aamb hAamb R hR
  have hAambpos : 0 < Aamb := lt_of_lt_of_le (by positivity) hAamb
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  refine ⟨1 / (c * B * d * R), ?_⟩
  rintro q ⟨y, hy, rfl⟩
  have hphi : Aamb < phi0 y := phi0_gt_of_far_value I Aamb R
    (sublevelMaximumAttained I Aamb hAambpos.le)
    ((le_max_right _ _).trans_lt hR) y hy
  have hr : L ≤ Real.sqrt (realSquaredNorm y.1) := by
    have hsqrt := Real.sq_sqrt (realSquaredNorm_nonneg y.1)
    have hsqrtnonneg := Real.sqrt_nonneg (realSquaredNorm y.1)
    change Aamb < realSquaredNorm y.1 / 2 at hphi
    nlinarith
  exact endRatio_le_of_gradient_and_growth I y c B d R hc hB hd hRpos
    (hgrad y hr) (hgrowth y) hy

/-- The literal ratio set is bounded for all radii beyond the actual maximum
of every sufficiently large original quadratic sublevel. All constants are
derived from the finite input, and the ambient level may be enlarged. -/
theorem ToricInput.exists_ratioSet_bddAbove_threshold (I : ToricInput n) :
    ∃ A : ℝ, 0 < A ∧ ∀ Aamb : ℝ, A ≤ Aamb → ∀ R : ℝ,
      max 1 (sublevelMagnitudeSup I Aamb) < R → BddAbove (ratioSet I R) := by
  obtain ⟨c, hc, L, hL, hgrad⟩ := I.G_dominant_lowerBound
  exact ratioSet_bddAbove_threshold_of_gradient_bound I c L hc hL hgrad

/-- Nonemptiness and boundedness of the formula's actual range set are both
proved before using its real supremum. This is the ratio-set producer in
`eq:Kthreshold`, without a geometric end-bound assumption. -/
theorem ToricInput.exists_ratioSet_wellDefined_threshold (I : ToricInput n) :
    ∃ A : ℝ, 0 < A ∧ ∀ Aamb : ℝ, A ≤ Aamb → ∀ R : ℝ,
      max 1 (sublevelMagnitudeSup I Aamb) < R → RatioSetWellDefined I R := by
  obtain ⟨A, hA, hbdd⟩ := I.exists_ratioSet_bddAbove_threshold
  refine ⟨A, hA, ?_⟩
  intro Aamb hAamb R hR
  exact ⟨I.ratioSet_nonempty R, hbdd Aamb hAamb R hR⟩

/-- The analytic bounds at the beginning of G1–G2 are chosen together from
the original finite input, with their literal threshold and quantifier order.
This assertion supplies neither all-`K` completeness nor an initial pair,
its completion markings, admissible rounding, or a comparison chain. -/
theorem ToricInput.exists_initial_analytic_bounds (I : ToricInput n) :
    ∃ Aamb R0 : ℝ, AmbientEndBound I Aamb ∧
      max 1 (sublevelMagnitudeSup I Aamb) < R0 ∧
      ∀ R : ℝ, R0 ≤ R → (ratioSet I R).Nonempty ∧ BddAbove (ratioSet I R) ∧
        ∃ Afib : ℝ, FiberEndBound I Aamb R Afib := by
  obtain ⟨Aorig, hamb⟩ := I.exists_original_ambientEndBound
  obtain ⟨Aratio, _, hratio⟩ := I.exists_ratioSet_wellDefined_threshold
  let Aamb := max Aorig Aratio
  have hamb' : AmbientEndBound I Aamb := by
    refine ⟨hamb.1.trans_le (le_max_left _ _), ?_⟩
    intro y hy
    exact hamb.2 y ((le_max_left _ _).trans hy)
  let R0 := max 1 (sublevelMagnitudeSup I Aamb) + 1
  have hR0 : max 1 (sublevelMagnitudeSup I Aamb) < R0 := by dsimp [R0]; linarith
  refine ⟨Aamb, R0, hamb', hR0, ?_⟩
  intro R hR
  have hs := hratio Aamb (le_max_right _ _) R (hR0.trans_le hR)
  exact ⟨hs.1, hs.2, I.exists_original_fiberEndBound Aamb R⟩

end FsFltz
