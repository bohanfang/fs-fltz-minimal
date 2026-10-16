import FsFltz.Analysis.TailoringNormalizedMargin

/-!
# Radial control on the whole tailored bounded-value end

Source: `geometric-part-fsf-proof.tex`, `eq:almosttangent`, lines 1198–1207.
The radial numerator is that of the normalized holomorphic polynomial;
the bounded-value hypothesis concerns the actual nonholomorphic family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open scoped BigOperators
variable {n : ℕ}

/-- The normalized radial discrepancy retains the original uniform constant. -/
theorem tailoringNormalizedInput_exists_radial_bound (I : ToricInput n) :
    ∃ B : ℝ, 0 < B ∧ ∀ β : ℝ, ∀ y : LGSpace n,
      ‖b0 (tailoringNormalizedInput I β) y‖ ≤
        supportHeight I y.1 * ‖tailoringOriginal I β y‖ +
          B * Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨B, hB, hb⟩ := I.coefficientPath_norm_b0_bound_by_W
  refine ⟨B, hB, fun β y => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hb 1 (by simp) y) (Real.exp_pos (-β)).le
  rw [maxMonomialMagnitude_coefficientOne] at h
  rw [b0_tailoringNormalizedInput, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hw : ‖tailoringOriginal I β y‖ =
      Real.exp (-β) * ‖W (I.alongCoefficientPath 1) y‖ := by
    rw [← W_tailoringNormalizedInput, W_tailoringNormalizedInput_scale, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hw]
  have he : Real.exp (supportHeight I y.1 - β) =
      Real.exp (-β) * Real.exp (supportHeight I y.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith only [h]

/-- Actual C¹ closeness bounds the normalized holomorphic value on every
bounded-value fiber of the nonholomorphic tailoring family. -/
theorem tailoringFamily_exists_original_value_bound (I : ToricInput n) :
    ∃ E : ℝ, 0 < E ∧ ∀ β s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, ‖tailoringFamily I β s y‖ ≤ 2 →
      ‖tailoringOriginal I β y‖ ≤
        2 + E * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨E, hE, he⟩ := tailoringFamily_exists_uniform_C1_bound I
  refine ⟨E, hE, fun β s hs y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Geometry.lgCover_surjective n y
  have hdiff := (le_add_of_nonneg_right (norm_nonneg _)).trans (he β s hs x)
  have htri := norm_le_norm_add_norm_sub (tailoringFamily I β s (Geometry.lgCover x))
    (tailoringOriginal I β (Geometry.lgCover x))
  exact htri.trans (add_le_add hy hdiff)

/-- The almost-tangency bound holds on the entire bounded-value end of the
literal tailored family. The metric is arbitrary within the fixed bounds,
so in particular it applies to the actual chosen potential Hessian. -/
theorem tailoringFamily_exists_uniform_metric_almostTangent
    (I : ToricInput n) {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ L : ℝ, 0 < L ∧ ∀ β s : ℝ,
      s ∈ Set.Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      L ≤ Real.sqrt (realSquaredNorm y.1) → ‖tailoringFamily I β s y‖ ≤ 2 →
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        (∀ v, inner ℝ (H v) v ≤ U * ‖v‖ ^ 2) →
        let r := Real.sqrt (metricRadialSq H y.1)
        let a := toricInverseMetricSq H (tailoringNormalizedInput I β) y
        0 < a ∧ ‖b0 (tailoringNormalizedInput I β) y‖ / (r * Real.sqrt a) ≤
          C * ((Real.exp (supportHeight I y.1 - β))⁻¹ +
            Real.exp (-Real.sqrt β) + r⁻¹) := by
  obtain ⟨d, hd, L, hL, hgrad⟩ := I.coefficientPath_inverseMetric_dominant_lowerBound hU
  obtain ⟨B, hB, hb⟩ := tailoringNormalizedInput_exists_radial_bound I
  obtain ⟨E, hE, he⟩ := tailoringFamily_exists_original_value_bound I
  obtain ⟨_, _, D, hD, hheight⟩ := I.exists_supportHeight_linear_bounds
  let k := Real.sqrt c
  have hk : 0 < k := Real.sqrt_pos.mpr hc
  let A := D / k
  have hA : 0 < A := div_pos hD hk
  let C := 2 * A / d + A * E / d + B / d + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, L, hL, ?_⟩
  intro β s hs y hy hfs H hsymm hlower hupper
  let r := Real.sqrt (metricRadialSq H y.1)
  let M := Real.exp (supportHeight I y.1 - β)
  let g := Real.sqrt (toricInverseMetricSq H (tailoringNormalizedInput I β) y)
  let ε := Real.exp (-Real.sqrt β)
  have hM : 0 < M := Real.exp_pos _
  have hε : 0 < ε := Real.exp_pos _
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v := fun v =>
    (mul_nonneg hc.le (sq_nonneg _)).trans (hlower v)
  have hrad := (metricRadialSq_radius_bounds H hc hU hlower hupper y.1).1
  have hr : 0 < r := (mul_pos hk (hL.trans_le hy)).trans_le hrad
  have hh : supportHeight I y.1 ≤ A * r := by
    have hρ : Real.sqrt (realSquaredNorm y.1) ≤ r / k :=
      (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hrad)
    exact (hheight y.1).2.trans (by
      simpa only [A, div_mul_eq_mul_div, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hρ hD.le)
  have hg : d * M ≤ g := by
    have h := hgrad 1 (by simp) y hy H hsymm hpos hupper
    rw [maxMonomialMagnitude_coefficientOne] at h
    have hgscale : g = Real.exp (-β) *
        Real.sqrt (toricInverseMetricSq H (I.alongCoefficientPath 1) y) := by
      dsimp [g]
      rw [toricInverseMetricSq_tailoringNormalizedInput,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
    rw [hgscale]
    have heM : M = Real.exp (-β) * Real.exp (supportHeight I y.1) := by
      dsimp [M]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heM]
    nlinarith only [mul_le_mul_of_nonneg_left h (Real.exp_pos (-β)).le]
  have hgpos : 0 < g := (mul_pos hd hM).trans_le hg
  have hn : ‖b0 (tailoringNormalizedInput I β) y‖ ≤
      A * r * (2 + E * ε * M) + B * M := by
    apply (hb β y).trans
    apply add_le_add _ le_rfl
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (he β s hs y hfs) (mul_pos hA hr).le)
  let T := 2 * A / d * M⁻¹ + A * E / d * ε + B / d * r⁻¹
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have heq : A * r * (2 + E * ε * M) + B * M = r * (d * M) * T := by
    dsimp [T]
    field_simp
  have hratio : ‖b0 (tailoringNormalizedInput I β) y‖ / (r * g) ≤ T := by
    apply (div_le_iff₀ (mul_pos hr hgpos)).mpr
    calc
      _ ≤ r * (d * M) * T := hn.trans_eq heq
      _ ≤ r * g * T := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg hr.le) hT
      _ = T * (r * g) := mul_comm _ _
  refine ⟨Real.sqrt_pos.mp hgpos, hratio.trans ?_⟩
  have hAd : 0 ≤ 2 * A / d := by positivity
  have hEd : 0 ≤ A * E / d := by positivity
  have hBd : 0 ≤ B / d := by positivity
  have h1 : 2 * A / d ≤ C := by dsimp [C]; linarith
  have h2 : A * E / d ≤ C := by dsimp [C]; linarith
  have h3 : B / d ≤ C := by dsimp [C]; linarith
  have h1' := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hM.le)
  have h2' := mul_le_mul_of_nonneg_right h2 hε.le
  have h3' := mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hr.le)
  dsimp [T] at hratio ⊢
  nlinarith only [h1', h2', h3']

end FsFltz
