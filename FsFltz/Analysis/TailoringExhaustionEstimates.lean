import FsFltz.Analysis.TailoringPoissonPositivity

/-!
# Exhaustion numerator errors for the literal tailored family

Source: `geometric-part-fsf-proof.tex`, `eq:C1`, lines 1107–1114,
`eq:rankerror`, lines 1134–1140, and `subsec:finite`, lines 1182–1197.
The numerator uses the actual cover differential, rather than an assumed
error certificate. Its native interpretation is supplied separately.
-/

noncomputable section

namespace FsFltz

open Geometry Set
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {n : ℕ}

/-- The source numerator on a homogeneous potential end, written using
the actual radial and angular evaluations of a complex differential. -/
def coverExhaustionNumerator
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : RealSpace n) (f : ℂ) (L : TangentCoordinates n →L[ℝ] ℂ) : ℝ :=
  metricRadialSq H u * coverPlanePairing H L -
    (conj (L (u, 0) - f / 2) * L (0, u)).im

private theorem norm_im_conj_mul_sub_le (z w z₀ w₀ : ℂ) :
    ‖(conj z * w).im - (conj z₀ * w₀).im‖ ≤
      ‖z - z₀‖ * ‖w‖ + ‖z₀‖ * ‖w - w₀‖ := by
  have he : conj z * w - conj z₀ * w₀ =
      conj (z - z₀) * w + conj z₀ * (w - w₀) := by
    rw [map_sub]
    ring
  calc
    _ = |(conj z * w - conj z₀ * w₀).im| := by
      rw [Complex.sub_im, Real.norm_eq_abs]
    _ ≤ ‖conj z * w - conj z₀ * w₀‖ := Complex.abs_im_le_norm _
    _ ≤ ‖conj (z - z₀) * w‖ + ‖conj z₀ * (w - w₀)‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]

/-- A quantitative perturbation estimate before any tailoring constants
are substituted; it controls both the value and differential errors. -/
theorem norm_coverExhaustionNumerator_sub_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : RealSpace n) (f f₀ : ℂ) (L L₀ : TangentCoordinates n →L[ℝ] ℂ) :
    ‖coverExhaustionNumerator H u f L - coverExhaustionNumerator H u f₀ L₀‖ ≤
      ‖metricRadialSq H u‖ * ‖coverPlanePairing H L - coverPlanePairing H L₀‖ +
      (‖L - L₀‖ * ‖(u, (0 : RealSpace n))‖ + ‖f - f₀‖ / 2) *
        ((‖L - L₀‖ + ‖L₀‖) * ‖((0 : RealSpace n), u)‖) +
      (‖L₀‖ * ‖(u, (0 : RealSpace n))‖ + ‖f₀‖ / 2) *
        (‖L - L₀‖ * ‖((0 : RealSpace n), u)‖) := by
  have hd : ‖(L (u, 0) - f / 2) - (L₀ (u, 0) - f₀ / 2)‖ ≤
      ‖L - L₀‖ * ‖(u, (0 : RealSpace n))‖ + ‖f - f₀‖ / 2 := by
    have he : (L (u, 0) - f / 2) - (L₀ (u, 0) - f₀ / 2) =
        (L - L₀) (u, 0) - (f - f₀) / 2 := by simp; ring
    rw [he]
    exact (norm_sub_le _ _).trans (by
      rw [norm_div, Complex.norm_ofNat]
      gcongr
      exact (L - L₀).le_opNorm _)
  have hz : ‖L₀ (u, 0) - f₀ / 2‖ ≤
      ‖L₀‖ * ‖(u, (0 : RealSpace n))‖ + ‖f₀‖ / 2 := by
    exact (norm_sub_le _ _).trans (by
      rw [norm_div, Complex.norm_ofNat]
      gcongr
      exact L₀.le_opNorm _)
  have hw : ‖L (0, u)‖ ≤ (‖L - L₀‖ + ‖L₀‖) * ‖((0 : RealSpace n), u)‖ := by
    refine (L.le_opNorm _).trans ?_
    gcongr
    exact norm_le_norm_sub_add L L₀
  have hdw : ‖L (0, u) - L₀ (0, u)‖ ≤ ‖L - L₀‖ * ‖((0 : RealSpace n), u)‖ := by
    exact (L - L₀).le_opNorm _
  have he : coverExhaustionNumerator H u f L - coverExhaustionNumerator H u f₀ L₀ =
      metricRadialSq H u * (coverPlanePairing H L - coverPlanePairing H L₀) -
        ((conj (L (u, 0) - f / 2) * L (0, u)).im -
          (conj (L₀ (u, 0) - f₀ / 2) * L₀ (0, u)).im) := by
    dsimp [coverExhaustionNumerator]
    ring
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have hcross := norm_im_conj_mul_sub_le (L (u, 0) - f / 2) (L (0, u))
    (L₀ (u, 0) - f₀ / 2) (L₀ (0, u))
  have h₁ := mul_le_mul hd hw (norm_nonneg _) (by positivity)
  have h₂ := mul_le_mul hz hdw (norm_nonneg _) (by positivity)
  linarith

/-- The second source `rankerror` bound for the actual cover numerator.
Here `metricRadialSq = r²`; the fixed unit-radius restriction allows the
zeroth-order error to be absorbed into the radial scale. -/
theorem tailoringFamily_exists_uniform_coverExhaustionNumerator_error
    (I : ToricInput n) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ β s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ x : TangentCoordinates n,
      1 ≤ ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ →
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
      ‖coverExhaustionNumerator H x.1 (tailoringFamily I β s (lgCover x))
          (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x) -
        coverExhaustionNumerator H x.1 (tailoringOriginal I β (lgCover x))
          (fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x)‖ ≤
        C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 *
          Real.exp (supportHeight I x.1 - β) ^ 2 := by
  obtain ⟨A, hA, hC1⟩ := tailoringFamily_exists_uniform_C1_bound I
  obtain ⟨P, hP, hπ⟩ := tailoringFamily_exists_uniform_coverPlanePairing_error I hc
  let B := 1 + (I.vertices.card : ℝ) + ∑ v ∈ I.vertices, ‖exponentLinearMap v‖
  let E := 1 + ‖logCoverRadialLift n‖ + ‖logCoverAngularLift n‖
  let T := 2 * A * E ^ 2 * (A + 2 * B)
  let C := 1 + P + T / c
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 1 ≤ E := by dsimp [E]; linarith [norm_nonneg (logCoverRadialLift n), norm_nonneg (logCoverAngularLift n)]
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun β s hs x hr H hlower => ?_⟩
  let L := fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x
  let L₀ := fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x
  let f := tailoringFamily I β s (lgCover x)
  let f₀ := tailoringOriginal I β (lgCover x)
  let ε := Real.exp (-Real.sqrt β)
  let M := Real.exp (supportHeight I x.1 - β)
  let r := ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖
  let R := metricRadialSq H x.1
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hε₁ : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hr₀ : 0 ≤ r := norm_nonneg _
  have hRlow : c * r ^ 2 ≤ R := hlower _
  have hR : 0 ≤ R := (mul_nonneg hc.le (sq_nonneg r)).trans hRlow
  have hb₀ := hC1 β s hs x
  have hv : ‖f - f₀‖ ≤ A * ε * M :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb₀
  have hd : ‖L - L₀‖ ≤ A * ε * M := by
    have hdif := fderiv_sub
      ((contDiff_tailoringFamily_cover I β s).differentiable (by simp) x)
      ((contDiff_tailoringOriginal_cover I β).differentiable (by simp) x)
    have hb := (le_add_of_nonneg_left (norm_nonneg _)).trans hb₀
    change ‖fderiv ℝ ((fun z => tailoringFamily I β s (lgCover z)) -
      (fun z => tailoringOriginal I β (lgCover z))) x‖ ≤ _ at hb
    rw [hdif] at hb
    exact hb
  have hdcoarse : ‖L - L₀‖ ≤ A * M := hd.trans (by
    have h := mul_le_mul_of_nonneg_left hε₁ hA.le
    exact mul_le_mul_of_nonneg_right (by simpa using h) hM)
  have hb : ‖L₀‖ ≤ B * M := (norm_fderiv_tailoringOriginal_cover_le I β x).trans (by
    dsimp only [B, M, lgCover]
    gcongr
    linarith [(Nat.cast_nonneg I.vertices.card : (0 : ℝ) ≤ _)])
  have hf₀ : ‖f₀‖ ≤ B * M := (norm_tailoringOriginal_le_card_mul_max I β (lgCover x)).trans (by
    dsimp only [B, M, lgCover]
    gcongr
    have hn : 0 ≤ ∑ v ∈ I.vertices, ‖exponentLinearMap v‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith)
  have hrad : ‖(x.1, (0 : RealSpace n))‖ ≤ E * r := by
    have h := (logCoverRadialLift n).le_opNorm (WithLp.toLp 2 x.1)
    exact h.trans (by dsimp only [E, r]; gcongr; linarith [norm_nonneg (logCoverAngularLift n)])
  have hang : ‖((0 : RealSpace n), x.1)‖ ≤ E * r := by
    have h := (logCoverAngularLift n).le_opNorm (WithLp.toLp 2 x.1)
    exact h.trans (by dsimp only [E, r]; gcongr; linarith [norm_nonneg (logCoverRadialLift n)])
  have hEr : 1 ≤ E * r := by nlinarith only [hE, hr, mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hr)]
  have hz : ‖L - L₀‖ * ‖(x.1, (0 : RealSpace n))‖ + ‖f - f₀‖ / 2 ≤
      2 * A * E * ε * M * r := by
    calc
      _ ≤ (A * ε * M) * (E * r) + (A * ε * M) / 2 := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ A * ε * M by positivity) (sub_nonneg.mpr hEr), show 0 ≤ A * ε * M by positivity]
  have hw : (‖L - L₀‖ + ‖L₀‖) * ‖((0 : RealSpace n), x.1)‖ ≤
      (A + B) * E * M * r := by
    calc
      _ ≤ (A * M + B * M) * (E * r) := by gcongr
      _ = _ := by ring
  have hz₀ : ‖L₀‖ * ‖(x.1, (0 : RealSpace n))‖ + ‖f₀‖ / 2 ≤
      2 * B * E * M * r := by
    calc
      _ ≤ (B * M) * (E * r) + (B * M) / 2 := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hB.le hM) (sub_nonneg.mpr hEr), mul_nonneg hB.le hM]
  have hdw : ‖L - L₀‖ * ‖((0 : RealSpace n), x.1)‖ ≤ A * E * ε * M * r := by
    calc
      _ ≤ (A * ε * M) * (E * r) := by gcongr
      _ = _ := by ring
  have hπb : ‖coverPlanePairing H L - coverPlanePairing H L₀‖ ≤ P * ε * M ^ 2 :=
    hπ β s hs x H hlower
  calc
    _ ≤ R * (P * ε * M ^ 2) +
        (2 * A * E * ε * M * r) * ((A + B) * E * M * r) +
        (2 * B * E * M * r) * (A * E * ε * M * r) := by
      refine (norm_coverExhaustionNumerator_sub_le H x.1 f f₀ L L₀).trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg hR]
      gcongr
    _ = (P * R + T * r ^ 2) * ε * M ^ 2 := by dsimp [T]; ring
    _ ≤ (P * R + (T / c) * R) * ε * M ^ 2 := by
      have hscale : T * r ^ 2 ≤ (T / c) * R := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hc).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hRlow hT])
      gcongr
    _ ≤ C * ε * R * M ^ 2 := by
      dsimp [C]
      nlinarith only [mul_nonneg hR (mul_nonneg hε (sq_nonneg M))]

end FsFltz
