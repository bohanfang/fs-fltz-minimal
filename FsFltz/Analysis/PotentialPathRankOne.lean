import FsFltz.Analysis.PotentialPathFiberBounds

/-!
# The bounded-value end is empty in rank one

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 792–795;
matching truncations, lines 1011–1049. A one-dimensional inverse Hessian
has zero fiber defect at every regular point. Thus the positive estimate
on the sufficiently large chosen potential level implies emptiness.
-/

noncomputable section

namespace FsFltz

open scoped ContDiff

/-- Equality in weighted Cauchy–Schwarz in the literal one-dimensional
Euclidean model; it needs no sign assumption on the invertible operator. -/
theorem metric_inverseMetric_pairing_eq_rankOne
    (H : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (u v : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (H u) u * inverseMetricSq H v = (inner ℝ u v) ^ 2 := by
  let e : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hvect : ∀ w : EuclideanSpace ℝ (Fin 1), w = w 0 • e := by
    intro w
    ext j
    fin_cases j
    simp [e]
  have hH : ∀ w : EuclideanSpace ℝ (Fin 1), (H w) 0 = w 0 * (H e) 0 := by
    intro w
    conv_lhs => rw [hvect w, map_smul]
    simp
  have hHinv : ∀ w : EuclideanSpace ℝ (Fin 1), (H.symm w) 0 = w 0 * (H.symm e) 0 := by
    intro w
    conv_lhs => rw [hvect w, map_smul]
    simp
  have hprod : (H e) 0 * (H.symm e) 0 = 1 := by
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w 0) (H.apply_symm_apply e)
    rw [hH] at h
    simpa [e, mul_comm] using h
  simp only [inverseMetricSq, PiLp.inner_apply, Fin.sum_univ_one,
    RCLike.inner_apply, RCLike.conj_to_real]
  rw [hH u, hHinv v]
  calc
    _ = ((H e) 0 * (H.symm e) 0) * (u 0 * v 0) ^ 2 := by ring
    _ = _ := by rw [hprod]; ring

/-- The rank-one complex radial square equals the product of the actual
metric radial square and actual inverse-Hessian derivative energy. -/
theorem metricRadialSq_mul_toricInverseMetricSq_eq_normSq_rankOne
    (H : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (I : ToricInput 1) (y : LGSpace 1) :
    metricRadialSq H y.1 * toricInverseMetricSq H I y = Complex.normSq (b0 I y) := by
  have hRe := metric_inverseMetric_pairing_eq_rankOne H
    (WithLp.toLp 2 y.1) (toricDerivativeRe I y)
  have hIm := metric_inverseMetric_pairing_eq_rankOne H
    (WithLp.toLp 2 y.1) (toricDerivativeIm I y)
  rw [b0_eq_complex_euclidean_pairing]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.add_im, Complex.mul_im, zero_mul, one_mul, mul_zero,
    sub_zero, add_zero, zero_add]
  dsimp [metricRadialSq, toricInverseMetricSq, complexInverseMetricSq]
  nlinarith only [hRe, hIm]

/-- The actual intrinsic radial defect is zero at every rank-one regular
point, for every invertible potential Hessian. -/
theorem potentialMetricFiberDefect_eq_zero_rankOne
    (H : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 1))
    (I : ToricInput 1) (y : LGSpace 1) (ha : toricInverseMetricSq H I y ≠ 0) :
    potentialMetricFiberDefect H I y = 0 := by
  rw [potentialMetricFiberDefect,
    ← metricRadialSq_mul_toricInverseMetricSq_eq_normSq_rankOne H I y,
    mul_div_cancel_right₀ _ ha, sub_self]

/-- The literal logarithmic potential level for the same chosen path has
no bounded-value points in rank one, uniformly in its independent parameters.
It therefore does not assert positivity of a zero-dimensional fiber field. -/
theorem ToricInput.coefficientPath_potentialPath_logarithmic_end_empty_rankOne
    (I : ToricInput 1) {φ φEnd : EuclideanSpace ℝ (Fin 1) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    {R : ℝ} (hR : 0 < R) (hend : ∀ x, R ≤ ‖x‖ → φ x = φEnd x)
    (Aamb : ℝ) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      Aamb ≤ F ^ 2 * β ^ 2 / 2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        {y : LGSpace 1 | F ^ 2 * β ^ 2 / 2 ≤
          potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s (WithLp.toLp 2 y.1) ∧
          ‖W (I.alongCoefficientPath t) y‖ ≤ Real.exp β} = ∅ := by
  obtain ⟨F, hF, β₀, hβ₀, hbound⟩ :=
    I.coefficientPath_potentialPath_logarithmic_potential_level
      hφ hEnd1 hEnds hhom hc hlower hupper hR hend Aamb
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨hA, hB⟩ := hbound β hβ
  refine ⟨hA, ?_⟩
  intro t ht s hs
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨_, ha, hdef⟩ := hB t ht s hs y hy.1 hy.2
  rw [potentialMetricFiberDefect_eq_zero_rankOne _ _ _ ha.ne'] at hdef
  have hlevel : 0 < F ^ 2 * β ^ 2 / 2 :=
    div_pos (mul_pos (sq_pos_of_pos hF) (sq_pos_of_pos (hβ₀.trans_le hβ))) (by norm_num)
  exact (hlevel.trans_le hy.1).not_ge hdef

end FsFltz
