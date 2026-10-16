import FsFltz.Analysis.PotentialPath
import FsFltz.Analysis.CoefficientPathEstimates
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Inverse-Hessian estimates for the adapted potential metric

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 680–695,
and `lem:margin`, lines 746–768. The real and imaginary derivative vectors
are measured by the actual inverse of the positive Hessian. Weighted
Cauchy–Schwarz and the Hessian upper bound give the two analytic bridges
needed for applying dominant-face estimates in this metric.
-/

noncomputable section

namespace FsFltz

open scoped ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal inverse-metric square of a real covector represented by its
Euclidean vector. -/
def inverseMetricSq (H : E ≃L[ℝ] E) (v : E) : ℝ := inner ℝ (H.symm v) v

/-- The source's complex derivative square `Ḡᵀ H⁻¹ G`, expressed by
the actual real and imaginary Euclidean derivative vectors. -/
def complexInverseMetricSq (H : E ≃L[ℝ] E) (gRe gIm : E) : ℝ :=
  inverseMetricSq H gRe + inverseMetricSq H gIm

/-- Symmetry and nonnegativity of the actual Hessian give weighted
Cauchy–Schwarz for its inverse, without a separate metric certificate. -/
theorem inner_sq_le_metric_mul_inverseMetricSq
    (H : E ≃L[ℝ] E)
    (hsymm : ∀ x y : E, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (H x) x) (u v : E) :
    (inner ℝ u v) ^ 2 ≤ inner ℝ (H u) u * inverseMetricSq H v := by
  let B : LinearMap.BilinForm ℝ E :=
    (innerₛₗ ℝ).compl₁₂ H.toLinearMap (LinearMap.id : E →ₗ[ℝ] E)
  have hBpos : ∀ x : E, 0 ≤ B x x := hpos
  have hBsymm : LinearMap.IsSymm B := by
    constructor
    intro x y
    change inner ℝ (H x) y = inner ℝ (H y) x
    rw [hsymm, real_inner_comm]
  have h := B.apply_sq_le_of_symm hBpos hBsymm u (H.symm v)
  change (inner ℝ (H u) (H.symm v)) ^ 2 ≤
    inner ℝ (H u) u * inner ℝ (H (H.symm v)) (H.symm v) at h
  rw [hsymm u (H.symm v), H.apply_symm_apply] at h
  simpa only [inverseMetricSq, real_inner_comm] using h

/-- Positive Hessian quadratic forms make the literal inverse-metric
square nonnegative. -/
theorem inverseMetricSq_nonneg (H : E ≃L[ℝ] E)
    (hpos : ∀ x : E, 0 ≤ inner ℝ (H x) x) (v : E) :
    0 ≤ inverseMetricSq H v := by
  have h := hpos (H.symm v)
  simpa only [H.apply_symm_apply, real_inner_comm, inverseMetricSq] using h

/-- A common upper Hessian bound gives the required common lower bound
for the actual inverse metric, by weighted Cauchy–Schwarz. -/
theorem norm_sq_div_le_inverseMetricSq (H : E ≃L[ℝ] E)
    (hsymm : ∀ x y : E, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (H x) x)
    {C : ℝ} (hC : 0 < C) (hupper : ∀ x : E, inner ℝ (H x) x ≤ C * ‖x‖ ^ 2)
    (v : E) : ‖v‖ ^ 2 / C ≤ inverseMetricSq H v := by
  by_cases hv : v = 0
  · simp [hv, inverseMetricSq]
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have h := inner_sq_le_metric_mul_inverseMetricSq H hsymm hpos v v
  rw [real_inner_self_eq_norm_sq] at h
  have hq := inverseMetricSq_nonneg H hpos v
  have hu := mul_le_mul_of_nonneg_right (hupper v) hq
  have hcanc : ‖v‖ ^ 2 ≤ C * inverseMetricSq H v := by
    have hh : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * (C * inverseMetricSq H v) := by
      nlinarith only [h, hu]
    exact (mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using hh)
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hcanc)

/-- The actual source scalar dominates the squared Euclidean complex
derivative norm divided by the common upper Hessian constant. -/
theorem euclidean_sq_div_le_complexInverseMetricSq (H : E ≃L[ℝ] E)
    (hsymm : ∀ x y : E, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (H x) x)
    {C : ℝ} (hC : 0 < C) (hupper : ∀ x : E, inner ℝ (H x) x ≤ C * ‖x‖ ^ 2)
    (gRe gIm : E) :
    (‖gRe‖ ^ 2 + ‖gIm‖ ^ 2) / C ≤ complexInverseMetricSq H gRe gIm := by
  simpa only [add_div, complexInverseMetricSq] using add_le_add
    (norm_sq_div_le_inverseMetricSq H hsymm hpos hC hupper gRe)
    (norm_sq_div_le_inverseMetricSq H hsymm hpos hC hupper gIm)

/-- The complex Cauchy bound `|u·G| ≤ r sqrt(a_H)` in its literal
real/imaginary vector form, with `r² = uᵀ H u`. -/
theorem norm_complex_pairing_le_metric_radius_mul_sqrt (H : E ≃L[ℝ] E)
    (hsymm : ∀ x y : E, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x : E, 0 ≤ inner ℝ (H x) x) (u gRe gIm : E) :
    ‖(inner ℝ u gRe : ℂ) + Complex.I * (inner ℝ u gIm : ℂ)‖ ≤
      Real.sqrt (inner ℝ (H u) u) * Real.sqrt (complexInverseMetricSq H gRe gIm) := by
  have hRe := inner_sq_le_metric_mul_inverseMetricSq H hsymm hpos u gRe
  have hIm := inner_sq_le_metric_mul_inverseMetricSq H hsymm hpos u gIm
  have ha : 0 ≤ complexInverseMetricSq H gRe gIm :=
    add_nonneg (inverseMetricSq_nonneg H hpos gRe) (inverseMetricSq_nonneg H hpos gIm)
  have hsq : ‖(inner ℝ u gRe : ℂ) + Complex.I * (inner ℝ u gIm : ℂ)‖ ^ 2 ≤
      inner ℝ (H u) u * complexInverseMetricSq H gRe gIm := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.mul_im, zero_mul, one_mul, mul_zero,
      sub_zero, add_zero, zero_add]
    dsimp [complexInverseMetricSq]
    nlinarith only [hRe, hIm]
  have hr := Real.sq_sqrt (hpos u)
  have hg := Real.sq_sqrt ha
  have hnonneg := mul_nonneg (Real.sqrt_nonneg (inner ℝ (H u) u))
    (Real.sqrt_nonneg (complexInverseMetricSq H gRe gIm))
  nlinarith only [hsq, hr, hg, hnonneg, norm_nonneg
    ((inner ℝ u gRe : ℂ) + Complex.I * (inner ℝ u gIm : ℂ))]

section Hessian

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Schwarz symmetry for the actual derivative of the Riesz gradient.
This supplies the symmetry premise of the metric estimates for smooth
potential Hessians, rather than adding symmetry to potential input data. -/
theorem inner_fderiv_gradient_symmetric {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x u v : E) :
    inner ℝ ((fderiv ℝ (gradient φ) x) u) v =
      inner ℝ u ((fderiv ℝ (gradient φ) x) v) := by
  have he : (fun y => (InnerProductSpace.toDual ℝ E) (gradient φ y)) =
      fderiv ℝ φ := funext fun _ => toDual_gradient
  have hd : HasFDerivAt (fderiv ℝ φ)
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
        (fderiv ℝ (gradient φ) x)) x := by
    rw [← he]
    exact (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x
      (((contDiff_gradient hφ).differentiable (by simp) x).hasFDerivAt)
  have h := second_derivative_symmetric
    (fun y => (hφ.differentiable (by simp) y).hasFDerivAt) hd u v
  change inner ℝ ((fderiv ℝ (gradient φ) x) u) v =
    inner ℝ ((fderiv ℝ (gradient φ) x) v) u at h
  exact h.trans (real_inner_comm _ _)

/-- A positive lower Hessian bound makes the actual Hessian invertible in
finite dimensions. No invertibility witness is assumed. -/
theorem fderiv_gradient_bijective_of_lowerBound {φ : E → ℝ} {c : ℝ}
    (hc : 0 < c) (hlower : ∀ x v : E,
      c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) (x : E) :
    Function.Bijective (fderiv ℝ (gradient φ) x) := by
  have hker : (fderiv ℝ (gradient φ) x).toLinearMap.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change (fderiv ℝ (gradient φ) x) v = 0 at hv
    have h := hlower x v
    rw [hv, inner_zero_left] at h
    by_contra hvne
    have hp := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hvne))
    linarith
  have hinj := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The literal positive Hessian as a continuous linear equivalence.
Its inverse is the actual `H⁻¹` used in the source's metric scalar. -/
def potentialHessianEquiv {φ : E → ℝ} {c : ℝ}
    (hc : 0 < c) (hlower : ∀ x v : E,
      c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (gradient φ) x)
    (LinearMap.ker_eq_bot.mpr (fderiv_gradient_bijective_of_lowerBound hc hlower x).1)
    (LinearMap.range_eq_top.mpr (fderiv_gradient_bijective_of_lowerBound hc hlower x).2)

@[simp]
theorem potentialHessianEquiv_apply {φ : E → ℝ} {c : ℝ}
    (hc : 0 < c) (hlower : ∀ x v : E,
      c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) (x v : E) :
    potentialHessianEquiv hc hlower x v = (fderiv ℝ (gradient φ) x) v := rfl

/-- The inverse of the actual positive Hessian consumes its common upper
bound. This is the required bridge from Euclidean derivative dominance to
dominance in the potential metric. -/
theorem potentialHessian_inverseMetric_lowerBound {φ : E → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ x v : E, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v : E, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    (x gRe gIm : E) :
    (‖gRe‖ ^ 2 + ‖gIm‖ ^ 2) / C ≤
      complexInverseMetricSq (potentialHessianEquiv hc hlower x) gRe gIm := by
  apply euclidean_sq_div_le_complexInverseMetricSq _ ?_ ?_ hC ?_ gRe gIm
  · intro u v
    exact inner_fderiv_gradient_symmetric hφ x u v
  · intro v
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower x v)
  · exact hupper x

/-- Weighted complex Cauchy–Schwarz for the actual Hessian of a smooth
uniformly positive potential. -/
theorem potentialHessian_complex_pairing_bound {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v : E, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (x u gRe gIm : E) :
    ‖(inner ℝ u gRe : ℂ) + Complex.I * (inner ℝ u gIm : ℂ)‖ ≤
      Real.sqrt (inner ℝ ((fderiv ℝ (gradient φ) x) u) u) *
        Real.sqrt (complexInverseMetricSq (potentialHessianEquiv hc hlower x) gRe gIm) := by
  simpa only [potentialHessianEquiv_apply] using
    norm_complex_pairing_le_metric_radius_mul_sqrt (potentialHessianEquiv hc hlower x)
      (inner_fderiv_gradient_symmetric hφ x)
      (fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower x v)) u gRe gIm

end Hessian

section Toric

variable {n : ℕ}

/-- The real part of the actual toric derivative in the fixed Euclidean
coordinates. -/
def toricDerivativeRe (I : ToricInput n) (y : LGSpace n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (G I y j).re)

/-- The imaginary part of the same actual toric derivative. -/
def toricDerivativeIm (I : ToricInput n) (y : LGSpace n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (G I y j).im)

/-- The literal inverse-Hessian derivative scalar for the original finite
polynomial on the quotient ambient. At the identity metric this is `a`. -/
def toricInverseMetricSq (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n) : ℝ :=
  complexInverseMetricSq H (toricDerivativeRe I y) (toricDerivativeIm I y)

/-- The sum of the two Euclidean real squares is exactly the existing
complex derivative square; this bridge preserves the original `a` contract. -/
theorem toricDerivativeReIm_norm_sq (I : ToricInput n) (y : LGSpace n) :
    ‖toricDerivativeRe I y‖ ^ 2 + ‖toricDerivativeIm I y‖ ^ 2 = a I y := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [toricDerivativeRe, toricDerivativeIm, WithLp.ofLp_toLp,
    Real.norm_eq_abs]
  simp only [sq_abs]
  simp only [a, Complex.normSq_apply, ← Finset.sum_add_distrib, pow_two]

/-- The native radial scalar is the complex Euclidean pairing with these
literal real and imaginary vectors. -/
theorem b0_eq_complex_euclidean_pairing (I : ToricInput n) (y : LGSpace n) :
    b0 I y =
      (inner ℝ (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n)) (toricDerivativeRe I y) : ℂ) +
        Complex.I * (inner ℝ (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))
          (toricDerivativeIm I y) : ℂ) := by
  apply Complex.ext <;>
    simp [b0, toricDerivativeRe, toricDerivativeIm, PiLp.inner_apply, mul_comm]

/-- An upper Hessian bound converts the existing Euclidean `a` into the
literal inverse-Hessian scalar. -/
theorem a_div_le_toricInverseMetricSq
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x, 0 ≤ inner ℝ (H x) x) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ x, inner ℝ (H x) x ≤ C * ‖x‖ ^ 2) (I : ToricInput n) (y : LGSpace n) :
    a I y / C ≤ toricInverseMetricSq H I y := by
  rw [← toricDerivativeReIm_norm_sq I y]
  exact euclidean_sq_div_le_complexInverseMetricSq H hsymm hpos hC hupper _ _

/-- The exact `b0` satisfies the source's metric Cauchy bound for any
positive symmetric Hessian, with its literal metric radial square. -/
theorem norm_b0_le_metric_radius_mul_sqrt_toricInverseMetricSq
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ x, 0 ≤ inner ℝ (H x) x) (I : ToricInput n) (y : LGSpace n) :
    ‖b0 I y‖ ≤
      Real.sqrt (inner ℝ (H (WithLp.toLp 2 y.1)) (WithLp.toLp 2 y.1)) *
        Real.sqrt (toricInverseMetricSq H I y) := by
  rw [b0_eq_complex_euclidean_pairing]
  exact norm_complex_pairing_le_metric_radius_mul_sqrt H hsymm hpos _ _ _

/-- The coefficient path has one dominant-face constant and radius for
every positive symmetric metric with a given common upper bound. The
constants are chosen before the metric, so this consumes metric families. -/
theorem ToricInput.coefficientPath_inverseMetric_dominant_lowerBound
    (I : ToricInput n) {C : ℝ} (hC : 0 < C) :
    ∃ d : ℝ, 0 < d ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
        ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
          (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
          (∀ x, 0 ≤ inner ℝ (H x) x) →
          (∀ x, inner ℝ (H x) x ≤ C * ‖x‖ ^ 2) →
        d * maxMonomialMagnitude (I.alongCoefficientPath t) y ≤
          Real.sqrt (toricInverseMetricSq H (I.alongCoefficientPath t) y) := by
  obtain ⟨d, hd, L, hL, hdominant⟩ := I.coefficientPath_G_dominant_lowerBound
  have hCsqrt : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  refine ⟨d / Real.sqrt C, div_pos hd hCsqrt, L, hL, ?_⟩
  intro t ht y hy H hsymm hpos hupper
  let J := I.alongCoefficientPath t
  have hlow : a J y / C ≤ toricInverseMetricSq H J y :=
    a_div_le_toricInverseMetricSq H hsymm hpos hC hupper J y
  have hgrad := hdominant t ht y hy
  have hsqa := Real.sq_sqrt (a_nonneg J y)
  have hsC := Real.sq_sqrt hC.le
  have ha : 0 ≤ toricInverseMetricSq H J y :=
    (div_nonneg (a_nonneg J y) hC.le).trans hlow
  have hsH := Real.sq_sqrt ha
  have hdiv : d * maxMonomialMagnitude J y / Real.sqrt C ≤
      Real.sqrt (toricInverseMetricSq H J y) := by
    apply (div_le_iff₀ hCsqrt).mpr
    have hm : a J y ≤ toricInverseMetricSq H J y * C := (div_le_iff₀ hC).mp hlow
    have hprodnonneg := mul_nonneg (Real.sqrt_nonneg (toricInverseMetricSq H J y)) hCsqrt.le
    have hgg : Real.sqrt (a J y) ≤ Real.sqrt (toricInverseMetricSq H J y) * Real.sqrt C := by
      nlinarith only [hsqa, hsC, hsH, hm, hprodnonneg, Real.sqrt_nonneg (a J y)]
    exact hgrad.trans hgg
  simpa only [div_mul_eq_mul_div, J] using hdiv

/-- The proved compact-path dominance estimate transfers to the actual
inverse of any selected smooth positive-Hessian potential with common
bounds. The potential remains a given chosen witness throughout. -/
theorem ToricInput.coefficientPath_potentialHessian_dominant_lowerBound
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2) :
    ∃ d : ℝ, 0 < d ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
        d * maxMonomialMagnitude (I.alongCoefficientPath t) y ≤
          Real.sqrt (toricInverseMetricSq
            (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1))
              (I.alongCoefficientPath t) y) := by
  obtain ⟨d, hd, L, hL, hdominant⟩ := I.coefficientPath_inverseMetric_dominant_lowerBound hC
  refine ⟨d, hd, L, hL, ?_⟩
  intro t ht y hy
  exact hdominant t ht y hy _ (inner_fderiv_gradient_symmetric hφ _)
    (fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)) (hupper _)

/-- One common dominant-face constant works for every actual Hessian in
the prescribed affine potential path and every coefficient-path member,
with the two parameters independent. The chosen endpoint potential is
retained, and the Hessians are constructed from its proved endpoint bounds. -/
theorem ToricInput.coefficientPath_potentialPath_dominant_lowerBound
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2) :
    ∃ d : ℝ, 0 < d ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
        d * maxMonomialMagnitude (I.alongCoefficientPath t) y ≤
          Real.sqrt (toricInverseMetricSq
            (potentialHessianEquiv (lt_min zero_lt_one hc)
              (hessian_potentialPath_lowerBound
                ((contDiff_id.norm_sq ℝ).div_const 2) hφ
                (fun x v => by simp [hessian_half_norm_sq]) hlower hs)
              (WithLp.toLp 2 y.1)) (I.alongCoefficientPath t) y) := by
  obtain ⟨d, hd, L, hL, hdominant⟩ :=
    I.coefficientPath_inverseMetric_dominant_lowerBound
      (zero_lt_one.trans_le (le_max_left (1 : ℝ) C))
  refine ⟨d, hd, L, hL, ?_⟩
  intro t ht s hs y hy
  have hq : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2) :=
    (contDiff_id.norm_sq ℝ).div_const 2
  have hl := hessian_potentialPath_lowerBound (c₀ := 1) hq hφ
    (fun x v => by simp [hessian_half_norm_sq]) hlower hs
  have hu := hessian_potentialPath_upperBound (C₀ := 1) hq hφ
    (fun x v => by simp [hessian_half_norm_sq]) hupper hs
  exact hdominant t ht y hy _
    (inner_fderiv_gradient_symmetric (potentialPath_contDiff_space hq hφ s) _)
    (fun v => (mul_nonneg (lt_min zero_lt_one hc).le (sq_nonneg _)).trans (hl _ v))
    (hu _)

end Toric

end FsFltz
