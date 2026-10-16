import FsFltz.Analysis.PotentialPathMargin
import FsFltz.Analysis.CoefficientPathRegularity
import FsFltz.Analysis.LaurentSurjectivity

/-!
# Literal ratio sets and a finite threshold for the fixed comparison path

Source: `geometric-part-fsf-proof.tex`, exceptional cylinder and
`eq:Kthreshold`, lines 838–875; path threshold, lines 1315–1322.
Nonemptiness, positive denominators, and one common upper bound precede
the supremum deductions. The potential witness is the same given endpoint;
coefficient and potential parameters remain independent in the estimates.
-/

noncomputable section

namespace FsFltz

open scoped ContDiff ComplexConjugate

variable {n : ℕ}

/-- The ratio appearing in the actual inverse-Hessian source threshold. -/
def potentialMetricEndRatio
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n) : ℝ :=
  ‖b0 I y‖ / (toricInverseMetricSq H I y * ‖W I y‖)

/-- Cauchy and dominance bound the actual inverse-Hessian ratio. -/
theorem potentialMetricEndRatio_le_of_gradient_and_growth
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ x z, inner ℝ (H x) z = inner ℝ x (H z))
    (hpos : ∀ v, 0 ≤ inner ℝ (H v) v)
    (I : ToricInput n) (y : LGSpace n) {d A e R U : ℝ}
    (hd : 0 < d) (hA : 0 < A) (he : 0 < e) (hR : 0 < R) (hU : 0 ≤ U)
    (hrad : Real.sqrt (metricRadialSq H y.1) ≤ U * Real.sqrt (realSquaredNorm y.1))
    (hgrad : d * maxMonomialMagnitude I y ≤ Real.sqrt (toricInverseMetricSq H I y))
    (hgrowth : A * Real.exp (e * Real.sqrt (realSquaredNorm y.1)) ≤ maxMonomialMagnitude I y)
    (hy : R ≤ ‖W I y‖) :
    potentialMetricEndRatio H I y ≤ U / (d * A * e * R) := by
  let ρ := Real.sqrt (realSquaredNorm y.1)
  let r := Real.sqrt (metricRadialSq H y.1)
  let g := Real.sqrt (toricInverseMetricSq H I y)
  let M := maxMonomialMagnitude I y
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hM : 0 < M := I.maxMonomialMagnitude_pos y
  have hg : 0 < g := (mul_pos hd hM).trans_le hgrad
  have ha : 0 < toricInverseMetricSq H I y := Real.sqrt_pos.mp hg
  have hW : 0 < ‖W I y‖ := hR.trans_le hy
  have hgg : d * M * g ≤ toricInverseMetricSq H I y := by
    calc
      d * M * g ≤ g * g := mul_le_mul_of_nonneg_right hgrad hg.le
      _ = toricInverseMetricSq H I y := Real.mul_self_sqrt ha.le
  have hfirst : potentialMetricEndRatio H I y ≤ r / (d * M * R) := by
    apply (div_le_div_iff₀ (mul_pos ha hW) (mul_pos (mul_pos hd hM) hR)).mpr
    calc
      ‖b0 I y‖ * (d * M * R) ≤ (r * g) * (d * M * R) :=
        mul_le_mul_of_nonneg_right
          (norm_b0_le_metric_radius_mul_sqrt_toricInverseMetricSq H hsymm hpos I y)
          (mul_pos (mul_pos hd hM) hR).le
      _ = (r * (d * M * g)) * R := by ring
      _ ≤ (r * toricInverseMetricSq H I y) * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgg hr) hR.le
      _ ≤ (r * toricInverseMetricSq H I y) * ‖W I y‖ :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hr ha.le)
      _ = r * (toricInverseMetricSq H I y * ‖W I y‖) := by ring
  have hlinear : A * e * ρ ≤ M := by
    calc
      A * e * ρ = A * (e * ρ) := by ring
      _ ≤ A * Real.exp (e * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (e * ρ)]) hA.le
      _ ≤ M := hgrowth
  apply hfirst.trans
  apply (div_le_div_iff₀ (mul_pos (mul_pos hd hM) hR)
    (mul_pos (mul_pos (mul_pos hd hA) he) hR)).mpr
  calc
    r * (d * A * e * R) ≤ (U * ρ) * (d * A * e * R) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = (A * e * ρ) * (U * d * R) := by ring
    _ ≤ M * (U * d * R) := mul_le_mul_of_nonneg_right hlinear (by positivity)
    _ = U * (d * M * R) := by ring

/-- One common far base disk excludes the Euclidean cylinder on which the
dominant metric estimate is not yet available. Outside it, every denominator
is positive and the actual inverse-Hessian ratios have one fixed upper bound. -/
theorem ToricInput.coefficientPath_metric_ratio_uniform_bound
    (I : ToricInput n) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) (Lmin : ℝ) :
    ∃ R₀ B : ℝ, 0 < R₀ ∧ 0 < B ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        (∀ v, inner ℝ (H v) v ≤ C * ‖v‖ ^ 2) →
        R ≤ ‖W (I.alongCoefficientPath t) y‖ →
          Lmin < Real.sqrt (realSquaredNorm y.1) ∧
          0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
            potentialMetricEndRatio H (I.alongCoefficientPath t) y ≤ B := by
  obtain ⟨d, hd, L, hL, hgrad⟩ := I.coefficientPath_inverseMetric_dominant_lowerBound hC
  obtain ⟨A, hA, e, he, hgrowth⟩ := I.coefficientPath_maxMonomialMagnitude_exponential_lowerBound
  obtain ⟨D, hD, hcylinder⟩ := I.coefficientPath_W_bound_on_radial_cylinder (max L Lmin)
  let R₀ := max 1 D + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  let B := Real.sqrt C / (d * A * e * R₀)
  have hB : 0 < B := div_pos (Real.sqrt_pos.mpr hC) (by positivity)
  refine ⟨R₀, B, hR₀, hB, ?_⟩
  intro R hR t ht y H hsymm hlower hupper hy
  have hyR₀ : R₀ ≤ ‖W (I.alongCoefficientPath t) y‖ := hR.trans hy
  have hycylinder : max L Lmin < Real.sqrt (realSquaredNorm y.1) := by
    by_contra h
    have hD' := hcylinder t ht y (le_of_not_gt h)
    have hDR : D < R₀ := by dsimp [R₀]; linarith [le_max_right (1 : ℝ) D]
    linarith
  have hyend : L ≤ Real.sqrt (realSquaredNorm y.1) :=
    ((le_max_left _ _).trans_lt hycylinder).le
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower v)
  have hgrad' := hgrad t ht y hyend H hsymm hpos hupper
  have ha := Real.sqrt_pos.mp ((mul_pos hd
    ((I.alongCoefficientPath t).maxMonomialMagnitude_pos y)).trans_le hgrad')
  refine ⟨(le_max_right _ _).trans_lt hycylinder, ha,
    potentialMetricEndRatio_le_of_gradient_and_growth H hsymm hpos
    (I.alongCoefficientPath t) y hd hA he hR₀ (Real.sqrt_nonneg C)
    (metricRadialSq_radius_bounds H hc hC hlower hupper y.1).2
    hgrad' (hgrowth t ht y) hyR₀⟩

/-- The identity inverse metric recovers exactly the original scalar `a`. -/
@[simp]
theorem toricInverseMetricSq_refl (I : ToricInput n) (y : LGSpace n) :
    toricInverseMetricSq (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) I y = a I y := by
  simpa only [toricInverseMetricSq, complexInverseMetricSq, inverseMetricSq,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    real_inner_self_eq_norm_sq] using toricDerivativeReIm_norm_sq I y

/-- The actual path Hessian at the original endpoint is literally the
identity equivalence; proof witnesses do not alter this equality. -/
theorem potentialPathHessianEquiv_zero
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin n)) :
    potentialPathHessianEquiv hφ hc hlower 0 hzero x =
      ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext v
  simp only [potentialPathHessianEquiv_apply, potentialPath_zero,
    ContinuousLinearEquiv.refl_apply]
  have he : gradient (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2) = id :=
    funext gradient_half_norm_sq
  rw [he]
  simp

/-- The actual range set in `eq:Kthreshold`, retaining the chosen potential
and the independent coefficient and potential parameters. -/
def potentialPathRatioSet (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (t s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) : Set ℝ :=
  (fun y : LGSpace n => potentialMetricEndRatio
    (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
      (I.alongCoefficientPath t) y) '' {y | R ≤ ‖W (I.alongCoefficientPath t) y‖}

/-- The specified threshold of a single actual coefficient/potential pair. -/
def potentialPathThreshold (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (t s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) : ℝ :=
  1 + 2 * sSup (potentialPathRatioSet I hφ hc hlower t s hs R)

/-- The source's path threshold is the supremum along its fixed diagonal
coefficient/potential path. Independence of the estimates also permits other
parameterizations, without assuming continuity of the threshold function. -/
def coefficientPotentialPathThresholdValues (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (R : ℝ) : Set ℝ :=
  {k | ∃ t, ∃ ht : t ∈ Set.Icc (0 : ℝ) 1,
    k = potentialPathThreshold I hφ hc hlower t t ht R}

/-- The literal finite path-uniform threshold used to choose `K_*/R²`. -/
def coefficientPotentialPathThreshold (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (R : ℝ) : ℝ := sSup (coefficientPotentialPathThresholdValues I hφ hc hlower R)

/-- At the original path endpoint the range set is exactly the prescribed
`S_R`, rather than a substitute set with the same bound. -/
theorem potentialPathRatioSet_zero_zero (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) :
    potentialPathRatioSet I hφ hc hlower 0 0 hzero R = ratioSet I R := by
  simp only [potentialPathRatioSet, potentialPathHessianEquiv_zero,
    ToricInput.alongCoefficientPath_zero, potentialMetricEndRatio, toricInverseMetricSq_refl,
    ratioSet, endRatio]
  rfl

/-- Surjectivity proves nonemptiness of every literal inverse-Hessian ratio
set before its real supremum is used. -/
theorem potentialPathRatioSet_nonempty (I : ToricInput n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (t s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) :
    (potentialPathRatioSet I hφ hc hlower t s hs R).Nonempty := by
  obtain ⟨y, hy⟩ := (I.alongCoefficientPath t).W_surjective (R : ℂ)
  refine ⟨_, y, ?_, rfl⟩
  change R ≤ ‖W (I.alongCoefficientPath t) y‖
  rw [hy, Complex.norm_real, Real.norm_eq_abs]
  exact le_abs_self R

/-- Nonempty actual ratio sets, positive denominators, and their common
bound construct the finite formula-defined path threshold. The original
threshold is retained exactly at `t=s=0`, hence `κ_path(R) ≥ K0(R)`.
`Lmin` may be the radius of the same chosen homogeneous end; the far-value
region is proved to lie outside that cylinder. -/
theorem ToricInput.coefficientPath_potentialPath_threshold_wellDefined
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    (Lmin : ℝ) :
    ∃ R₀ B : ℝ, 0 < R₀ ∧ 0 < B ∧ ∀ R : ℝ, R₀ ≤ R →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1,
        (potentialPathRatioSet I hφ hc hlower t s hs R).Nonempty ∧
        BddAbove (potentialPathRatioSet I hφ hc hlower t s hs R) ∧
        (∀ y : LGSpace n, R ≤ ‖W (I.alongCoefficientPath t) y‖ →
          Lmin < Real.sqrt (realSquaredNorm y.1) ∧
          0 < toricInverseMetricSq
            (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
              (I.alongCoefficientPath t) y) ∧
        1 ≤ potentialPathThreshold I hφ hc hlower t s hs R ∧
          potentialPathThreshold I hφ hc hlower t s hs R ≤ 1 + 2 * B) ∧
      (coefficientPotentialPathThresholdValues I hφ hc hlower R).Nonempty ∧
      BddAbove (coefficientPotentialPathThresholdValues I hφ hc hlower R) ∧
      K0 I R ≤ coefficientPotentialPathThreshold I hφ hc hlower R ∧
        coefficientPotentialPathThreshold I hφ hc hlower R ≤ 1 + 2 * B := by
  obtain ⟨R₀, B, hR₀, hB, hbound⟩ := I.coefficientPath_metric_ratio_uniform_bound
    (lt_min zero_lt_one hc) (zero_lt_one.trans_le (le_max_left (1 : ℝ) C)) Lmin
  refine ⟨R₀, B, hR₀, hB, ?_⟩
  intro R hR
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, R ≤ ‖W (I.alongCoefficientPath t) y‖ →
        Lmin < Real.sqrt (realSquaredNorm y.1) ∧
        0 < toricInverseMetricSq
          (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
            (I.alongCoefficientPath t) y ∧
        potentialMetricEndRatio
          (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
            (I.alongCoefficientPath t) y ≤ B := by
    intro t ht s hs y hy
    obtain ⟨hsymm, hl, hu⟩ := potentialPathHessianEquiv_bounds hφ hc hlower hupper s hs
      (WithLp.toLp 2 y.1)
    exact hbound R hR t ht y _ hsymm hl hu hy
  have hpair : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1,
      (potentialPathRatioSet I hφ hc hlower t s hs R).Nonempty ∧
      BddAbove (potentialPathRatioSet I hφ hc hlower t s hs R) ∧
      (∀ y : LGSpace n, R ≤ ‖W (I.alongCoefficientPath t) y‖ →
        Lmin < Real.sqrt (realSquaredNorm y.1) ∧
        0 < toricInverseMetricSq
          (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
            (I.alongCoefficientPath t) y) ∧
      1 ≤ potentialPathThreshold I hφ hc hlower t s hs R ∧
      potentialPathThreshold I hφ hc hlower t s hs R ≤ 1 + 2 * B := by
    intro t ht s hs
    have hne := potentialPathRatioSet_nonempty I hφ hc hlower t s hs R
    have hup : ∀ q ∈ potentialPathRatioSet I hφ hc hlower t s hs R, q ≤ B := by
      rintro q ⟨y, hy, rfl⟩
      exact (hpoint t ht s hs y hy).2.2
    have hbdd : BddAbove (potentialPathRatioSet I hφ hc hlower t s hs R) := ⟨B, hup⟩
    obtain ⟨q, y, hy, rfl⟩ := hne
    have hq : 0 ≤ potentialMetricEndRatio
        (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
          (I.alongCoefficientPath t) y :=
      div_nonneg (norm_nonneg _) (mul_nonneg (hpoint t ht s hs y hy).2.1.le (norm_nonneg _))
    have hsupnonneg := hq.trans (le_csSup hbdd ⟨y, hy, rfl⟩)
    have hsupupper := csSup_le
      (potentialPathRatioSet_nonempty I hφ hc hlower t s hs R) hup
    refine ⟨potentialPathRatioSet_nonempty I hφ hc hlower t s hs R, hbdd,
      fun y hy => ⟨(hpoint t ht s hs y hy).1, (hpoint t ht s hs y hy).2.1⟩, ?_, ?_⟩
    · dsimp [potentialPathThreshold]
      linarith
    · dsimp [potentialPathThreshold]
      linarith
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hvalues : (coefficientPotentialPathThresholdValues I hφ hc hlower R).Nonempty :=
    ⟨potentialPathThreshold I hφ hc hlower 0 0 hzero R, 0, hzero, rfl⟩
  have hvaluesupper : ∀ k ∈ coefficientPotentialPathThresholdValues I hφ hc hlower R,
      k ≤ 1 + 2 * B := by
    rintro k ⟨t, ht, rfl⟩
    exact (hpair t ht t ht).2.2.2.2
  have hvaluesbdd : BddAbove (coefficientPotentialPathThresholdValues I hφ hc hlower R) :=
    ⟨1 + 2 * B, hvaluesupper⟩
  have hK0 : potentialPathThreshold I hφ hc hlower 0 0 hzero R = K0 I R := by
    rw [potentialPathThreshold, potentialPathRatioSet_zero_zero, K0]
  refine ⟨hpair, hvalues, hvaluesbdd, ?_, csSup_le hvalues hvaluesupper⟩
  rw [← hK0]
  exact le_csSup hvaluesbdd ⟨0, hzero, rfl⟩

/-- The actual formula-defined threshold yields the sharp base-outward
lower bound in `eq:baseoutward`. The two quotient scalars are exactly those
in the native Liouville flow identity; positive denominators are explicit. -/
theorem potentialPathThreshold_baseoutward_lowerBound
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (t s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) {R K : ℝ} (hR : 0 < R)
    (hbdd : BddAbove (potentialPathRatioSet I hφ hc hlower t s hs R))
    (hK : potentialPathThreshold I hφ hc hlower t s hs R ≤ K)
    (y : LGSpace n) (hy : R ≤ ‖W (I.alongCoefficientPath t) y‖)
    (ha : 0 < toricInverseMetricSq
      (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1))
        (I.alongCoefficientPath t) y) :
    let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)
    let J := I.alongCoefficientPath t
    0 < toricInverseMetricSq H J y * Complex.normSq (W J y) /
        (1 + K * toricInverseMetricSq H J y) ∧
      toricInverseMetricSq H J y * Complex.normSq (W J y) /
        (1 + K * toricInverseMetricSq H J y) ≤
      (2 * (conj (W J y) * b0 J y).re +
          K * toricInverseMetricSq H J y * Complex.normSq (W J y)) /
        (1 + K * toricInverseMetricSq H J y) := by
  let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)
  let J := I.alongCoefficientPath t
  have hw : 0 < ‖W J y‖ := hR.trans_le hy
  have hd : 0 < toricInverseMetricSq H J y * ‖W J y‖ := mul_pos ha hw
  have hratio := le_csSup hbdd
    (show potentialMetricEndRatio H J y ∈ potentialPathRatioSet I hφ hc hlower t s hs R from
      ⟨y, hy, rfl⟩)
  have hnonneg : 0 ≤ potentialMetricEndRatio H J y :=
    div_nonneg (norm_nonneg _) hd.le
  have hKone : 1 ≤ K := by
    have hsupnonneg := hnonneg.trans hratio
    dsimp [potentialPathThreshold] at hK
    linarith
  have hden : 0 < 1 + K * toricInverseMetricSq H J y := by positivity
  have hb : 2 * ‖b0 J y‖ ≤ (K - 1) * (toricInverseMetricSq H J y * ‖W J y‖) := by
    have hh : ‖b0 J y‖ / (toricInverseMetricSq H J y * ‖W J y‖) ≤ (K - 1) / 2 := by
      dsimp [potentialMetricEndRatio] at hratio
      dsimp [potentialPathThreshold] at hK
      linarith
    have hh' := (div_le_iff₀ hd).mp hh
    linarith
  have hb' := mul_le_mul_of_nonneg_right hb hw.le
  have hre : -(‖W J y‖ * ‖b0 J y‖) ≤ (conj (W J y) * b0 J y).re := by
    have h := Complex.abs_re_le_norm (conj (W J y) * b0 J y)
    have h' := neg_le_abs (conj (W J y) * b0 J y).re
    rw [norm_mul, Complex.norm_conj] at h
    linarith
  refine ⟨div_pos (mul_pos ha ?_) hden, ?_⟩
  · rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos hw
  · apply (div_le_div_iff_of_pos_right hden).mpr
    rw [Complex.normSq_eq_norm_sq]
    nlinarith

end FsFltz
