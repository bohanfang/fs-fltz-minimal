import FsFltz.Analysis.TailoringPoissonNative

/-!
# Positivity of the actual tailored Poisson scalar

Source: `geometric-part-fsf-proof.tex`, `lem:tailoredpositivity`, lines
1142–1180. Scalar normalization preserves the relative dominant-face
constant. The modification vanishes near the fixed exceptional cylinder;
outside it the proved native C¹ Poisson error is absorbed by dominance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- The same finite toric geometry with the normalized coefficient-one
tuple used by the literal tailoring homotopy. -/
def tailoringNormalizedInput (I : ToricInput n) (β : ℝ) : ToricInput n :=
  { I with
    coeff := fun _ => (Real.exp (-β) : ℂ)
    coeff_ne_zero := fun _ => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _) }

theorem W_tailoringNormalizedInput (I : ToricInput n) (β : ℝ) :
    W (tailoringNormalizedInput I β) = tailoringOriginal I β := by
  funext y
  exact Finset.sum_coe_sort I.vertices (fun v => monomial (Real.exp (-β) : ℂ) v y)

theorem G_tailoringNormalizedInput (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (j : Fin n) :
    G (tailoringNormalizedInput I β) y j =
      (Real.exp (-β) : ℂ) * G (I.alongCoefficientPath 1) y j := by
  simp only [G, tailoringNormalizedInput, ToricInput.alongCoefficientPath_one_coeff,
    Finset.mul_sum, monomial, one_mul]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem toricDerivativeRe_tailoringNormalizedInput (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    toricDerivativeRe (tailoringNormalizedInput I β) y =
      Real.exp (-β) • toricDerivativeRe (I.alongCoefficientPath 1) y := by
  ext j
  change (G (tailoringNormalizedInput I β) y j).re =
    Real.exp (-β) * (G (I.alongCoefficientPath 1) y j).re
  rw [G_tailoringNormalizedInput]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem toricDerivativeIm_tailoringNormalizedInput (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    toricDerivativeIm (tailoringNormalizedInput I β) y =
      Real.exp (-β) • toricDerivativeIm (I.alongCoefficientPath 1) y := by
  ext j
  change (G (tailoringNormalizedInput I β) y j).im =
    Real.exp (-β) * (G (I.alongCoefficientPath 1) y j).im
  rw [G_tailoringNormalizedInput]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Literal quadratic scaling of the inverse-Hessian metric scalar. -/
theorem toricInverseMetricSq_tailoringNormalizedInput
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    toricInverseMetricSq H (tailoringNormalizedInput I β) y =
      Real.exp (-β) ^ 2 * toricInverseMetricSq H (I.alongCoefficientPath 1) y := by
  simp only [toricInverseMetricSq, complexInverseMetricSq,
    toricDerivativeRe_tailoringNormalizedInput, toricDerivativeIm_tailoringNormalizedInput,
    inverseMetricSq, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem maxMonomialMagnitude_coefficientOne (I : ToricInput n) (y : LGSpace n) :
    maxMonomialMagnitude (I.alongCoefficientPath 1) y = Real.exp (supportHeight I y.1) := by
  apply le_antisymm
  · obtain ⟨v, hv⟩ := (I.alongCoefficientPath 1).maxMonomialMagnitude_attained y
    rw [← hv, norm_monomial, ToricInput.alongCoefficientPath_one_coeff, norm_one, one_mul]
    exact Real.exp_le_exp.mpr (I.pairing_le_supportHeight y.1 v)
  · obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
    have h := (I.alongCoefficientPath 1).norm_monomial_le_maxMonomialMagnitude y v
    simpa only [norm_monomial, ToricInput.alongCoefficientPath_one_coeff,
      norm_one, one_mul, hv] using h

/-- Normalization does not change the exceptional radius or relative
dominant-face constant for the actual inverse Hessian. -/
theorem tailoringOriginal_exists_uniform_native_planePairing_lowerBound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ d : ℝ, 0 < d ∧ ∃ R : ℝ, 0 < R ∧ ∀ β : ℝ, ∀ y : LGSpace n,
      R ≤ Real.sqrt (realSquaredNorm y.1) →
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y,
      d * Real.exp (supportHeight I y.1 - β) ^ 2 ≤
        (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringOriginal I β) y hnd := by
  obtain ⟨d, hd, R, hR, hb⟩ := I.coefficientPath_potentialHessian_dominant_lowerBound
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) hc hU hlower hupper
  refine ⟨d ^ 2, sq_pos_of_pos hd, R, hR, fun β y hy hnd => ?_⟩
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [← W_tailoringNormalizedInput,
    planePairing_W_potentialHessian hφ hc hlower, toricInverseMetricSq_tailoringNormalizedInput]
  have h := hb 1 (by simp) (lgCover x) hy
  rw [maxMonomialMagnitude_coefficientOne] at h
  change d * Real.exp (supportHeight I (lgCover x).1) ≤
    Real.sqrt (toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
      (I.alongCoefficientPath 1) (lgCover x)) at h
  have ha : 0 ≤ toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
      (I.alongCoefficientPath 1) (lgCover x) := by
    apply add_nonneg <;> apply inverseMetricSq_nonneg
    · intro v
      exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)
    · intro v
      exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)
  have hs := Real.sq_sqrt ha
  have hsq : d ^ 2 * Real.exp (supportHeight I (lgCover x).1) ^ 2 ≤
      toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
        (I.alongCoefficientPath 1) (lgCover x) := by
    have hsq := mul_self_le_mul_self
      (mul_nonneg hd.le (Real.exp_pos _).le) h
    nlinarith only [hsq, hs]
  have he : Real.exp (supportHeight I (lgCover x).1 - β) =
      Real.exp (-β) * Real.exp (supportHeight I (lgCover x).1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  convert mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.exp (-β))) using 1
  ring

theorem realEuclideanRadius_eq_norm (u : RealSpace n) :
    Real.sqrt (realSquaredNorm u) = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [realSquaredNorm, Real.norm_eq_abs]

/-- The homotopy and its actual differential are literally unchanged on
any fixed radial cylinder once `β` is large enough. -/
theorem tailoringFamily_exists_unchanged_compact_differential (I : ToricInput n) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, ∀ x : TangentCoordinates n,
      Real.sqrt (realSquaredNorm x.1) ≤ R →
      tailoringFamily I β s (lgCover x) = tailoringOriginal I β (lgCover x) ∧
      fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x =
        fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x := by
  obtain ⟨d, hd, B, hB, hb⟩ := tailoringFamily_exists_growing_unchanged_ball I
  refine ⟨max B ((R + 1) / d), lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro β hβ s x hx
  have hBβ := (le_max_left B ((R + 1) / d)).trans hβ
  have hR : R + 1 ≤ d * β := by
    have hh := (le_max_right B ((R + 1) / d)).trans hβ
    exact (div_le_iff₀ hd).mp hh |>.trans_eq (mul_comm β d)
  refine ⟨(hb β hBβ s (lgCover x) (hx.trans (by linarith))).2, ?_⟩
  have hcont : Continuous (fun z : TangentCoordinates n => Real.sqrt (realSquaredNorm z.1)) := by
    simp_rw [realEuclideanRadius_eq_norm]
    exact ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp continuous_fst).norm
  have hnear := hcont.continuousAt.eventually_lt continuousAt_const
    (show Real.sqrt (realSquaredNorm x.1) < R + 1 by linarith)
  have heq : (fun z : TangentCoordinates n => tailoringFamily I β s (lgCover z)) =ᶠ[nhds x]
      (fun z => tailoringOriginal I β (lgCover z)) := by
    filter_upwards [hnear] with z hz
    exact (hb β hBβ s (lgCover z) (hz.le.trans hR)).2
  exact heq.fderiv_eq

/-- The original normalized holomorphic scalar is nonnegative everywhere,
including all possible critical points in the fixed compact region. -/
theorem tailoringOriginal_native_planePairing_nonneg (I : ToricInput n)
    {φ : RealSpace n → ℝ} {c : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ) (y : LGSpace n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) :
    0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringOriginal I β) y hnd := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [← W_tailoringNormalizedInput, planePairing_W_potentialHessian hφ hc hlower]
  apply add_nonneg <;> apply inverseMetricSq_nonneg
  · intro v
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)
  · intro v
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)

/-- Every fixed cylinder is eventually mapped inside the unit base disk,
uniformly through the actual tailoring family. -/
theorem tailoringFamily_exists_compact_norm_lt_one (I : ToricInput n) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, ∀ y : LGSpace n,
      Real.sqrt (realSquaredNorm y.1) ≤ R → ‖tailoringFamily I β s y‖ < 1 := by
  obtain ⟨B, hB, hb⟩ := tailoringFamily_exists_unchanged_compact_differential I R
  obtain ⟨_d, _hd, U, hU, hu⟩ := I.exists_supportHeight_linear_bounds
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  refine ⟨max B (U * R + Real.log (I.vertices.card : ℝ) + 1),
    lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro β hβ s y hy
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [(hb β ((le_max_left _ _).trans hβ) s x hy).1]
  have hheight : supportHeight I (lgCover x).1 ≤ U * R :=
    (hu (lgCover x).1).2.trans (mul_le_mul_of_nonneg_left hy hU.le)
  have hsmall : (I.vertices.card : ℝ) * Real.exp (supportHeight I (lgCover x).1 - β) < 1 := by
    rw [← Real.exp_log hN, ← Real.exp_add, Real.exp_lt_one_iff]
    have hh := (le_max_right B (U * R + Real.log (I.vertices.card : ℝ) + 1)).trans hβ
    linarith
  exact (norm_tailoringOriginal_le_card_mul_max I β (lgCover x)).trans_lt hsmall

/-- All three source positivity assertions for the actual native scalar:
global nonnegativity, a uniform positive quadratic end bound, and strict
positivity over the complement of the open unit base disk. All constants
are chosen before the homotopy and base coefficients. -/
theorem tailoringFamily_exists_uniform_native_planePairing_positivity
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ d : ℝ, 0 < d ∧ ∃ R : ℝ, 0 < R ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
        ∀ hnd : (lgManifold n).Nondegenerate
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y,
        0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd ∧
        (R ≤ Real.sqrt (realSquaredNorm y.1) →
          d * Real.exp (supportHeight I y.1 - β) ^ 2 / 2 ≤
            (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd) ∧
        (1 ≤ ‖tailoringFamily I β s y‖ →
          0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd) := by
  obtain ⟨d, hd, R, hR, hdom⟩ :=
    tailoringOriginal_exists_uniform_native_planePairing_lowerBound I hφ hc hU hlower hupper
  obtain ⟨C, _hC, herror⟩ := tailoringFamily_exists_uniform_native_planePairing_error I hφ hc hlower
  obtain ⟨Bd, _hBd, hdiff⟩ := tailoringFamily_exists_unchanged_compact_differential I R
  obtain ⟨Bn, _hBn, hnorm⟩ := tailoringFamily_exists_compact_norm_lt_one I R
  have hlim : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, heps⟩ := eventually_atTop.mp (hlim.eventually_lt_const
    (show (0 : ℝ) < d / 2 by positivity))
  let β₀ := max 1 (max Be (max Bd Bn))
  refine ⟨d, hd, R, hR, β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ s hs y hnd
  have hBe : Be ≤ β := (le_max_left Be (max Bd Bn)).trans
    ((le_max_right 1 _).trans hβ)
  have hBd : Bd ≤ β := (le_max_left Bd Bn).trans ((le_max_right Be _).trans
    ((le_max_right 1 _).trans hβ))
  have hBn : Bn ≤ β := (le_max_right Bd Bn).trans ((le_max_right Be _).trans
    ((le_max_right 1 _).trans hβ))
  have hend (hy : R ≤ Real.sqrt (realSquaredNorm y.1)) :
      d * Real.exp (supportHeight I y.1 - β) ^ 2 / 2 ≤
        (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd := by
    have he := herror β s hs y hnd
    rw [Real.norm_eq_abs] at he
    have hlo := (abs_le.mp he).1
    have hmargin := hdom β y hy hnd
    have hsmall := mul_le_mul_of_nonneg_right (heps β hBe).le
      (sq_nonneg (Real.exp (supportHeight I y.1 - β)))
    linarith
  have hpositive (hy : R ≤ Real.sqrt (realSquaredNorm y.1)) :
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd :=
    (show 0 < d * Real.exp (supportHeight I y.1 - β) ^ 2 / 2 by positivity).trans_le (hend hy)
  refine ⟨?_, hend, ?_⟩
  · by_cases hy : R ≤ Real.sqrt (realSquaredNorm y.1)
    · exact (hpositive hy).le
    obtain ⟨x, rfl⟩ := lgCover_surjective n y
    have hdif := (hdiff β hBd s x (le_of_not_ge hy)).2
    rw [planePairing_lambdaPotentialForm_eq_cover hφ x
        (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
        (contMDiff_tailoringFamily_lgManifold I β s), hdif,
      ← planePairing_lambdaPotentialForm_eq_cover hφ x
        (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
        (contMDiff_tailoringOriginal_lgManifold I β)]
    exact tailoringOriginal_native_planePairing_nonneg I hφ hc hlower β (lgCover x) hnd
  · intro hf
    by_cases hy : R ≤ Real.sqrt (realSquaredNorm y.1)
    · exact hpositive hy
    exact False.elim (not_lt_of_ge hf (hnorm β hBn s y (le_of_not_ge hy)))

/-- The literal tailored primitive has a symplectic exterior derivative
for every nonnegative base coefficient, with one threshold uniform in `K`.
Closedness and smoothness follow from the proved native exterior calculus. -/
theorem tailoringFamily_exists_uniform_symplectic (I : ToricInput n)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ K : ℝ, 0 ≤ K →
      (lgManifold n).IsSymplecticOn
        ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ := by
  obtain ⟨_d, _hd, _R, _hR, B, hB, hb⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨B, hB, fun β hβ s hs K hK => ?_⟩
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  apply (lgManifold n).isSymplecticOn_exteriorDerivative_rankTwoPrimitive_of_nonneg
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β s)
    (fun y _ => nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) _ hK
  intro y _hy
  exact (hb β hβ s hs y _).1

end FsFltz
