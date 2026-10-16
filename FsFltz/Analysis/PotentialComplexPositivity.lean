import FsFltz.Geometry.PotentialHamiltonian
import FsFltz.Geometry.PrescribedGradingBridge

/-!
# Quantitative complex positivity of the actual potential form

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1477–1495.
The Hessian lower bound controls the native descended symplectic form on
`(q, Jq)`. The immediate consumer is intrinsic Lyapunov positivity.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The potential form evaluated against the standard complex rotation is
exactly the sum of the two Euclidean Hessian quadratic forms. -/
theorem exteriorDerivative_lambdaPotentialForm_complex_eq {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x q : TangentCoordinates n) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x (coordinateComplexStructure n q)) =
      inner ℝ
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.1)) (WithLp.toLp 2 q.1) +
      inner ℝ
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.2)) (WithLp.toLp 2 q.2) := by
  rw [exteriorDerivative_lambdaPotentialForm_euclidean hφ]
  simp [coordinateComplexStructure_apply]

/-- Uniform Hessian positivity controls the native product coordinate norm. -/
theorem exteriorDerivative_lambdaPotentialForm_complex_lower {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (x q : TangentCoordinates n) :
    c * ‖q‖ ^ 2 ≤
      evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
        (lgCoverTangent x q) (lgCoverTangent x (coordinateComplexStructure n q)) := by
  rw [exteriorDerivative_lambdaPotentialForm_complex_eq hφ]
  have hnorm (v : RealSpace n) : ‖v‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) i
  have hr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q.1) (hnorm q.1) 2) hc
  have ha := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q.2) (hnorm q.2) 2) hc
  have hR := hlower (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.1)
  have hA := hlower (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.2)
  rw [Prod.norm_def]
  rcases le_total ‖q.1‖ ‖q.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg hc (sq_nonneg ‖(WithLp.toLp 2 q.1 : EuclideanSpace ℝ (Fin n))‖)]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg hc (sq_nonneg ‖(WithLp.toLp 2 q.2 : EuclideanSpace ℝ (Fin n))‖)]

/-- Strict native complex positivity, including the vacuous rank-zero case. -/
theorem exteriorDerivative_lambdaPotentialForm_complex_pos {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (x q : TangentCoordinates n) (hq : q ≠ 0) :
    0 < evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x (coordinateComplexStructure n q)) :=
  (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hq))).trans_le
    (exteriorDerivative_lambdaPotentialForm_complex_lower hφ hc.le hlower x q)

/-- Hessian quadratic bounds also control mixed evaluations. -/
theorem norm_inner_potentialHessian_le {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c U : ℝ} (hc : 0 ≤ c) (hU : 0 ≤ U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    ‖inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) x u) v‖ ≤
      U * ‖u‖ * ‖v‖ := by
  let H := fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) x
  let B : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
    (innerₛₗ ℝ).compl₁₂ H.toLinearMap (LinearMap.id : _ →ₗ[ℝ] _)
  have hpos (w) : 0 ≤ B w w := (mul_nonneg hc (sq_nonneg _)).trans (hlower x w)
  have hsymm : LinearMap.IsSymm B := by
    constructor
    intro a b
    change inner ℝ (H a) b = inner ℝ (H b) a
    rw [inner_fderiv_gradient_symmetric (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff),
      real_inner_comm]
  have hsq := B.apply_sq_le_of_symm hpos hsymm u v
  have hb := mul_le_mul (hupper x u) (hupper x v) (hpos v)
    (mul_nonneg hU (sq_nonneg _))
  change (inner ℝ (H u) v) ^ 2 ≤ inner ℝ (H u) u * inner ℝ (H v) v at hsq
  rw [Real.norm_eq_abs]
  have habs := sq_abs (inner ℝ (H u) v)
  have hnonneg : 0 ≤ U * ‖u‖ * ‖v‖ := mul_nonneg (mul_nonneg hU (norm_nonneg _)) (norm_nonneg _)
  change inner ℝ (H u) u * inner ℝ (H v) v ≤ _ at hb
  nlinarith [sq_nonneg (|inner ℝ (H u) v| - U * ‖u‖ * ‖v‖)]

/-- A uniform upper bound for the actual potential symplectic form, in
coordinate supremum norms, with only the fixed norm-equivalence constant. -/
theorem exteriorDerivative_lambdaPotentialForm_norm_le {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c U : ℝ} (hc : 0 ≤ c) (hU : 0 ≤ U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (x q r : TangentCoordinates n) :
    ‖evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
        (lgCoverTangent x q) (lgCoverTangent x r)‖ ≤
      (2 * U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ 2) * ‖q‖ * ‖r‖ := by
  let K := ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖
  have hK : 0 ≤ K := norm_nonneg _
  have hnorm (v : RealSpace n) : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖v‖ :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm v
  have hq1 : ‖(WithLp.toLp 2 q.1 : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖q‖ :=
    (hnorm q.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le q) hK)
  have hq2 : ‖(WithLp.toLp 2 q.2 : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖q‖ :=
    (hnorm q.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le q) hK)
  have hr1 : ‖(WithLp.toLp 2 r.1 : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖r‖ :=
    (hnorm r.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le r) hK)
  have hr2 : ‖(WithLp.toLp 2 r.2 : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖r‖ :=
    (hnorm r.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le r) hK)
  rw [exteriorDerivative_lambdaPotentialForm_euclidean hφ]
  refine (norm_sub_le _ _).trans ?_
  have h1 := (norm_inner_potentialHessian_le hφ hc hU hlower hupper
    (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.1) (WithLp.toLp 2 r.2)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hq1 hU) hr2 (norm_nonneg _)
      (mul_nonneg hU (mul_nonneg hK (norm_nonneg _))))
  have h2 := (norm_inner_potentialHessian_le hφ hc hU hlower hupper
    (WithLp.toLp 2 x.1) (WithLp.toLp 2 r.1) (WithLp.toLp 2 q.2)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hr1 hU) hq2 (norm_nonneg _)
      (mul_nonneg hU (mul_nonneg hK (norm_nonneg _))))
  calc
    _ ≤ U * (K * ‖q‖) * (K * ‖r‖) + U * (K * ‖r‖) * (K * ‖q‖) := add_le_add h1 h2
    _ = _ := by dsimp [K]; ring

end FsFltz.Geometry
