import FsFltz.Geometry.PotentialHamiltonian
import FsFltz.Analysis.PotentialPathThreshold

/-!
# Native base derivative for the holomorphic potential primitive

Source: `geometric-part-fsf-proof.tex`, `eq:baseoutward`, lines 869–875.
This identifies the actual derivative needed for the moving base boundary
with the scalar expression controlled by the literal path threshold.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexConjugate

namespace FsFltz.Geometry

variable {n : ℕ}

/-- Chain rule for the native squared superpotential norm. -/
theorem scalarDerivative_normSq_W (I : ToricInput n) (y : LGSpace n)
    (v : (lgManifold n).Tangent y) :
    (lgManifold n).scalarDerivative (fun z => Complex.normSq (W I z)) y v =
      2 * (conj (W I y) * complexDifferential (lgManifold n) (W I) y v).re := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  rw [complexDifferential_W_lgCover]
  exact differentialCovector_absWSq_lgCover I x q

/-- On the homogeneous end, the actual native base derivative is the
source numerator divided by the positive rank-two denominator. -/
theorem scalarDerivative_normSq_W_liouvilleVector_potential
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (I : ToricInput n)
    (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    {K : ℝ} (hK : 0 ≤ K) (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) :
    (lgManifold n).scalarDerivative (fun y => Complex.normSq (W I y)) (lgCover x)
      ((lgManifold n).liouvilleVector
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) (lgCover x)) =
      (2 * (conj (W I (lgCover x)) * b0 I (lgCover x)).re +
        K * toricInverseMetricSq H I (lgCover x) * Complex.normSq (W I (lgCover x))) /
          (1 + K * toricInverseMetricSq H I (lgCover x)) := by
  rw [scalarDerivative_normSq_W,
    complexDifferential_liouvilleVector_potential_W hφ I x H hH hEuler hK hpos]
  simp only [Complex.real_smul, mul_div_assoc, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, sub_zero, add_zero, Complex.normSq_apply]
  ring

/-- The formula-defined path threshold controls the actual moving base
boundary. The pointwise Euler hypothesis restricts this statement to the
homogeneous end, where the earlier homogeneous-potential theorem supplies it. -/
theorem potentialPathThreshold_native_baseoutward
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (t s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) {R K : ℝ} (hR : 0 < R)
    (hbdd : BddAbove (potentialPathRatioSet I hφ hc hlower t s hs R))
    (hK : potentialPathThreshold I hφ hc hlower t s hs R ≤ K) (hKnonneg : 0 ≤ K)
    (x : TangentCoordinates n)
    (hy : R ≤ ‖W (I.alongCoefficientPath t) (lgCover x)‖)
    (ha : 0 < toricInverseMetricSq
      (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 x.1))
      (I.alongCoefficientPath t) (lgCover x))
    (hEuler : let ψ := potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm
      fderiv ℝ (coordinateGradient ψ) x.1 x.1 = coordinateGradient ψ x.1) :
    let ψ := potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm
    let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 x.1)
    let J := I.alongCoefficientPath t
    let Z := (lgManifold n).liouvilleVector
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm ψ) (W J) K) (lgCover x)
    0 < toricInverseMetricSq H J (lgCover x) * Complex.normSq (W J (lgCover x)) /
        (1 + K * toricInverseMetricSq H J (lgCover x)) ∧
      toricInverseMetricSq H J (lgCover x) * Complex.normSq (W J (lgCover x)) /
        (1 + K * toricInverseMetricSq H J (lgCover x)) ≤
      (lgManifold n).scalarDerivative (fun y => Complex.normSq (W J y)) (lgCover x) Z := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let ψ := potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s ∘ e.symm
  let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 x.1)
  have hψ : ContDiff ℝ ∞ ψ :=
    (potentialPath_contDiff_space ((contDiff_id.norm_sq ℝ).div_const 2) hφ s).comp
      e.symm.contDiff
  have hcomp : ψ ∘ e = potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s := by
    funext z
    simp [ψ, Function.comp_def]
  have hH : ∀ v, fderiv ℝ (gradient (ψ ∘ e)) (WithLp.toLp 2 x.1) v = H v := by
    rw [hcomp]
    intro v
    rfl
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v := fun v =>
    (mul_nonneg (le_min zero_le_one hc.le) (sq_nonneg _)).trans
      (hessian_potentialPath_lowerBound ((contDiff_id.norm_sq ℝ).div_const 2) hφ
        (fun x v => by simp [hessian_half_norm_sq]) hlower hs (WithLp.toLp 2 x.1) v)
  have hid := scalarDerivative_normSq_W_liouvilleVector_potential hψ
    (I.alongCoefficientPath t) x H hH hEuler hKnonneg hpos
  exact (potentialPathThreshold_baseoutward_lowerBound I hφ hc hlower t s hs hR
    hbdd hK (lgCover x) hy ha).imp_right (fun h => h.trans_eq hid.symm)

end FsFltz.Geometry
