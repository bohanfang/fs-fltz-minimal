import FsFltz.Analysis.TailoringExhaustionEstimates

/-!
# Native exhaustion numerator and its actual tailoring error

Source: `geometric-part-fsf-proof.tex`, `eq:rankphi`, lines 1129–1132,
and the second `eq:rankerror`, lines 1134–1140. The scalar is the expanded
Hamiltonian numerator of the native rank-two Liouville identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {n : ℕ}

/-- The actual scalar `B_f` in the native rank-two exhaustion identity. -/
def potentialExhaustionNumerator (φ : RealSpace n → ℝ) (f : LGSpace n → ℂ)
    (y : LGSpace n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) : ℝ :=
  let M := lgManifold n
  let Z := M.liouvilleVector (lambdaPotentialForm φ) y
  let X_A := M.hamiltonianVector (M.exteriorDerivative (lambdaPotentialForm φ)) y hnd
    (Complex.reCLM.comp (complexDifferential M f y))
  let X_B := M.hamiltonianVector (M.exteriorDerivative (lambdaPotentialForm φ)) y hnd
    (Complex.imCLM.comp (complexDifferential M f y))
  M.scalarDerivative (fun z => φ z.1) y Z * M.planePairing (lambdaPotentialForm φ) f y hnd +
    ((complexDifferential M f y Z).im - (f y).im / 2) *
      M.scalarDerivative (fun z => φ z.1) y X_A +
    ((f y).re / 2 - (complexDifferential M f y Z).re) *
      M.scalarDerivative (fun z => φ z.1) y X_B

/-- Native `B_f` equals its logarithmic-coordinate formula on precisely
the homogeneous potential end. The differential may be nonholomorphic. -/
theorem potentialExhaustionNumerator_eq_cover {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f) :
    potentialExhaustionNumerator φ f (lgCover x) hnd =
      coverExhaustionNumerator H x.1 (f (lgCover x))
        (fderiv ℝ (fun z => f (lgCover z)) x) := by
  let L := fderiv ℝ (fun z : TangentCoordinates n => f (lgCover z)) x
  have hparts (p : ℂ →L[ℝ] ℝ) (v : TangentCoordinates n) :
      (p.comp (complexDifferential (lgManifold n) f (lgCover x))) (lgCoverTangent x v) =
        inner ℝ (coverCovectorVector (p.comp L) (logCoverRadialLift n)) (WithLp.toLp 2 v.1) +
        inner ℝ (coverCovectorVector (p.comp L) (logCoverAngularLift n)) (WithLp.toLp 2 v.2) := by
    rw [← coverCovectorVector_reconstruction]
    dsimp [L]
    rw [fderiv_complex_lgCover hf]
    rfl
  have hham (p : ℂ →L[ℝ] ℝ) :
      (lgManifold n).scalarDerivative (fun z => φ z.1) (lgCover x)
        ((lgManifold n).hamiltonianVector
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
          (p.comp (complexDifferential (lgManifold n) f (lgCover x)))) = p (L (0, x.1)) := by
    rw [scalarDerivative_potential_hamiltonian hφ x H hH hEuler hnd _ _ _ (hparts p)]
    rw [real_inner_comm, inner_coverCovectorVector]
    rfl
  have hbase : complexDifferential (lgManifold n) f (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) = L (x.1, 0) := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler]
    dsimp [L]
    rw [fderiv_complex_lgCover hf]
    rfl
  have hrad : (lgManifold n).scalarDerivative (fun z => φ z.1) (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
        metricRadialSq H x.1 := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler,
      scalarDerivative_potential_lgCover hφ, fderiv_potential_eq_euclidean_inner hφ,
      euclidean_gradient_eq_hessian_radial hφ x H hH hEuler]
    rfl
  unfold potentialExhaustionNumerator
  dsimp only
  rw [hrad, hbase, hham Complex.reCLM, hham Complex.imCLM,
    planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd hf]
  simp only [coverExhaustionNumerator, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- For the holomorphic polynomial, the covering-coordinate numerator is
the literal inverse-metric margin `Q_W`. -/
theorem coverExhaustionNumerator_W {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (I : ToricInput n) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v) :
    coverExhaustionNumerator H x.1 (W I (lgCover x))
      (fderiv ℝ (fun z => W I (lgCover z)) x) = potentialMetricMargin H I (lgCover x) := by
  have hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ x H hH
  have hπ := (planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd
      (contMDiff_W_lgManifold I)).symm.trans
    (planePairing_W_lambdaPotentialForm hφ I x H hH hnd)
  have hrad : fderiv ℝ (fun z => W I (lgCover z)) x (x.1, 0) = b0 I (lgCover x) := by
    rw [fderiv_complex_lgCover (f := W I) (contMDiff_W_lgManifold I), ContinuousLinearMap.comp_apply,
      complexDifferential_W_lgCover]
    simp [dW, b0, lgCover, mul_comm]
  have hang : fderiv ℝ (fun z => W I (lgCover z)) x (0, x.1) = Complex.I * b0 I (lgCover x) := by
    rw [fderiv_complex_lgCover (f := W I) (contMDiff_W_lgManifold I), ContinuousLinearMap.comp_apply,
      complexDifferential_W_lgCover]
    simp [dW, b0, lgCover, Finset.mul_sum, mul_comm, mul_assoc]
  rw [coverExhaustionNumerator, hπ, hrad, hang]
  simp only [potentialMetricMargin, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, lgCover]
  ring

/-- The second `rankerror` bound for the actual native Hamiltonian
numerator, measured against the actual normalized holomorphic margin.
The constant is chosen before `β,s,x`, and does not involve `K`. -/
theorem tailoringFamily_exists_uniform_native_exhaustionNumerator_error
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) :
    ∃ C : ℝ, 0 < C ∧ ∀ β s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ x : TangentCoordinates n,
      1 ≤ ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ →
      fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1 →
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
      let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
      ‖potentialExhaustionNumerator φ (tailoringFamily I β s) (lgCover x) hnd -
        potentialMetricMargin H (tailoringNormalizedInput I β) (lgCover x)‖ ≤
        C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 *
          Real.exp (supportHeight I x.1 - β) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := tailoringFamily_exists_uniform_coverExhaustionNumerator_error I hc
  refine ⟨C, hC, fun β s hs x hr hEuler hnd => ?_⟩
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  dsimp only
  rw [potentialExhaustionNumerator_eq_cover hφ x H (fun _ => rfl) hEuler hnd
      (contMDiff_tailoringFamily_lgManifold I β s),
    ← coverExhaustionNumerator_W hφ (tailoringNormalizedInput I β) x H (fun _ => rfl),
    W_tailoringNormalizedInput]
  exact hb β s hs x hr H (hlower _)

/-- The actual native exhaustion derivative has the source numerator.
In particular, positivity of the proved numerator controls the Liouville
field for every later nonnegative `K`. -/
theorem scalarDerivative_liouvilleVector_potential_eq_numerator
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    {K : ℝ} (hden : 1 + K * (lgManifold n).planePairing
      (lambdaPotentialForm φ) f (lgCover x) hnd ≠ 0) :
    (lgManifold n).scalarDerivative (fun z => φ z.1) (lgCover x)
      ((lgManifold n).liouvilleVector
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) f K) (lgCover x)) =
      (metricRadialSq H x.1 + K * potentialExhaustionNumerator φ f (lgCover x) hnd) /
        (1 + K * (lgManifold n).planePairing (lambdaPotentialForm φ) f (lgCover x) hnd) := by
  have hrad : (lgManifold n).scalarDerivative (fun z => φ z.1) (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
        metricRadialSq H x.1 := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler,
      scalarDerivative_potential_lgCover hφ, fderiv_potential_eq_euclidean_inner hφ,
      euclidean_gradient_eq_hessian_radial hφ x H hH hEuler]
    rfl
  have h := (lgManifold n).scalarDerivative_liouvilleVector_rankTwoPrimitive
    (fun z => φ z.1) (isSmoothForm_lambdaPotentialForm hφ) hf K (lgCover x) hnd hden
  change _ = (_ + K * potentialExhaustionNumerator φ f (lgCover x) hnd) / _ at h
  rw [hrad] at h
  exact h

end FsFltz
