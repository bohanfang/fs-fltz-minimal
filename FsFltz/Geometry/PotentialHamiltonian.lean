import FsFltz.Geometry.PotentialLiouvilleRadial
import FsFltz.Geometry.RankTwoLiouville
import FsFltz.Analysis.PotentialMetricEstimates
import FsFltz.Analysis.PotentialPathMargin

/-!
# Native Hamiltonian vectors for the actual potential Hessian

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 680–744,
and the rank-two identities preceding `eq:rankerror`, lines 1116–1140.
The quotient-manifold exterior derivative is identified with the actual
Euclidean Hessian, and Hamiltonian uniqueness determines its inverse blocks.
The resulting Poisson scalar is the literal inverse-Hessian metric scalar.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

private theorem toLp_equiv_apply (v : EuclideanSpace ℝ (Fin n)) :
    WithLp.toLp 2 ((EuclideanSpace.equiv (Fin n) ℝ) v) = v := rfl

private theorem euclidean_equiv_symm_apply (v : RealSpace n) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm v = WithLp.toLp 2 v := rfl

private theorem euclidean_equiv_apply_toLp (v : RealSpace n) :
    (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 v) = v := rfl

/-- The coordinate Hessian and the Euclidean Riesz Hessian are conjugate
by the fixed based-space equivalence. -/
theorem coordinateHessian_eq_euclideanHessian {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (u v : RealSpace n) :
    fderiv ℝ (coordinateGradient φ) u v =
      (EuclideanSpace.equiv (Fin n) ℝ)
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm u)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm v)) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have he : coordinateGradient φ = e ∘ gradient (φ ∘ e) ∘ e.symm :=
    funext (coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by simp)))
  have hs : ContDiff ℝ ∞ (φ ∘ e) := hφ.comp e.contDiff
  have hg := (contDiff_gradient hs).differentiable (by simp)
  rw [he]
  have hd := e.toContinuousLinearMap.hasFDerivAt.comp u
    ((hg (e.symm u)).hasFDerivAt.comp u e.symm.toContinuousLinearMap.hasFDerivAt)
  exact congrArg (fun D : RealSpace n →L[ℝ] RealSpace n => D v) hd.fderiv

/-- Literal Hessian blocks of the native symplectic form, expressed in the
Euclidean spaces used by the proved inverse-metric estimates. -/
theorem exteriorDerivative_lambdaPotentialForm_euclidean {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x q r : TangentCoordinates n) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x r) =
      inner ℝ
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.1)) (WithLp.toLp 2 r.2) -
      inner ℝ
        (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
          (WithLp.toLp 2 x.1) (WithLp.toLp 2 r.1)) (WithLp.toLp 2 q.2) := by
  rw [exteriorDerivative_lambdaPotentialForm_lgCover hφ,
    coordinateHessian_eq_euclideanHessian hφ,
    coordinateHessian_eq_euclideanHessian hφ]
  simp [PiLp.inner_apply, Finset.sum_sub_distrib, mul_comm]

section Hamiltonian

variable {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)

include hφ hH

/-- Invertibility of the actual potential Hessian proves native
nondegeneracy directly, without assuming a Legendre diffeomorphism. -/
theorem nondegenerate_lambdaPotentialForm_of_hessian :
    (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) := by
  intro v hv
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hrad := hv (lgCoverTangent x (0, e (H (e.symm q.1))))
  have hang := hv (lgCoverTangent x (e (H.symm (e.symm q.2)), 0))
  rw [exteriorDerivative_lambdaPotentialForm_euclidean hφ] at hrad hang
  simp only [hH] at hrad hang
  have hq₁ : q.1 = 0 := by
    have hz : H (e.symm q.1) = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simpa only [e, toLp_equiv_apply, euclidean_equiv_symm_apply,
        WithLp.toLp_zero, map_zero, inner_zero_left, sub_zero] using hrad
    exact e.symm.injective (H.injective (by simpa using hz))
  have hq₂ : q.2 = 0 := by
    have hz : e.symm q.2 = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      simpa only [e, toLp_equiv_apply, euclidean_equiv_symm_apply, WithLp.toLp_zero, map_zero,
        H.apply_symm_apply, inner_zero_right, zero_sub, neg_eq_zero] using hang
    exact e.symm.injective (by simpa using hz)
  have he : q = 0 := Prod.ext hq₁ hq₂
  rw [he, map_zero]

/-- A native covector with real and angular Euclidean coefficient vectors
has the literal inverse-Hessian Hamiltonian blocks. The reconstruction
hypothesis only describes the covector on the surjective quotient cover. -/
theorem hamiltonianVector_lambdaPotentialForm
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (p : (lgManifold n).Tangent (lgCover x) →L[ℝ] ℝ)
    (pRad pAng : EuclideanSpace ℝ (Fin n))
    (hp : ∀ q : TangentCoordinates n, p (lgCoverTangent x q) =
      inner ℝ pRad (WithLp.toLp 2 q.1) + inner ℝ pAng (WithLp.toLp 2 q.2)) :
    (lgManifold n).hamiltonianVector
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd p =
      lgCoverTangent x
        ((EuclideanSpace.equiv (Fin n) ℝ) (H.symm pAng),
          -(EuclideanSpace.equiv (Fin n) ℝ) (H.symm pRad)) := by
  apply sub_eq_zero.mp
  apply hnd
  intro w
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 w
  rw [evalTwo_sub_left, hamiltonianVector_contraction,
    exteriorDerivative_lambdaPotentialForm_euclidean hφ, hp]
  have hs := inner_fderiv_gradient_symmetric
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) (WithLp.toLp 2 x.1)
  simp only [hH] at hs
  simp only [toLp_equiv_apply, WithLp.toLp_neg, hH, H.apply_symm_apply,
    inner_neg_right, sub_neg_eq_add]
  rw [hs, H.apply_symm_apply, real_inner_comm pRad (WithLp.toLp 2 q.1)]
  ring

/-- The Poisson pairing of arbitrary native real covectors is the literal
inverse-Hessian cross pairing, including its contraction-convention sign. -/
theorem rankTwoPairing_lambdaPotentialForm
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (p q : (lgManifold n).Tangent (lgCover x) →L[ℝ] ℝ)
    (pRad pAng qRad qAng : EuclideanSpace ℝ (Fin n))
    (hp : ∀ z : TangentCoordinates n, p (lgCoverTangent x z) =
      inner ℝ pRad (WithLp.toLp 2 z.1) + inner ℝ pAng (WithLp.toLp 2 z.2))
    (hq : ∀ z : TangentCoordinates n, q (lgCoverTangent x z) =
      inner ℝ qRad (WithLp.toLp 2 z.1) + inner ℝ qAng (WithLp.toLp 2 z.2)) :
    (lgManifold n).rankTwoPairing
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd p q =
      inner ℝ (H.symm qAng) pRad - inner ℝ (H.symm qRad) pAng := by
  unfold SmoothManifold.rankTwoPairing
  rw [hamiltonianVector_lambdaPotentialForm hφ x H hH hnd q qRad qAng hq, hp]
  simp only [toLp_equiv_apply, WithLp.toLp_neg, inner_neg_right,
    real_inner_comm, sub_eq_add_neg]

end Hamiltonian

/-- The actual quotient differential of the finite polynomial has the
real coefficient blocks prescribed by its holomorphic derivative. -/
theorem complexDifferential_W_lgCover_re (I : ToricInput n)
    (x q : TangentCoordinates n) :
    (complexDifferential (lgManifold n) (W I) (lgCover x) (lgCoverTangent x q)).re =
      inner ℝ (toricDerivativeRe I (lgCover x)) (WithLp.toLp 2 q.1) +
        inner ℝ (-toricDerivativeIm I (lgCover x)) (WithLp.toLp 2 q.2) := by
  rw [complexDifferential_W_lgCover]
  simp [dW, toricDerivativeRe, toricDerivativeIm, PiLp.inner_apply,
    Finset.sum_add_distrib, mul_comm, sub_eq_add_neg]

/-- The imaginary coefficient blocks use the same literal derivative
vectors and the source's positive complex-structure convention. -/
theorem complexDifferential_W_lgCover_im (I : ToricInput n)
    (x q : TangentCoordinates n) :
    (complexDifferential (lgManifold n) (W I) (lgCover x) (lgCoverTangent x q)).im =
      inner ℝ (toricDerivativeIm I (lgCover x)) (WithLp.toLp 2 q.1) +
        inner ℝ (toricDerivativeRe I (lgCover x)) (WithLp.toLp 2 q.2) := by
  rw [complexDifferential_W_lgCover]
  simp [dW, toricDerivativeRe, toricDerivativeIm, PiLp.inner_apply,
    Finset.sum_add_distrib, mul_comm, add_comm]

/-- For the literal polynomial, the native Poisson scalar is the source's
actual inverse-Hessian scalar, for every point and coefficient tuple. -/
theorem planePairing_W_lambdaPotentialForm {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (I : ToricInput n) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)) :
    (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) (lgCover x) hnd =
      toricInverseMetricSq H I (lgCover x) := by
  unfold SmoothManifold.planePairing
  rw [rankTwoPairing_lambdaPotentialForm hφ x H hH hnd _ _
    (toricDerivativeRe I (lgCover x)) (-toricDerivativeIm I (lgCover x))
    (toricDerivativeIm I (lgCover x)) (toricDerivativeRe I (lgCover x))
    (complexDifferential_W_lgCover_re I x) (complexDifferential_W_lgCover_im I x)]
  simp [toricInverseMetricSq, complexInverseMetricSq, inverseMetricSq]

/-- The pairing identification instantiated with the inverse of the
actual positive Hessian produced by the analytic metric API. -/
theorem planePairing_W_potentialHessian {φ : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (I : ToricInput n) (x : TangentCoordinates n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)) :
    (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) (lgCover x) hnd =
      toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
        I (lgCover x) :=
  planePairing_W_lambdaPotentialForm hφ I x _ (fun _ => rfl) hnd

/-- A holomorphic differential written with its real and imaginary
Euclidean derivative vectors has the native inverse-metric Poisson square.
This also applies to scalar-normalized polynomials without changing input. -/
theorem planePairing_lambdaPotentialForm_holomorphic {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (f : (lgManifold n).Point → ℂ) (gRe gIm : EuclideanSpace ℝ (Fin n))
    (hRe : ∀ q : TangentCoordinates n,
      (complexDifferential (lgManifold n) f (lgCover x) (lgCoverTangent x q)).re =
        inner ℝ gRe (WithLp.toLp 2 q.1) + inner ℝ (-gIm) (WithLp.toLp 2 q.2))
    (hIm : ∀ q : TangentCoordinates n,
      (complexDifferential (lgManifold n) f (lgCover x) (lgCoverTangent x q)).im =
        inner ℝ gIm (WithLp.toLp 2 q.1) + inner ℝ gRe (WithLp.toLp 2 q.2)) :
    (lgManifold n).planePairing (lambdaPotentialForm φ) f (lgCover x) hnd =
      complexInverseMetricSq H gRe gIm := by
  unfold SmoothManifold.planePairing
  rw [rankTwoPairing_lambdaPotentialForm hφ x H hH hnd _ _ gRe (-gIm) gIm gRe hRe hIm]
  simp [complexInverseMetricSq, inverseMetricSq]

/-- Uniform positivity constructs the native nondegeneracy witness used
by the Hamiltonian and pairing formulas from the actual Hessian. -/
theorem nondegenerate_lambdaPotentialForm_potentialHessian
    {φ : RealSpace n → ℝ} {c : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (x : TangentCoordinates n) :
    (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) :=
  nondegenerate_lambdaPotentialForm_of_hessian hφ x
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl)

/-- The real potential defines a smooth scalar on the actual quotient. -/
theorem contMDiff_potentialValue {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => φ y.1) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hlog : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, RealSpace n) ∞
      (fun y : (lgManifold n).Point => y.1) :=
    (contMDiff_fst : ContMDiff (lgModel n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.fst : LGSpace n → _)).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  exact hφ.contMDiff.comp hlog

/-- The intrinsic quotient differential of the potential pulls back to
its actual real derivative, with no angle representative choice. -/
theorem scalarDerivative_potential_lgCover {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x q : TangentCoordinates n) :
    (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x q) =
      fderiv ℝ φ x.1 q.1 := by
  have hd := mfderiv_comp_apply x
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv] at hd
  have hfd := ((hφ.differentiable (by simp) x.1).hasFDerivAt).comp x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  change fderiv ℝ (fun z : TangentCoordinates n => φ z.1) x q = _ at hd
  exact hd.symm.trans (congrArg (fun D : TangentCoordinates n →L[ℝ] ℝ => D q) hfd.fderiv)

/-- The real derivative is the Euclidean Riesz pairing in the fixed basis. -/
theorem fderiv_potential_eq_euclidean_inner {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (u v : RealSpace n) :
    fderiv ℝ φ u v = inner ℝ
      (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 u))
      (WithLp.toLp 2 v) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hd := inner_gradient_left (f := φ ∘ e) (x := e.symm u) (y := e.symm v)
  rw [fderiv_comp (e.symm u) (hφ.differentiable (by simp) u) e.differentiableAt,
    e.fderiv] at hd
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    e.apply_symm_apply, e, euclidean_equiv_symm_apply, euclidean_equiv_apply_toLp] using hd.symm

section HolomorphicFlow

variable {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (I : ToricInput n) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)

include hφ hH hEuler

/-- Euler's identity and Hessian invertibility determine the actual base
Liouville vector at a point of the homogeneous end. -/
theorem liouvilleVector_lambdaPotentialForm_radial_of_hessian :
    (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
  (lgManifold n).liouvilleVector_eq _ _
    (nondegenerate_lambdaPotentialForm_of_hessian hφ x H hH)
    (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)

/-- On the homogeneous end, the Riesz gradient is the Hessian applied to
the radial vector. This is a consequence of the coordinate Euler identity. -/
theorem euclidean_gradient_eq_hessian_radial :
    gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x.1) =
      H (WithLp.toLp 2 x.1) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hh := coordinateHessian_eq_euclideanHessian hφ x.1 x.1
  simp only [euclidean_equiv_symm_apply, hH] at hh
  have hg := coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by simp)) x.1
  simp only [euclidean_equiv_symm_apply] at hg
  exact (e.injective (hh.symm.trans (hEuler.trans hg))).symm

/-- The homogeneous potential derivative on any native Hamiltonian field
is its literal radial pairing with the angular covector coefficient. -/
theorem scalarDerivative_potential_hamiltonian
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (p : (lgManifold n).Tangent (lgCover x) →L[ℝ] ℝ)
    (pRad pAng : EuclideanSpace ℝ (Fin n))
    (hp : ∀ q : TangentCoordinates n, p (lgCoverTangent x q) =
      inner ℝ pRad (WithLp.toLp 2 q.1) + inner ℝ pAng (WithLp.toLp 2 q.2)) :
    (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
        ((lgManifold n).hamiltonianVector
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd p) =
      inner ℝ (WithLp.toLp 2 x.1) pAng := by
  rw [hamiltonianVector_lambdaPotentialForm hφ x H hH hnd p pRad pAng hp,
    scalarDerivative_potential_lgCover hφ, fderiv_potential_eq_euclidean_inner hφ,
    euclidean_gradient_eq_hessian_radial hφ x H hH hEuler, toLp_equiv_apply]
  have hs := inner_fderiv_gradient_symmetric
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) (WithLp.toLp 2 x.1)
  simp only [hH] at hs
  rw [hs, H.apply_symm_apply]

/-- The source's `eq:holoflow` for the actual updated native Liouville
vector, on precisely the points where the potential is homogeneous. -/
theorem complexDifferential_liouvilleVector_potential_W {K : ℝ}
    (hK : 0 ≤ K) (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) :
    complexDifferential (lgManifold n) (W I) (lgCover x)
        ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) (lgCover x)) =
      (b0 I (lgCover x) + (K * toricInverseMetricSq H I (lgCover x) / 2) • W I (lgCover x)) /
        ((1 + K * toricInverseMetricSq H I (lgCover x) : ℝ) : ℂ) := by
  have hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ x H hH
  have hp := planePairing_W_lambdaPotentialForm hφ I x H hH hnd
  have ha : 0 ≤ toricInverseMetricSq H I (lgCover x) :=
    add_nonneg (inverseMetricSq_nonneg H hpos _) (inverseMetricSq_nonneg H hpos _)
  have hden : 1 + K * (lgManifold n).planePairing
      (lambdaPotentialForm φ) (W I) (lgCover x) hnd ≠ 0 := by
    rw [hp]
    positivity
  rw [(lgManifold n).complexDifferential_liouvilleVector_rankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I) K (lgCover x) hnd hden,
    hp, liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler]
  change (complexDifferential (lgManifold n) (W I) (lgCover x)
      (lgCoverTangent x (x.1, 0)) + _) / _ = _
  rw [complexDifferential_W_lgCover I x (x.1, 0)]
  congr 2
  simp [dW, b0, lgCover, mul_comm]

/-- The source's `eq:holoexhaustion`, with the actual native updated
Liouville vector and the literal margin scalar of the analytic estimates. -/
theorem scalarDerivative_liouvilleVector_potential_W {K : ℝ}
    (hK : 0 ≤ K) (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) :
    (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
        ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) (lgCover x)) =
      (metricRadialSq H x.1 + K * potentialMetricMargin H I (lgCover x)) /
        (1 + K * toricInverseMetricSq H I (lgCover x)) := by
  have hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ x H hH
  have hp := planePairing_W_lambdaPotentialForm hφ I x H hH hnd
  have ha : 0 ≤ toricInverseMetricSq H I (lgCover x) :=
    add_nonneg (inverseMetricSq_nonneg H hpos _) (inverseMetricSq_nonneg H hpos _)
  have hden : 1 + K * (lgManifold n).planePairing
      (lambdaPotentialForm φ) (W I) (lgCover x) hnd ≠ 0 := by rw [hp]; positivity
  have hbase : complexDifferential (lgManifold n) (W I) (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
        b0 I (lgCover x) := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler,
      complexDifferential_W_lgCover I x (x.1, 0)]
    simp [dW, b0, lgCover, mul_comm]
  have hrad : (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
        metricRadialSq H x.1 := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler,
      scalarDerivative_potential_lgCover hφ, fderiv_potential_eq_euclidean_inner hφ,
      euclidean_gradient_eq_hessian_radial hφ x H hH hEuler]
    rfl
  have hA := scalarDerivative_potential_hamiltonian hφ x H hH hEuler hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover x)))
    (toricDerivativeRe I (lgCover x)) (-toricDerivativeIm I (lgCover x))
    (complexDifferential_W_lgCover_re I x)
  have hB := scalarDerivative_potential_hamiltonian hφ x H hH hEuler hnd
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover x)))
    (toricDerivativeIm I (lgCover x)) (toricDerivativeRe I (lgCover x))
    (complexDifferential_W_lgCover_im I x)
  have hb := b0_eq_complex_euclidean_pairing I (lgCover x)
  have hbRe := congrArg Complex.re hb
  have hbIm := congrArg Complex.im hb
  simp only [lgCover, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, one_mul, zero_add] at hbRe hbIm
  change (b0 I (lgCover x)).re =
    inner ℝ (WithLp.toLp 2 x.1) (toricDerivativeRe I (lgCover x)) at hbRe
  change (b0 I (lgCover x)).im =
    inner ℝ (WithLp.toLp 2 x.1) (toricDerivativeIm I (lgCover x)) at hbIm
  rw [inner_neg_right, ← hbIm] at hA
  rw [← hbRe] at hB
  rw [(lgManifold n).scalarDerivative_liouvilleVector_rankTwoPrimitive
    (fun y => φ y.1) (isSmoothForm_lambdaPotentialForm hφ)
    (contMDiff_W_lgManifold I) K (lgCover x) hnd hden]
  rw [hp, hbase, hrad, hA, hB]
  congr 1
  simp only [potentialMetricMargin, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, lgCover]
  ring

end HolomorphicFlow

/-- Both native holomorphic Liouville identities on the literal common
homogeneous end. The Hessian inverse, nondegeneracy, radial field and Euler
identity are derived from the chosen smooth positive-Hessian potential. -/
theorem liouville_identities_potential_W_on_homogeneous_end
    {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    (I : ToricInput n) (x : TangentCoordinates n)
    (hx : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖)
    {K : ℝ} (hK : 0 ≤ K) :
    let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
    let Z := (lgManifold n).liouvilleVector
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) (lgCover x)
    complexDifferential (lgManifold n) (W I) (lgCover x) Z =
        (b0 I (lgCover x) + (K * toricInverseMetricSq H I (lgCover x) / 2) • W I (lgCover x)) /
          ((1 + K * toricInverseMetricSq H I (lgCover x) : ℝ) : ℂ) ∧
      (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) Z =
        (metricRadialSq H x.1 + K * potentialMetricMargin H I (lgCover x)) /
          (1 + K * toricInverseMetricSq H I (lgCover x)) := by
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  have hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v := fun _ => rfl
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end
    hφ hEnd hhom hR heq hx
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v := fun v =>
    (mul_nonneg hc.le (sq_nonneg _)).trans (hlower (WithLp.toLp 2 x.1) v)
  exact ⟨complexDifferential_liouvilleVector_potential_W hφ I x H hH hEuler hK hpos,
    scalarDerivative_liouvilleVector_potential_W hφ I x H hH hEuler hK hpos⟩

end FsFltz.Geometry
