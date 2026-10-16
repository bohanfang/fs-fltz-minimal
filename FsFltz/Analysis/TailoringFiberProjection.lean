import FsFltz.Analysis.TailoringPoissonPositivity
import FsFltz.Geometry.RankTwoFiberProjection

/-!
# The actual tailored fiber projection in logarithmic coordinates

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1208–1220.
The inverse Hessian constructs the Hamiltonian vectors of the actual
covering-coordinate covectors. The displayed continuous linear projector is
proved to push forward to the native symplectic projection. Its norm is thus
measured in the fixed logarithmic coordinates, rather than an arbitrary chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- The literal inverse-Hessian Hamiltonian vector of a cover covector. -/
def coverHamiltonianVector
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : TangentCoordinates n →L[ℝ] ℝ) : TangentCoordinates n :=
  logCoverRadialLift n (H.symm (coverCovectorVector p (logCoverAngularLift n))) -
    logCoverAngularLift n (H.symm (coverCovectorVector p (logCoverRadialLift n)))

theorem coverHamiltonianVector_sub
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q : TangentCoordinates n →L[ℝ] ℝ) :
    coverHamiltonianVector H (p - q) =
      coverHamiltonianVector H p - coverHamiltonianVector H q := by
  simp only [coverHamiltonianVector, coverCovectorVector_sub, map_sub]
  abel

theorem coverCovectorVector_smul (t : ℝ) (p : TangentCoordinates n →L[ℝ] ℝ)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
    coverCovectorVector (t • p) e = t • coverCovectorVector p e := by
  simp only [coverCovectorVector, ContinuousLinearMap.smul_comp, map_smul]

theorem coverHamiltonianVector_smul
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : ℝ) (p : TangentCoordinates n →L[ℝ] ℝ) :
    coverHamiltonianVector H (t • p) = t • coverHamiltonianVector H p := by
  simp only [coverHamiltonianVector, coverCovectorVector_smul, map_smul, smul_sub]

theorem norm_coverHamiltonianVector_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : TangentCoordinates n →L[ℝ] ℝ) :
    ‖coverHamiltonianVector H p‖ ≤
      coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖p‖ := by
  have hterm (e f : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
      ‖e (H.symm (coverCovectorVector p f))‖ ≤
        ‖e‖ * ‖H.symm.toContinuousLinearMap‖ * (‖p‖ * ‖f‖) := by
    calc
      _ ≤ ‖e‖ * ‖H.symm (coverCovectorVector p f)‖ := e.le_opNorm _
      _ ≤ ‖e‖ * (‖H.symm.toContinuousLinearMap‖ * ‖coverCovectorVector p f‖) := by
        gcongr
        exact H.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e‖ * (‖H.symm.toContinuousLinearMap‖ * (‖p‖ * ‖f‖)) := by
        gcongr
        exact norm_coverCovectorVector_le p f
      _ = _ := by ring
  exact (norm_sub_le _ _).trans ((add_le_add
    (hterm (logCoverRadialLift n) (logCoverAngularLift n))
    (hterm (logCoverAngularLift n) (logCoverRadialLift n))).trans_eq (by
      dsimp [coverPoissonNormConstant]; ring))

/-- The numerator of the source's rank-two projection correction. -/
def coverFiberProjectionNumerator
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) :
    TangentCoordinates n →L[ℝ] TangentCoordinates n :=
  (Complex.imCLM.comp L).smulRight (coverHamiltonianVector H (Complex.reCLM.comp L)) -
    (Complex.reCLM.comp L).smulRight (coverHamiltonianVector H (Complex.imCLM.comp L))

/-- The source projection, as an actual continuous linear map on the cover. -/
def coverFiberProjection
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) :
    TangentCoordinates n →L[ℝ] TangentCoordinates n :=
  ContinuousLinearMap.id ℝ (TangentCoordinates n) +
    (coverPlanePairing H L)⁻¹ • coverFiberProjectionNumerator H L

theorem coverFiberProjection_apply
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) (v : TangentCoordinates n) :
    coverFiberProjection H L v =
      v + ((L v).im / coverPlanePairing H L) •
          coverHamiltonianVector H (Complex.reCLM.comp L) -
        ((L v).re / coverPlanePairing H L) •
          coverHamiltonianVector H (Complex.imCLM.comp L) := by
  simp only [coverFiberProjection, coverFiberProjectionNumerator,
    add_apply, ContinuousLinearMap.id_apply,
    smul_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.imCLM_apply, Complex.reCLM_apply, smul_sub, smul_smul, div_eq_mul_inv]
  simp only [mul_comm, add_sub_assoc]

/-- The coordinate Hamiltonian is the native Hamiltonian of the same actual
covector, via the quotient covering derivative. -/
theorem lgCoverTangent_coverHamiltonianVector {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (p : (lgManifold n).Tangent (lgCover x) →L[ℝ] ℝ) :
    lgCoverTangent x (coverHamiltonianVector H (p.comp (lgCoverTangent x))) =
      (lgManifold n).hamiltonianVector
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd p := by
  rw [hamiltonianVector_lambdaPotentialForm hφ x H hH hnd p
    (coverCovectorVector (p.comp (lgCoverTangent x)) (logCoverRadialLift n))
    (coverCovectorVector (p.comp (lgCoverTangent x)) (logCoverAngularLift n))
    (fun v => coverCovectorVector_reconstruction (p.comp (lgCoverTangent x)) v)]
  congr 1
  simp [coverHamiltonianVector, logCoverRadialLift, logCoverAngularLift]

/-- The displayed coordinate projection is the actual native symplectic
projection of the actual complex map, including nonholomorphic maps. -/
theorem lgCoverTangent_coverFiberProjection {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (v : TangentCoordinates n) :
    lgCoverTangent x
        (coverFiberProjection H (fderiv ℝ (fun z => f (lgCover z)) x) v) =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
        (lgCoverTangent x v) := by
  rw [coverFiberProjection_apply, map_sub, map_add, map_smul, map_smul,
    ← planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd hf,
    fderiv_complex_lgCover hf]
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
    lgCoverTangent_coverHamiltonianVector hφ x H hH hnd,
    lgCoverTangent_coverHamiltonianVector hφ x H hH hnd]
  rfl

end FsFltz
