import FsFltz.Analysis.TailoringPoissonEstimates
import FsFltz.Geometry.PotentialHamiltonian

/-!
# Native Poisson error for the tailored quotient map

Source: `geometric-part-fsf-proof.tex`, `eq:rankerror`, lines 1134–1140,
and `lem:tailoredpositivity`, lines 1142–1180. The scalar in this module is
the actual Hamiltonian pairing of the native quotient differentials for
the literal potential primitive. No error estimate is assumed as input.
-/

noncomputable section

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- The actual complex manifold differential pulls back to the actual
Fréchet differential on the logarithmic cover. -/
theorem fderiv_complex_lgCover {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (x : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n => f (lgCover z)) x =
      (complexDifferential (lgManifold n) f (lgCover x)).comp (lgCoverTangent x) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have h := mfderiv_comp x (hf.mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv] at h
  exact h

/-- Native and covering-coordinate Poisson scalars agree for every smooth
complex map, including the nonholomorphic tailored family. -/
theorem planePairing_lambdaPotentialForm_eq_cover {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f) :
    (lgManifold n).planePairing (lambdaPotentialForm φ) f (lgCover x) hnd =
      coverPlanePairing H (fderiv ℝ (fun z => f (lgCover z)) x) := by
  let L := fderiv ℝ (fun z : TangentCoordinates n => f (lgCover z)) x
  let p := Complex.reCLM.comp L
  let q := Complex.imCLM.comp L
  have hp (v : TangentCoordinates n) :
      (Complex.reCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
        (lgCoverTangent x v) =
      inner ℝ (coverCovectorVector p (logCoverRadialLift n)) (WithLp.toLp 2 v.1) +
        inner ℝ (coverCovectorVector p (logCoverAngularLift n)) (WithLp.toLp 2 v.2) := by
    rw [← coverCovectorVector_reconstruction]
    dsimp [p, L]
    rw [fderiv_complex_lgCover hf]
    rfl
  have hq (v : TangentCoordinates n) :
      (Complex.imCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
        (lgCoverTangent x v) =
      inner ℝ (coverCovectorVector q (logCoverRadialLift n)) (WithLp.toLp 2 v.1) +
        inner ℝ (coverCovectorVector q (logCoverAngularLift n)) (WithLp.toLp 2 v.2) := by
    rw [← coverCovectorVector_reconstruction]
    dsimp [q, L]
    rw [fderiv_complex_lgCover hf]
    rfl
  exact rankTwoPairing_lambdaPotentialForm hφ x H hH hnd _ _ _ _ _ _ hp hq

/-- Nondegeneracy of the native potential form from the actual Hessian
lower bound, uniformly on the quotient ambient. -/
theorem nondegenerate_lambdaPotentialForm_of_lowerBound {φ : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (y : LGSpace n) :
    (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  exact nondegenerate_lambdaPotentialForm_of_hessian hφ x
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl)

/-- The native Poisson error for the actual tailored maps and actual
potential primitive, with a constant independent of `β,s,y` and `K`. -/
theorem tailoringFamily_exists_uniform_native_planePairing_error (I : ToricInput n)
    {φ : RealSpace n → ℝ} {c : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β s : ℝ), s ∈ Icc (0 : ℝ) 1 →
      ∀ (y : LGSpace n)
        (hnd : (lgManifold n).Nondegenerate
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      ‖(lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd -
        (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringOriginal I β) y hnd‖ ≤
          C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I y.1 - β) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := tailoringFamily_exists_uniform_coverPlanePairing_error I hc
  refine ⟨C, hC, fun β s hs y hnd => ?_⟩
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [planePairing_lambdaPotentialForm_eq_cover hφ x
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
      (contMDiff_tailoringFamily_lgManifold I β s),
    planePairing_lambdaPotentialForm_eq_cover hφ x
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
      (contMDiff_tailoringOriginal_lgManifold I β)]
  exact hb β s hs x _ (hlower (WithLp.toLp 2 x.1))

end FsFltz
