import FsFltz.Geometry.TailoringConormalDifferential
import FsFltz.Geometry.PotentialLiouvilleRadial

/-!
# The actual native intrinsic Liouville direction on conormal pieces

Source: `geometric-part-fsf-proof.tex`, `eq:intrinsiccone`, lines 1637–1647.
The coordinate calculation below is transported to the primitive-determined
native intrinsic field by the proved symplectic projection theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

theorem coverCovectorVector_im_radial_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0) :
    coverCovectorVector
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x))
      (logCoverRadialLift n) = 0 := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_coverCovectorVector]
  change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
    ((EuclideanSpace.equiv (Fin n) ℝ) w, 0)).im = inner ℝ 0 w
  rw [fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff]
  simp

theorem coverCovectorVector_re_angular_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0) :
    coverCovectorVector
      (Complex.reCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x))
      (logCoverAngularLift n) = 0 := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_coverCovectorVector]
  change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
    (0, (EuclideanSpace.equiv (Fin n) ℝ) w)).re = inner ℝ 0 w
  rw [fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff]
  simp

theorem coverCovectorVector_im_angular_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0) :
    coverCovectorVector
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x))
      (logCoverAngularLift n) = WithLp.toLp 2 (tailoringConormalVector I β x.1) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_coverCovectorVector]
  change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
    (0, (EuclideanSpace.equiv (Fin n) ℝ) w)).im = _
  rw [fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff]
  simp [PiLp.inner_apply, mul_comm]

theorem coverHamiltonianVector_im_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    coverHamiltonianVector H
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) =
      ((EuclideanSpace.equiv (Fin n) ℝ)
        (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0) := by
  simp only [coverHamiltonianVector,
    coverCovectorVector_im_radial_conormal I β σ x hx hθ hoff,
    coverCovectorVector_im_angular_conormal I β σ x hx hθ hoff, map_zero, sub_zero]
  rfl

/-- The actual projection has zero angular velocity and the source's
radial correction, including the nonholomorphic cutoff transition. -/
theorem coverFiberProjection_radial_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    coverFiberProjection H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
      (x.1, 0) =
      (x.1 - (fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 /
        coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) •
        ((EuclideanSpace.equiv (Fin n) ℝ)
          (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
  rw [coverFiberProjection_apply,
    fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff,
    coverHamiltonianVector_im_conormal I β σ x hx hθ hoff H]
  simp

/-- Equation `eq:intrinsiccone` evaluated on the primitive-determined
native field of an actual smooth fiber embedding. The only tangent-image
hypothesis is the ordinary regular-fiber presentation. -/
theorem native_liouvilleVector_tailoring_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (e : ℕ) (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n))
    (a : N.Point) (hpoint : j.map a = lgCover x)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (hπ : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (lgCover x) hnd ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker) :
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a) =
      lgCoverTangent x
        (x.1 - (fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 /
          coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) •
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
  have hnd' : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map a) := by
    rwa [hpoint]
  have hπ' : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (j.map a) hnd' ≠ 0 := by
    simpa only [hpoint] using hπ
  have he := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection N j
    (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) a hnd'
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    hπ' (by rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]; exact hkernel)
  have hZ : (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
    (lgManifold n).liouvilleVector_eq _ _ hnd
      (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)
  have hprojection := lgCoverTangent_coverFiberProjection hφ x H hH hnd
    (contMDiff_tailoringFamily_lgManifold I β 1) (x.1, 0)
  have hformula := coverFiberProjection_radial_conormal I β σ x hx hθ hoff H
  have hcalc : ∀ (y : LGSpace n)
      (hndy : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      y = lgCover x →
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y hndy
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) =
      lgCoverTangent x
        (x.1 - (fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 /
          coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) •
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
    intro y hndy hy
    subst y
    rw [hZ]
    exact hprojection.symm.trans (congrArg (lgCoverTangent x) hformula)
  exact he.trans (hcalc (j.map a) hnd' hpoint)

/-- The Legendre derivative of that actual field has zero angle block and
the exact momentum block `p − (a_f / π_f) G`. -/
theorem legendre_liouville_direction_tailoring_conormal
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (t : ℝ) :
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (legendreMap (coordinateGradient φ)) (lgCover x)
      (lgCoverTangent x
        (x.1 - t • ((EuclideanSpace.equiv (Fin n) ℝ)
          (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0)) =
      cotangentCoverTangent (x.2, coordinateGradient φ x.1)
        (0, coordinateGradient φ x.1 - t • tailoringConormalVector I β x.1) := by
  rw [legendreMap_lgCoverTangent (contDiff_coordinateGradient hφ)]
  congr 1
  refine Prod.ext ?_ ?_
  · rfl
  change fderiv ℝ (coordinateGradient φ) x.1
    (x.1 - t • ((EuclideanSpace.equiv (Fin n) ℝ)
      (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))))) = _
  rw [map_sub, map_smul, hEuler, coordinateHessian_eq_euclideanHessian hφ]
  change coordinateGradient φ x.1 - t • (EuclideanSpace.equiv (Fin n) ℝ)
    (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))) = _
  rw [hH, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem tailoring_conormal_momentum_direction_mem_span
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (u : RealSpace n)
    (p : RealSpace n) (hp : p ∈ σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v u = 0)
    (t : ℝ) : p - t • tailoringConormalVector I β u ∈ Submodule.span ℝ σ :=
  Submodule.sub_mem _ (Submodule.subset_span hp)
    (Submodule.smul_mem _ _ (tailoringConormalVector_mem_span I β σ u hoff))

end FsFltz
