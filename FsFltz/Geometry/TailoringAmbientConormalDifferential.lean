import FsFltz.Geometry.TailoringConormalLiouville
import FsFltz.Geometry.TailoringAmbientRayPositivity

/-!
# Actual conormal differential and ambient field beyond the level-one fiber

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1776–1818,
especially the ambient cone equation at lines 1791–1805. The norm condition
refers to the literal normalized endpoint function, including its
small-monomial cutoff. No invariance or hitting map is supplied as input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- At every actual endpoint value of norm at least one, the auxiliary
small-monomial cutoff has already reached its constant value one. -/
theorem tailoringEta_eq_one_of_one_le_norm_endpoint (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hy : 1 ≤ ‖tailoringFamily I β 1 y‖) :
    tailoringEta I β y = 1 := by
  by_contra hη
  exact (not_lt_of_ge hy) (norm_tailoringFamily_lt_one_of_eta_ne_one I β
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) y hη)

/-- Flatness at the maximum of the auxiliary cutoff identifies the actual
endpoint differential with the defining equation wherever the actual
auxiliary cutoff is one. -/
theorem fderiv_tailoringFamily_one_eq_equation_of_eta_eq_one
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringEta I β (lgCover x) = 1) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x =
      fderiv ℝ (fun z => tailoringEquation I β (lgCover z)) x := by
  have hη := hx
  let η : TangentCoordinates n → ℝ := fun z => tailoringEta I β (lgCover z)
  have hηeq : η = fun z => tailoringEta I β (z.1, 0) := by
    funext z
    simp only [η, tailoringEta_eq, lgCover]
  have hηdiff : DifferentiableAt ℝ η x := by
    rw [hηeq]
    exact ((contDiff_tailoringEta_real I β).comp contDiff_fst).differentiable (by simp) x
  have hηzero : fderiv ℝ η x = 0 := by
    apply IsLocalMax.fderiv_eq_zero
    exact Eventually.of_forall fun z => by
      change tailoringEta I β (lgCover z) ≤ tailoringEta I β (lgCover x)
      rw [hη]
      exact tailoringEta_le_one I β (lgCover z)
  have hηF := Complex.ofRealCLM.hasFDerivAt.comp x hηdiff.hasFDerivAt
  rw [hηzero, ContinuousLinearMap.comp_zero] at hηF
  let F := fun z => tailoringEquation I β (lgCover z)
  let O := fun z => tailoringOriginal I β (lgCover z)
  let C := fun z => tailoringCorrection I β (lgCover z)
  have hcut (v : Lattice n) : DifferentiableAt ℝ
      (fun z : TangentCoordinates n => (tailoringCutoff I β v z.1 : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      (((tailoringCutoff_contDiff I β v).comp contDiff_fst).differentiable (by simp) x)
  have hF : DifferentiableAt ℝ F x :=
    (hcut 0).neg.add
      (DifferentiableAt.fun_sum (u := I.vertices) (fun v _ =>
        (hcut v).mul
          (hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x).differentiableAt))
  have hO : DifferentiableAt ℝ O x :=
    (contDiff_tailoringOriginal_cover I β).differentiable (by simp) x
  have hCeq : C = fun z => 1 + F z - O z := by
    funext z
    dsimp [C, F, O, tailoringCorrection, tailoringEquation, tailoringOriginal, lgCover]
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hC : DifferentiableAt ℝ C x := by
    rw [hCeq]
    exact (hF.const_add 1).sub hO
  have hfamily : (fun z => tailoringFamily I β 1 (lgCover z)) =
      fun z => O z + (η z : ℂ) * C z := by
    funext z
    simp only [tailoringFamily, one_mul, O, η, C, tailoringCorrection]
  have hequation : F = fun z => O z + C z - 1 := by
    rw [hCeq]
    funext z
    ring
  change fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x = fderiv ℝ F x
  rw [hfamily, hequation]
  change fderiv ℝ (O + (Complex.ofRealCLM ∘ η) * C) x =
    fderiv ℝ (fun z => (O + C) z - 1) x
  rw [(hO.hasFDerivAt.add (hηF.mul hC.hasFDerivAt)).fderiv,
    ((hO.hasFDerivAt.add hC.hasFDerivAt).sub_const 1).fderiv]
  change fderiv ℝ O x +
    ((tailoringEta I β (lgCover x) : ℂ) • fderiv ℝ C x + C x • 0) = _
  rw [hη, Complex.ofReal_one, one_smul]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, zero_apply, smul_eq_mul, mul_zero, add_zero]

/-- The full transition-cutoff radial differential and imaginary angular
block at actual conormal points with auxiliary cutoff one, without a
level-one equation or a norm restriction. -/
theorem fderiv_tailoringFamily_one_conormal_of_eta_eq_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringEta I β (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (w : TangentCoordinates n) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w =
      (fderiv ℝ (tailoringRadialFunction I β) x.1 w.1 : ℂ) +
        Complex.I * ((∑ j, tailoringConormalVector I β x.1 j * w.2 j : ℝ) : ℂ) := by
  rw [fderiv_tailoringFamily_one_eq_equation_of_eta_eq_one I β x hx,
    fderiv_tailoringEquation_cover, add_apply, ContinuousLinearMap.comp_apply]
  change tailoringLeadingDifferential I β (lgCover x) w +
    tailoringRadialError I β (lgCover x) w.1 = _
  rw [tailoringLeadingDifferential_apply_eq_normal,
    tailoringRetainedNormal_eq_conormalVector I β σ (lgCover x) hθ hoff,
    tailoringRadialError_conormal_apply I β σ (lgCover x) hθ hoff,
    fderiv_tailoringRadialFunction_apply]
  simp only [lgCover, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hs : (∑ j, (tailoringConormalVector I β x.1 j : ℂ) * (w.1 j : ℂ)) =
      ((∑ v ∈ I.vertices, tailoringCutoff I β v x.1 *
        Real.exp (pairing v x.1 - β) * pairing v w.1 : ℝ) : ℂ) := by
    norm_cast
    exact tailoringConormalVector_pairing I β x.1 w.1
  rw [hs]
  have hi : (∑ j, (tailoringConormalVector I β x.1 j : ℂ) *
      (Complex.I * (w.2 j : ℂ))) =
      ∑ j, Complex.I * ((tailoringConormalVector I β x.1 j : ℂ) * (w.2 j : ℂ)) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hi]
  push_cast
  ring

/-- The imaginary Hamiltonian of the actual endpoint has only a radial
inverse-Hessian block on the actual auxiliary-cutoff-one conormal region. -/
theorem coverHamiltonianVector_im_conormal_of_eta_eq_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringEta I β (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    coverHamiltonianVector H
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) =
      ((EuclideanSpace.equiv (Fin n) ℝ)
        (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0) := by
  have hrad : coverCovectorVector
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x))
      (logCoverRadialLift n) = 0 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_coverCovectorVector]
    change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
      ((EuclideanSpace.equiv (Fin n) ℝ) w, 0)).im = inner ℝ 0 w
    rw [fderiv_tailoringFamily_one_conormal_of_eta_eq_one I β σ x hx hθ hoff]
    simp
  have hang : coverCovectorVector
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x))
      (logCoverAngularLift n) = WithLp.toLp 2 (tailoringConormalVector I β x.1) := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_coverCovectorVector]
    change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
      (0, (EuclideanSpace.equiv (Fin n) ℝ) w)).im = _
    rw [fderiv_tailoringFamily_one_conormal_of_eta_eq_one I β σ x hx hθ hoff]
    simp [PiLp.inner_apply, mul_comm]
  simp only [coverHamiltonianVector, hrad, hang, map_zero, sub_zero]
  rfl

/-- The actual endpoint is real on the auxiliary-cutoff-one conormal
region, without requiring the level-one equation. -/
theorem tailoringFamily_one_eq_radial_of_eta_eq_one_conormal
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (y : LGSpace n)
    (hy : tailoringEta I β y = 1) (hθ : y.2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v y.1 = 0) :
    tailoringFamily I β 1 y = (tailoringRadialFunction I β y.1 : ℂ) := by
  have h := tailoringFamily_one_sub_one_of_eta_eq_one I β y
    hy
  rw [tailoringEquation_eq_radial_of_offCone I β σ y hθ hoff] at h
  rw [Complex.ofReal_sub, Complex.ofReal_one] at h
  linear_combination h

/-- The actual ambient rank-two Liouville field has zero angular velocity
and the source's inverse-Hessian radial correction throughout this region.
The Hessian and Euler assumptions are literal pointwise analytic identities. -/
theorem native_liouvilleVector_rankTwo_tailoring_conormal_of_eta_eq_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringEta I β (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (K : ℝ)
    (hden : 1 + K * coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ≠ 0) :
    let π := coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
    (lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (lgCover x) =
      lgCoverTangent x
        (x.1 + (K / (1 + K * π) *
          ((tailoringFamily I β 1 (lgCover x)).re / 2 -
            fderiv ℝ (tailoringRadialFunction I β) x.1 x.1)) •
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
  let f := tailoringFamily I β 1
  have hf := contMDiff_tailoringFamily_lgManifold I β 1
  let hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ x H hH
  have hπ := planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd hf
  have hden' : 1 + K * (lgManifold n).planePairing (lambdaPotentialForm φ) f
      (lgCover x) hnd ≠ 0 := by
    rw [hπ]
    exact hden
  have hZ : (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
    (lgManifold n).liouvilleVector_eq _ _ hnd
      (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)
  have hq : (lgManifold n).hamiltonianVector
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
      (Complex.imCLM.comp (complexDifferential (lgManifold n) f (lgCover x))) =
      lgCoverTangent x ((EuclideanSpace.equiv (Fin n) ℝ)
        (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0) := by
    rw [← lgCoverTangent_coverHamiltonianVector hφ x H hH hnd,
      ContinuousLinearMap.comp_assoc, ← fderiv_complex_lgCover hf,
      coverHamiltonianVector_im_conormal_of_eta_eq_one I β σ x hx hθ hoff H]
  have hdf : complexDifferential (lgManifold n) f (lgCover x)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
      (fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 : ℂ) := by
    rw [hZ]
    change ((complexDifferential (lgManifold n) f (lgCover x)).comp
      (lgCoverTangent x)) (x.1, 0) = _
    rw [← fderiv_complex_lgCover hf,
      fderiv_tailoringFamily_one_conormal_of_eta_eq_one I β σ x hx hθ hoff]
    simp
  have hreal := tailoringFamily_one_eq_radial_of_eta_eq_one_conormal I β σ
    (lgCover x) hx hθ hoff
  have him : (f (lgCover x)).im = 0 := by
    change (tailoringFamily I β 1 (lgCover x)).im = 0
    rw [hreal]
    simp
  have hdre : (Complex.reCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) =
      fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 := by
    exact congrArg Complex.re hdf
  have hdim : (Complex.imCLM.comp (complexDifferential (lgManifold n) f (lgCover x)))
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) = 0 := by
    exact congrArg Complex.im hdf
  dsimp only
  rw [(lgManifold n).liouvilleVector_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
      hf K (lgCover x) hnd hden',
    (lgManifold n).rankTwoLiouvilleVector_formula,
    hdre, hdim, him, hZ, hq]
  change lgCoverTangent x (x.1, 0) +
    (K / (1 + K * (lgManifold n).planePairing (lambdaPotentialForm φ) f
      (lgCover x) hnd)) •
    ((0 - 0 / 2) • _ +
      ((f (lgCover x)).re / 2 - fderiv ℝ (tailoringRadialFunction I β) x.1 x.1) •
        lgCoverTangent x ((EuclideanSpace.equiv (Fin n) ℝ)
          (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0)) = _
  rw [hπ]
  simp only [zero_div, sub_self, zero_smul, zero_add, ← map_smul, ← map_add]
  congr 1
  ext <;> simp [smul_smul, f]

/-- The actual Legendre derivative of the updated ambient field has zero
angle block and its stated momentum correction remains in the face span.
This is pointwise tangency, not preservation of the positive cone by a flow. -/
theorem native_legendre_rankTwo_tailoring_conormal_mem_span_of_eta_eq_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringEta I β (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hp : coordinateGradient φ x.1 ∈ Submodule.span ℝ σ) (K : ℝ)
    (hden : 1 + K * coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ≠ 0) :
    let π := coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
    let κ := K / (1 + K * π) *
      ((tailoringFamily I β 1 (lgCover x)).re / 2 -
        fderiv ℝ (tailoringRadialFunction I β) x.1 x.1)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (legendreMap (coordinateGradient φ)) (lgCover x)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (lgCover x)) =
      cotangentCoverTangent (x.2, coordinateGradient φ x.1)
        (0, coordinateGradient φ x.1 + κ • tailoringConormalVector I β x.1) ∧
      coordinateGradient φ x.1 + κ • tailoringConormalVector I β x.1 ∈
        Submodule.span ℝ σ := by
  dsimp only
  constructor
  · rw [native_liouvilleVector_rankTwo_tailoring_conormal_of_eta_eq_one I β σ x hx hθ hoff
      hφ H hH hEuler K hden,
      legendreMap_lgCoverTangent (contDiff_coordinateGradient hφ)]
    congr 1
    refine Prod.ext rfl ?_
    rw [map_add, map_smul, hEuler, coordinateHessian_eq_euclideanHessian hφ]
    change coordinateGradient φ x.1 + _ • (EuclideanSpace.equiv (Fin n) ℝ)
      (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
        (WithLp.toLp 2 x.1) (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))) = _
    rw [hH, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · exact Submodule.add_mem _ hp
      (Submodule.smul_mem _ _ (tailoringConormalVector_mem_span I β σ x.1 hoff))

theorem fderiv_tailoringFamily_one_eq_equation_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x =
      fderiv ℝ (fun z => tailoringEquation I β (lgCover z)) x := by
  exact fderiv_tailoringFamily_one_eq_equation_of_eta_eq_one I β
    x (tailoringEta_eq_one_of_one_le_norm_endpoint I β (lgCover x) hx)

theorem fderiv_tailoringFamily_one_conormal_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (w : TangentCoordinates n) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w =
      (fderiv ℝ (tailoringRadialFunction I β) x.1 w.1 : ℂ) +
        Complex.I * ((∑ j, tailoringConormalVector I β x.1 j * w.2 j : ℝ) : ℂ) := by
  exact fderiv_tailoringFamily_one_conormal_of_eta_eq_one I β σ
    x (tailoringEta_eq_one_of_one_le_norm_endpoint I β (lgCover x) hx) hθ hoff w

theorem coverHamiltonianVector_im_conormal_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    coverHamiltonianVector H
      (Complex.imCLM.comp (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) =
      ((EuclideanSpace.equiv (Fin n) ℝ)
        (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0) := by
  exact coverHamiltonianVector_im_conormal_of_eta_eq_one I β σ
    x (tailoringEta_eq_one_of_one_le_norm_endpoint I β (lgCover x) hx) hθ hoff H

theorem tailoringFamily_one_eq_radial_of_norm_ge_one_conormal
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (y : LGSpace n)
    (hy : 1 ≤ ‖tailoringFamily I β 1 y‖) (hθ : y.2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v y.1 = 0) :
    tailoringFamily I β 1 y = (tailoringRadialFunction I β y.1 : ℂ) := by
  exact tailoringFamily_one_eq_radial_of_eta_eq_one_conormal I β σ
    y (tailoringEta_eq_one_of_one_le_norm_endpoint I β y hy) hθ hoff

theorem native_liouvilleVector_rankTwo_tailoring_conormal
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (K : ℝ)
    (hden : 1 + K * coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ≠ 0) :
    let π := coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
    (lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (lgCover x) =
      lgCoverTangent x
        (x.1 + (K / (1 + K * π) *
          ((tailoringFamily I β 1 (lgCover x)).re / 2 -
            fderiv ℝ (tailoringRadialFunction I β) x.1 x.1)) •
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
  exact native_liouvilleVector_rankTwo_tailoring_conormal_of_eta_eq_one I β σ
    x (tailoringEta_eq_one_of_one_le_norm_endpoint I β (lgCover x) hx) hθ hoff
    hφ H hH hEuler K hden

theorem native_legendre_rankTwo_tailoring_conormal_mem_span
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hp : coordinateGradient φ x.1 ∈ σ) (K : ℝ)
    (hden : 1 + K * coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ≠ 0) :
    let π := coverPlanePairing H
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
    let κ := K / (1 + K * π) *
      ((tailoringFamily I β 1 (lgCover x)).re / 2 -
        fderiv ℝ (tailoringRadialFunction I β) x.1 x.1)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      (legendreMap (coordinateGradient φ)) (lgCover x)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (lgCover x)) =
      cotangentCoverTangent (x.2, coordinateGradient φ x.1)
        (0, coordinateGradient φ x.1 + κ • tailoringConormalVector I β x.1) ∧
      coordinateGradient φ x.1 + κ • tailoringConormalVector I β x.1 ∈
        Submodule.span ℝ σ := by
  exact native_legendre_rankTwo_tailoring_conormal_mem_span_of_eta_eq_one I β σ
    x (tailoringEta_eq_one_of_one_le_norm_endpoint I β (lgCover x) hx) hθ hoff
    hφ H hH hEuler (Submodule.subset_span hp) K hden

end FsFltz
