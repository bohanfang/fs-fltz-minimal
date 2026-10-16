import FsFltz.Geometry.PotentialLiouville
import FsFltz.Analysis.HomogeneousPotential

/-!
# The adapted Liouville field on the homogeneous end

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 680–688.
The actual derivative of the quotient Legendre map transports the Hessian
form to the canonical cotangent form. Euler's identity then proves the
radial contraction equation for the literal potential primitive.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

/-- The actual quotient derivative of the Legendre map has precisely the
angular identity and the Hessian in its two coordinate blocks. -/
theorem legendreMap_lgCoverTangent {Φ : RealSpace n → RealSpace n}
    (hΦ : ContDiff ℝ ∞ Φ) (x q : TangentCoordinates n) :
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (legendreMap Φ) (lgCover x)
      (lgCoverTangent x q) =
        cotangentCoverTangent (x.2, Φ x.1) (q.2, fderiv ℝ Φ x.1 q.1) := by
  let F : TangentCoordinates n → TangentCoordinates n := fun z => (z.2, Φ z.1)
  have hF : ContDiff ℝ ∞ F := contDiff_snd.prodMk (hΦ.comp contDiff_fst)
  have hD := (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).prodMk
    (((hΦ.differentiable (by simp)) x.1).hasFDerivAt.comp x
      (hasFDerivAt_fst (𝕜 := ℝ) (p := x)))
  change HasFDerivAt F _ x at hD
  have h1 := mfderiv_comp_apply x
    ((contMDiff_legendreMap hΦ).mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x) q
  have h2 := mfderiv_comp_apply x
    ((contMDiff_cotangentCover n).mdifferentiable (by simp) (F x))
    (hF.contMDiff.mdifferentiable (by simp) x) q
  rw [mfderiv_eq_fderiv (f := F), hD.fderiv] at h2
  exact h1.symm.trans h2

/-- The exterior derivative is the literal Hessian two-form in all real
cover tangent directions. -/
theorem exteriorDerivative_lambdaPotentialForm_lgCover {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x q r : TangentCoordinates n) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x r) =
        ∑ j, ((fderiv ℝ (coordinateGradient φ) x.1 q.1) j * r.2 j -
          (fderiv ℝ (coordinateGradient φ) x.1 r.1) j * q.2 j) := by
  let L : (lgManifold n).SmoothMap (cotangentManifold n) :=
    ⟨legendreMap (coordinateGradient φ), contMDiff_legendreMap (contDiff_coordinateGradient hφ)⟩
  have hd := (lgManifold n).exteriorDerivative_pullback (cotangentManifold n) L
    (lambdaCanForm n) (isSmoothForm_lambdaCanForm n)
  change (lgManifold n).exteriorDerivative
    ((lgManifold n).pullback (cotangentManifold n) (legendreMap (coordinateGradient φ))
      (lambdaCanForm n)) = _ at hd
  rw [pullback_lambdaCanForm_legendreMap hφ] at hd
  rw [hd]
  change ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)
    (legendreMap (coordinateGradient φ) (lgCover x)))
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (legendreMap (coordinateGradient φ)) (lgCover x)
        (![lgCoverTangent x q, lgCoverTangent x r] i)) = _
  have he : (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (legendreMap (coordinateGradient φ)) (lgCover x)
        (![lgCoverTangent x q, lgCoverTangent x r] i)) =
      ![cotangentCoverTangent (x.2, coordinateGradient φ x.1)
          (q.2, fderiv ℝ (coordinateGradient φ) x.1 q.1),
        cotangentCoverTangent (x.2, coordinateGradient φ x.1)
          (r.2, fderiv ℝ (coordinateGradient φ) x.1 r.1)] := by
    ext i
    fin_cases i <;> exact legendreMap_lgCoverTangent (contDiff_coordinateGradient hφ) x _
  rw [he]
  exact exteriorDerivative_lambdaCanForm_cotangentCover
    (x.2, coordinateGradient φ x.1)
    (q.2, fderiv ℝ (coordinateGradient φ) x.1 q.1)
    (r.2, fderiv ℝ (coordinateGradient φ) x.1 r.1)

/-- Euler's Hessian identity is exactly the native radial Liouville
contraction equation, with no old-metric gradient substituted. -/
theorem liouvilleEquation_lambdaPotentialForm_radial {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1) :
    (lgManifold n).LiouvilleEquation (lambdaPotentialForm φ) (lgCover x)
      (lgCoverTangent x (x.1, 0)) := by
  intro v
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  rw [exteriorDerivative_lambdaPotentialForm_lgCover hφ,
    lambdaPotentialForm_lgCover, hEuler]
  simp

/-- Consequently the primitive-determined Liouville vector is radial at
every point where the global potential has the degree-two Euler identity. -/
theorem liouvilleVector_lambdaPotentialForm_radial {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (Φ : RealSpace n ≃ₜ RealSpace n)
    (hΦ : ∀ x, Φ x = coordinateGradient φ x) (hΨ : ContDiff ℝ ∞ Φ.symm)
    (x : TangentCoordinates n)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1) :
    (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
  (lgManifold n).liouvilleVector_eq _ _
    ((isSymplecticOn_exteriorDerivative_lambdaPotentialForm hφ Φ hΦ hΨ).2.2 _ (mem_univ _))
    (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)

/-- Literal agreement outside a ball transfers the degree-two Hessian
identity to the smooth global extension on the open homogeneous end. -/
theorem coordinateHessian_apply_self_on_homogeneous_end
    {φ φEnd : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    {u : RealSpace n} (hu : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖) :
    fderiv ℝ (coordinateGradient φ) u u = coordinateGradient φ u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu; linarith
  have hopen : IsOpen {v : RealSpace n | R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖} :=
    isOpen_lt continuous_const (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.norm
  have hfg : φ =ᶠ[𝓝 u] φEnd := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact heq v hv.le
  have hgg : coordinateGradient φ =ᶠ[𝓝 u] coordinateGradient φEnd := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with v hv
    ext j
    exact congrArg (fun D : RealSpace n →L[ℝ] ℝ => D (Pi.single j 1)) hv
  rw [hgg.fderiv_eq, hgg.eq_of_nhds]
  exact coordinateHessian_apply_self_of_homogeneous_two hhom
    (fun v hv => (hEnd v hv).differentiableAt (by simp)) hu0
    (hgg.differentiableAt_iff.mp ((contDiff_coordinateGradient hφ).differentiable (by simp) u))

/-- The actual global Liouville field is the radial field throughout its
homogeneous end. Neither the field formula nor the Euler identity is an input. -/
theorem liouvilleVector_lambdaPotentialForm_on_homogeneous_end
    {φ φEnd : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΨ : ContDiff ℝ ∞ Φ.symm) {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    (x : TangentCoordinates n) (hx : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖) :
    (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
  liouvilleVector_lambdaPotentialForm_radial hφ Φ hΦ hΨ x
    (coordinateHessian_apply_self_on_homogeneous_end hφ hEnd hhom hR heq hx)

/-- Instantiation with the constructed compatible potential gives the
source's radial Liouville end from the finite toric input alone. -/
theorem _root_.FsFltz.ToricInput.exists_adapted_radial_liouville_end (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ ∞ φ ∧
      (lgManifold n).IsSymplecticOn
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) univ ∧
      ∃ R > 0, (∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
        ∀ x : TangentCoordinates n, R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ →
          (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
            lgCoverTangent x (x.1, 0) := by
  obtain ⟨φEnd, φ, hstrong, _, _, hφs, _, _, ⟨R, hR, heq⟩,
    _, Φ, _, _, _, _, hΦ, _, hΦinv⟩ := I.exists_compatiblePotential_with_legendre
  refine ⟨φEnd, φ, hstrong, hφs,
    isSymplecticOn_exteriorDerivative_lambdaPotentialForm hφs Φ hΦ hΦinv, R, hR, heq, ?_⟩
  exact liouvilleVector_lambdaPotentialForm_on_homogeneous_end hφs hstrong.smooth
    hstrong.homogeneous Φ hΦ hΦinv hR heq

end FsFltz.Geometry
