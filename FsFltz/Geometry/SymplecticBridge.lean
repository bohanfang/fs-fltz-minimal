import FsFltz.Geometry.QuotientFormBridge
import FsFltz.Geometry.ExteriorDerivative
import FsFltz.Geometry.ToricSmoothForms
import FsFltz.AnalyticGeometry

/-!
# Exterior differentiation of the prescribed quotient primitive

The calculations concern the actual quotient forms of `sec:data`, lines 74–86
of `geoemtric-part-fsf.tex`, and the foundational bridge required by
`sec:lean`, lines 805–814. They assert no completeness or comparison existence.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold

/-- The standard primitive on the real logarithmic cover. -/
def coverLambda0 {n : ℕ} (x : TangentCoordinates n) :
    TangentCoordinates n [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
    (∑ j, x.1 j • (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)))

theorem coverLambda0_apply {n : ℕ} (x : TangentCoordinates n)
    (q : Fin 1 → TangentCoordinates n) :
    coverLambda0 x q = ∑ j, x.1 j * (q 0).2 j := by
  simp [coverLambda0]

theorem contDiff_coverLambda0 (n : ℕ) :
    ContDiff ℝ ∞ (coverLambda0 (n := n)) := by
  apply (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := TangentCoordinates n) (F := ℝ) (0 : Fin 1)).contDiff.comp
  exact ContDiff.sum (fun j _ =>
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))).contDiff.smul contDiff_const)

/-- Differentiating the cover primitive gives the canonical two-form. -/
theorem extDeriv_coverLambda0 {n : ℕ} (x q r : TangentCoordinates n) :
    extDeriv coverLambda0 x ![q, r] = omega0Coordinates q r := by
  let A (v : TangentCoordinates n) : TangentCoordinates n →L[ℝ] ℝ :=
    ∑ j, v.2 j • (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))
  have hf (vs : Fin 1 → TangentCoordinates n) :
      (fun z => coverLambda0 z vs) = A (vs 0) := by
    funext z
    simp [coverLambda0_apply, A, mul_comm]
  have hd (vs : Fin 1 → TangentCoordinates n) :
      fderiv ℝ (fun z => coverLambda0 z vs) x = A (vs 0) := by
    rw [hf, (A (vs 0)).hasFDerivAt.fderiv]
  rw [extDeriv_apply ((contDiff_coverLambda0 n).differentiable (by simp) x)]
  simp [Fin.sum_univ_two, hd, A, Fin.removeNth, omega0Coordinates,
    Finset.sum_add_distrib, mul_comm, sub_eq_add_neg]

/-- Literal planar primitive `(x dy - y dx)/2`, represented by a native form. -/
def planeLambda (z : ℂ) : ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
    ((1 / 2 : ℝ) • (z.re • Complex.imCLM - z.im • Complex.reCLM))

theorem planeLambda_apply (z : ℂ) (q : Fin 1 → ℂ) :
    planeLambda z q = (1 / 2 : ℝ) * (z.re * (q 0).im - z.im * (q 0).re) := by
  simp [planeLambda]

theorem contDiff_planeLambda : ContDiff ℝ ∞ planeLambda := by
  apply (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).contDiff.comp
  exact (Complex.reCLM.contDiff.smul contDiff_const |>.sub
    (Complex.imCLM.contDiff.smul contDiff_const)).const_smul (1 / 2 : ℝ)

/-- The exterior derivative of the prescribed planar primitive is `dx ∧ dy`.
This is an actual Fréchet calculation, rather than an assumed pullback rule. -/
theorem extDeriv_planeLambda (z q r : ℂ) :
    extDeriv planeLambda z ![q, r] = q.re * r.im - q.im * r.re := by
  let A (v : ℂ) : ℂ →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (v.im • Complex.reCLM - v.re • Complex.imCLM)
  have hf (vs : Fin 1 → ℂ) : (fun z => planeLambda z vs) = A (vs 0) := by
    funext z
    simp [planeLambda_apply, A]
    ring
  have hd (vs : Fin 1 → ℂ) : fderiv ℝ (fun z => planeLambda z vs) z = A (vs 0) := by
    rw [hf, (A (vs 0)).hasFDerivAt.fderiv]
  rw [extDeriv_apply (contDiff_planeLambda.differentiable (by simp) z)]
  simp [Fin.sum_univ_two, hd, A, Fin.removeNth]
  ring

/-- Smoothness of the superpotential on the full real covering space. -/
theorem contDiff_W_lgCover {n : ℕ} (I : ToricInput n) :
    ContDiff ℝ ∞ (fun z : TangentCoordinates n => W I (lgCover z)) :=
  ((contMDiff_W_lgManifold I).comp (contMDiff_lgCover n)).contDiff

theorem fderiv_W_lgCover_apply {n : ℕ} (I : ToricInput n)
    (x q : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n => W I (lgCover z)) x q =
      dW I (lgCover x) q :=
  fderiv_W_representatives_apply I x q

/-- The literal Euclidean pullback of the planar primitive by `W`. -/
def coverPlaneForm {n : ℕ} (I : ToricInput n) (x : TangentCoordinates n) :
    TangentCoordinates n [⋀^Fin 1]→L[ℝ] ℝ :=
  (planeLambda (W I (lgCover x))).compContinuousLinearMap
    (fderiv ℝ (fun z : TangentCoordinates n => W I (lgCover z)) x)

theorem coverPlaneForm_apply {n : ℕ} (I : ToricInput n)
    (x : TangentCoordinates n) (q : Fin 1 → TangentCoordinates n) :
    coverPlaneForm I x q = (1 / 2 : ℝ) *
      ((W I (lgCover x)).re * (dW I (lgCover x) (q 0)).im -
        (W I (lgCover x)).im * (dW I (lgCover x) (q 0)).re) := by
  simp only [coverPlaneForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    planeLambda_apply, Function.comp_apply]
  rw [fderiv_W_lgCover_apply]

theorem differentiableAt_coverPlaneForm {n : ℕ} (I : ToricInput n)
    (x : TangentCoordinates n) : DifferentiableAt ℝ (coverPlaneForm I) x := by
  apply ((contDiff_planeLambda.comp (contDiff_W_lgCover I)).differentiable
    (by simp) x).continuousAlternatingMapCompContinuousLinearMap
  exact ((contDiff_W_lgCover I).fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x

/-- Actual exterior differentiation of the pulled-back planar primitive. -/
theorem extDeriv_coverPlaneForm {n : ℕ} (I : ToricInput n)
    (x q r : TangentCoordinates n) :
    extDeriv (coverPlaneForm I) x ![q, r] =
      (dW I (lgCover x) q).re * (dW I (lgCover x) r).im -
        (dW I (lgCover x) q).im * (dW I (lgCover x) r).re := by
  have h := extDeriv_pullback («ω» := planeLambda)
    (f := fun z : TangentCoordinates n => W I (lgCover z)) (x := x)
    (contDiff_planeLambda.differentiable (by simp) (W I (lgCover x)))
    (contDiff_W_lgCover I).contDiffAt (by simp)
  change extDeriv (coverPlaneForm I) x = _ at h
  rw [h]
  have hv : (fderiv ℝ (fun z => W I (lgCover z)) x) ∘ ![q, r] =
      ![fderiv ℝ (fun z => W I (lgCover z)) x q,
        fderiv ℝ (fun z => W I (lgCover z)) x r] := by
    funext i
    fin_cases i <;> rfl
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hv,
    extDeriv_planeLambda, fderiv_W_lgCover_apply,
    fderiv_W_lgCover_apply]

/-- The actual primitive pulled back along the quotient cover has a single
global coefficient expression, which can therefore be differentiated. -/
theorem lambdaKForm_cover_coefficients {n : ℕ} (I : ToricInput n) (K : ℝ) :
    (fun x : TangentCoordinates n => (lambdaKForm I K (lgCover x)).compContinuousLinearMap
      (lgCoverTangent x)) = fun x => coverLambda0 x + K • coverPlaneForm I x := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro vs
  have hv : vs = fun _ => vs 0 := funext (fun i => congrArg vs (Subsingleton.elim i 0))
  rw [hv]
  change evalOne (lambdaKForm I K) (lgCover x) (lgCoverTangent x (vs 0)) = _
  rw [lambdaKForm_lgCover]
  simp [coverLambda0_apply, coverPlaneForm_apply, lambdaKCoordinates,
    lambda0Coordinates, lgCover]
  ring

/-- Differentiation of the single global expression on the real cover. -/
theorem extDeriv_coverLambdaK {n : ℕ} (I : ToricInput n) (K : ℝ)
    (x q r : TangentCoordinates n) :
    extDeriv (fun z => coverLambda0 z + K • coverPlaneForm I z) x ![q, r] =
      omegaKCoordinates I K (lgCover x) q r := by
  erw [extDeriv_fun_add ((contDiff_coverLambda0 n).differentiable (by simp) x)
    ((differentiableAt_coverPlaneForm I x).const_smul K), extDeriv_fun_smul]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, extDeriv_coverLambda0, extDeriv_coverPlaneForm, omegaKCoordinates]
  ring

/-- The actual quotient exterior derivative has the source's prescribed
coordinate formula on all cover tangent vectors. -/
theorem exteriorDerivative_lambdaKForm_lgCover {n : ℕ} (I : ToricInput n) (K : ℝ)
    (x q r : TangentCoordinates n) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaKForm I K)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x r) =
        omegaKCoordinates I K (lgCover x) q r := by
  have h := (lgManifold n).exteriorDerivative_pullback_from_normedSpace
    lgCover (contMDiff_lgCover n) (lambdaKForm I K) (isSmoothForm_lambdaKForm I K) x
  change extDeriv (fun z => (lambdaKForm I K (lgCover z)).compContinuousLinearMap
    (lgCoverTangent z)) x =
    ((lgManifold n).exteriorDerivative (lambdaKForm I K) (lgCover x)).compContinuousLinearMap
      (lgCoverTangent x) at h
  rw [lambdaKForm_cover_coefficients] at h
  have hv : (lgCoverTangent x) ∘ ![q, r] =
      ![lgCoverTangent x q, lgCoverTangent x r] := by
    funext i
    fin_cases i <;> rfl
  have he := congrArg (fun eta => eta ![q, r]) h.symm
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hv,
    extDeriv_coverLambdaK] at he
  exact he

/-- Every point of the quotient manifold has a representative in the cover. -/
theorem lgCover_surjective (n : ℕ) :
    Function.Surjective (lgCover (n := n)) := by
  intro y
  obtain ⟨theta, htheta⟩ := angleQuotient_surjective y.2
  exact ⟨(y.1, theta), Prod.ext rfl htheta⟩

/-- The coordinate nondegeneracy calculation tests every geometric tangent
vector because the actual quotient-cover derivative is surjective. -/
theorem nondegenerate_exteriorDerivative_lambdaKForm_at_cover {n : ℕ}
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) (x : TangentCoordinates n) :
    (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative (lambdaKForm I K))
      (lgCover x) := by
  intro v hv
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  have hq : q = 0 := omegaKCoordinates_nondegenerate I (lgCover x) hK q (fun r => by
    rw [← exteriorDerivative_lambdaKForm_lgCover]
    exact hv (lgCoverTangent x r))
  rw [hq, map_zero]

/-- Pointwise nondegeneracy of the actual exterior derivative for every
nonnegative `K`, including the zero-dimensional linear-algebra case. -/
theorem nondegenerate_exteriorDerivative_lambdaKForm {n : ℕ}
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) (y : (lgManifold n).Point) :
    (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative (lambdaKForm I K)) y := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  exact nondegenerate_exteriorDerivative_lambdaKForm_at_cover I hK x

/-- The prescribed primitive is actually exact symplectic for all `K ≥ 0`.
Smoothness and closedness follow from the proved intrinsic exterior calculus;
nondegeneracy follows from the explicit source positivity calculation. -/
theorem isSymplecticOn_exteriorDerivative_lambdaKForm {n : ℕ}
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) :
    (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative (lambdaKForm I K))
      Set.univ := by
  apply ((lgManifold n).isSymplecticOn_exteriorDerivative_iff
    (lambdaKForm I K) (isSmoothForm_lambdaKForm I K) Set.univ).mpr
  exact fun y _ => nondegenerate_exteriorDerivative_lambdaKForm I hK y

/-- The cotangent-cover primitive is the logarithmic-cover primitive pulled
back by the linear interchange of angular and momentum coordinates. -/
def coverLambdaCan {n : ℕ} (x : TangentCoordinates n) :
    TangentCoordinates n [⋀^Fin 1]→L[ℝ] ℝ :=
  (coverLambda0 x.swap).compContinuousLinearMap
    (ContinuousLinearEquiv.prodComm ℝ (RealSpace n) (RealSpace n)).toContinuousLinearMap

theorem coverLambdaCan_apply {n : ℕ} (x : TangentCoordinates n)
    (q : Fin 1 → TangentCoordinates n) :
    coverLambdaCan x q = ∑ j, x.2 j * (q 0).1 j := by
  simp [coverLambdaCan, coverLambda0_apply]

/-- The canonical cotangent derivative is `sum dp_j ∧ d theta_j`, in the
source's `(theta,p)` coordinate order (`sec:data`, lines 92–97). -/
theorem extDeriv_coverLambdaCan {n : ℕ} (x q r : TangentCoordinates n) :
    extDeriv coverLambdaCan x ![q, r] = omega0Coordinates q.swap r.swap := by
  let S := ContinuousLinearEquiv.prodComm ℝ (RealSpace n) (RealSpace n)
  have h := extDeriv_pullback («ω» := coverLambda0) (f := S) (x := x) (r := ∞)
    ((contDiff_coverLambda0 n).differentiable (by simp) (S x))
    S.contDiff.contDiffAt (by simp)
  simp only [S.fderiv] at h
  change extDeriv coverLambdaCan x =
    (extDeriv coverLambda0 x.swap).compContinuousLinearMap S.toContinuousLinearMap at h
  rw [h, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hv : S.toContinuousLinearMap ∘ ![q, r] = ![q.swap, r.swap] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, extDeriv_coverLambda0]

theorem lambdaCanForm_cover_coefficients (n : ℕ) :
    (fun x : TangentCoordinates n => (lambdaCanForm n (cotangentCover x)).compContinuousLinearMap
      (cotangentCoverTangent x)) = coverLambdaCan := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro vs
  have hv : vs = fun _ => vs 0 := funext (fun i => congrArg vs (Subsingleton.elim i 0))
  rw [hv]
  change evalOne (lambdaCanForm n) (cotangentCover x) (cotangentCoverTangent x (vs 0)) = _
  rw [lambdaCanForm_cotangentCover]
  simp [coverLambdaCan_apply]

/-- The actual quotient cotangent differential has exactly the canonical
coordinate expression. Smoothness is proved for the specified primitive. -/
theorem exteriorDerivative_lambdaCanForm_cotangentCover {n : ℕ}
    (x q r : TangentCoordinates n) :
    evalTwo ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) (cotangentCover x)
      (cotangentCoverTangent x q) (cotangentCoverTangent x r) =
        ∑ j, (q.2 j * r.1 j - r.2 j * q.1 j) := by
  have h := (cotangentManifold n).exteriorDerivative_pullback_from_normedSpace
    cotangentCover (contMDiff_cotangentCover n) (lambdaCanForm n) (isSmoothForm_lambdaCanForm n) x
  change extDeriv (fun z => (lambdaCanForm n (cotangentCover z)).compContinuousLinearMap
    (cotangentCoverTangent z)) x =
    ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)
      (cotangentCover x)).compContinuousLinearMap (cotangentCoverTangent x) at h
  rw [lambdaCanForm_cover_coefficients] at h
  have hv : (cotangentCoverTangent x) ∘ ![q, r] =
      ![cotangentCoverTangent x q, cotangentCoverTangent x r] := by
    funext i
    fin_cases i <;> rfl
  have he := congrArg (fun eta => eta ![q, r]) h.symm
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hv,
    extDeriv_coverLambdaCan] at he
  exact he

/-- The canonical coordinate form is nondegenerate in every rank, including
rank zero; each coordinate is detected by a standard coordinate vector. -/
theorem omega0Coordinates_nondegenerate {n : ℕ} (q : TangentCoordinates n)
    (hq : ∀ r, omega0Coordinates q r = 0) : q = 0 := by
  classical
  apply Prod.ext
  · funext j
    have h := hq (0, Pi.single j 1)
    simpa [omega0Coordinates, Pi.single_apply, mul_ite] using h
  · funext j
    have h := hq (Pi.single j 1, 0)
    simpa [omega0Coordinates, Pi.single_apply, ite_mul] using h

theorem cotangentCover_surjective (n : ℕ) :
    Function.Surjective (cotangentCover (n := n)) := by
  intro y
  obtain ⟨theta, htheta⟩ := angleQuotient_surjective y.1
  exact ⟨(theta, y.2), Prod.ext htheta rfl⟩

theorem nondegenerate_exteriorDerivative_lambdaCanForm_at_cover {n : ℕ}
    (x : TangentCoordinates n) :
    (cotangentManifold n).Nondegenerate
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) (cotangentCover x) := by
  intro v hv
  obtain ⟨q, rfl⟩ := (cotangentCoverTangent_bijective x).2 v
  have hq : q.swap = 0 := omega0Coordinates_nondegenerate q.swap (fun r => by
    have h := hv (cotangentCoverTangent x r.swap)
    rw [exteriorDerivative_lambdaCanForm_cotangentCover] at h
    exact h)
  have hq' : q = 0 := by
    simpa using congrArg Prod.swap hq
  rw [hq', map_zero]

/-- Pointwise nondegeneracy of the actual cotangent differential, without
an input tuple or positive-dimensional restriction. -/
theorem nondegenerate_exteriorDerivative_lambdaCanForm {n : ℕ}
    (y : (cotangentManifold n).Point) :
    (cotangentManifold n).Nondegenerate
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) y := by
  obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
  exact nondegenerate_exteriorDerivative_lambdaCanForm_at_cover x

/-- The specified cotangent primitive is actually exact symplectic; the
derivative's smoothness and closedness follow from intrinsic exterior calculus.
Source: `sec:data`, lines 92–97, and conventions, lines 119–130. -/
theorem isSymplecticOn_exteriorDerivative_lambdaCanForm (n : ℕ) :
    (cotangentManifold n).IsSymplecticOn
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) Set.univ := by
  apply ((cotangentManifold n).isSymplecticOn_exteriorDerivative_iff
    (lambdaCanForm n) (isSmoothForm_lambdaCanForm n) Set.univ).mpr
  exact fun y _ => nondegenerate_exteriorDerivative_lambdaCanForm y

end FsFltz.Geometry
