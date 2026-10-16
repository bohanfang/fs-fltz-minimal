import FsFltz.Analysis.TailoringSupport
import FsFltz.Analysis.InverseMetricNorm

/-!
# Quantitative Poisson errors for the literal tailoring family

Source: `geometric-part-fsf-proof.tex`, `eq:C1`, lines 1107–1114;
`eq:rankerror`, lines 1134–1140; `lem:tailoredpositivity`, lines 1142–1180.
The differential vectors below are the Riesz representatives of the actual
logarithmic-cover differentials. The inverse metric is the actual Hessian
inverse. The bilinear estimate is used immediately for this family.
-/

noncomputable section

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- The radial Euclidean slice of logarithmic covering coordinates. -/
def logCoverRadialLift (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n :=
  (ContinuousLinearMap.inl ℝ (RealSpace n) (RealSpace n)).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

/-- The angular Euclidean slice of logarithmic covering coordinates. -/
def logCoverAngularLift (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n :=
  (ContinuousLinearMap.inr ℝ (RealSpace n) (RealSpace n)).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

/-- The Euclidean vector representing a covector restricted to a specified
Euclidean slice. This is the Riesz inverse, rather than extra metric data. -/
def coverCovectorVector (p : TangentCoordinates n →L[ℝ] ℝ)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
    EuclideanSpace ℝ (Fin n) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (p.comp e)

theorem inner_coverCovectorVector (p : TangentCoordinates n →L[ℝ] ℝ)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (coverCovectorVector p e) v = p (e v) :=
  InnerProductSpace.toDual_symm_apply

theorem coverCovectorVector_sub (p q : TangentCoordinates n →L[ℝ] ℝ)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
    coverCovectorVector (p - q) e = coverCovectorVector p e - coverCovectorVector q e := by
  simp only [coverCovectorVector, ContinuousLinearMap.sub_comp, map_sub]

theorem norm_coverCovectorVector_le (p : TangentCoordinates n →L[ℝ] ℝ)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
    ‖coverCovectorVector p e‖ ≤ ‖p‖ * ‖e‖ := by
  rw [coverCovectorVector, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Reconstruction of any actual covector from its two Euclidean slices. -/
theorem coverCovectorVector_reconstruction (p : TangentCoordinates n →L[ℝ] ℝ)
    (v : TangentCoordinates n) :
    p v = inner ℝ (coverCovectorVector p (logCoverRadialLift n)) (WithLp.toLp 2 v.1) +
      inner ℝ (coverCovectorVector p (logCoverAngularLift n)) (WithLp.toLp 2 v.2) := by
  rw [inner_coverCovectorVector, inner_coverCovectorVector]
  change p v = p (v.1, 0) + p (0, v.2)
  rw [← map_add]
  simp

/-- The inverse-Hessian bilinear Poisson pairing in logarithmic coordinates.
The native Hamiltonian bridge identifies this with `rankTwoPairing`. -/
def coverPoissonBilinear
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q : TangentCoordinates n →L[ℝ] ℝ) : ℝ :=
  inner ℝ (H.symm (coverCovectorVector q (logCoverAngularLift n)))
      (coverCovectorVector p (logCoverRadialLift n)) -
    inner ℝ (H.symm (coverCovectorVector q (logCoverRadialLift n)))
      (coverCovectorVector p (logCoverAngularLift n))

theorem coverPoissonBilinear_sub_left
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p p₀ q : TangentCoordinates n →L[ℝ] ℝ) :
    coverPoissonBilinear H (p - p₀) q =
      coverPoissonBilinear H p q - coverPoissonBilinear H p₀ q := by
  simp only [coverPoissonBilinear, coverCovectorVector_sub, inner_sub_right]
  ring

theorem coverPoissonBilinear_sub_right
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q q₀ : TangentCoordinates n →L[ℝ] ℝ) :
    coverPoissonBilinear H p (q - q₀) =
      coverPoissonBilinear H p q - coverPoissonBilinear H p q₀ := by
  simp only [coverPoissonBilinear, coverCovectorVector_sub, map_sub, inner_sub_left]
  ring

/-- A fixed coordinate constant accounts for the chosen cover norm. -/
def coverPoissonNormConstant (n : ℕ) : ℝ :=
  2 * ‖logCoverRadialLift n‖ * ‖logCoverAngularLift n‖

theorem norm_coverPoissonBilinear_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q : TangentCoordinates n →L[ℝ] ℝ) :
    ‖coverPoissonBilinear H p q‖ ≤ coverPoissonNormConstant n *
      ‖H.symm.toContinuousLinearMap‖ * ‖p‖ * ‖q‖ := by
  have hterm (e f : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
      ‖inner ℝ (H.symm (coverCovectorVector q e)) (coverCovectorVector p f)‖ ≤
        ‖H.symm.toContinuousLinearMap‖ * (‖q‖ * ‖e‖) * (‖p‖ * ‖f‖) := by
    refine (norm_inner_le_norm _ _).trans ?_
    apply mul_le_mul
    · exact (H.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_coverCovectorVector_le q e) (norm_nonneg _))
    · exact norm_coverCovectorVector_le p f
    · exact norm_nonneg _
    · positivity
  exact (norm_sub_le _ _).trans ((add_le_add
    (hterm (logCoverAngularLift n) (logCoverRadialLift n))
    (hterm (logCoverRadialLift n) (logCoverAngularLift n))).trans_eq (by
      dsimp only [coverPoissonNormConstant]; ring))

/-- Bilinear perturbation bound, including both differential errors. -/
theorem norm_coverPoissonBilinear_sub_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q p₀ q₀ : TangentCoordinates n →L[ℝ] ℝ) :
    ‖coverPoissonBilinear H p q - coverPoissonBilinear H p₀ q₀‖ ≤
      coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        (‖p - p₀‖ * ‖q‖ + ‖p₀‖ * ‖q - q₀‖) := by
  have he : coverPoissonBilinear H p q - coverPoissonBilinear H p₀ q₀ =
      coverPoissonBilinear H (p - p₀) q + coverPoissonBilinear H p₀ (q - q₀) := by
    rw [coverPoissonBilinear_sub_left, coverPoissonBilinear_sub_right]
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_coverPoissonBilinear_le H (p - p₀) q)
    (norm_coverPoissonBilinear_le H p₀ (q - q₀))).trans_eq (by ring))

/-- The source Poisson scalar for the real and imaginary parts of an actual
complex differential in logarithmic covering coordinates. -/
def coverPlanePairing
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) : ℝ :=
  coverPoissonBilinear H (Complex.reCLM.comp L) (Complex.imCLM.comp L)

theorem norm_coverPlanePairing_sub_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L L₀ : TangentCoordinates n →L[ℝ] ℂ) :
    ‖coverPlanePairing H L - coverPlanePairing H L₀‖ ≤
      (coverPoissonNormConstant n * ‖Complex.reCLM‖ * ‖Complex.imCLM‖) *
        ‖H.symm.toContinuousLinearMap‖ * ‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖) := by
  have hp : ‖Complex.reCLM.comp L - Complex.reCLM.comp L₀‖ ≤
      ‖Complex.reCLM‖ * ‖L - L₀‖ := by
    rw [← ContinuousLinearMap.comp_sub]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hq : ‖Complex.imCLM.comp L - Complex.imCLM.comp L₀‖ ≤
      ‖Complex.imCLM‖ * ‖L - L₀‖ := by
    rw [← ContinuousLinearMap.comp_sub]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hpn := ContinuousLinearMap.opNorm_comp_le Complex.reCLM L₀
  have hqn := ContinuousLinearMap.opNorm_comp_le Complex.imCLM L
  have hL : ‖L‖ ≤ ‖L - L₀‖ + ‖L₀‖ := by
    have he : L = (L - L₀) + L₀ := by abel
    conv_lhs => rw [he]
    exact norm_add_le _ _
  have h₁ := mul_le_mul hp hqn (norm_nonneg _) (by positivity)
  have h₂ := mul_le_mul hpn hq (norm_nonneg _) (by positivity)
  have hinner :
      ‖Complex.reCLM.comp L - Complex.reCLM.comp L₀‖ * ‖Complex.imCLM.comp L‖ +
        ‖Complex.reCLM.comp L₀‖ * ‖Complex.imCLM.comp L - Complex.imCLM.comp L₀‖ ≤
      (‖Complex.reCLM‖ * ‖Complex.imCLM‖) *
        (‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖)) := by
    calc
      _ ≤ (‖Complex.reCLM‖ * ‖L - L₀‖) * (‖Complex.imCLM‖ * ‖L‖) +
          (‖Complex.reCLM‖ * ‖L₀‖) * (‖Complex.imCLM‖ * ‖L - L₀‖) :=
        add_le_add h₁ h₂
      _ ≤ (‖Complex.reCLM‖ * ‖L - L₀‖) *
          (‖Complex.imCLM‖ * (‖L - L₀‖ + ‖L₀‖)) +
          (‖Complex.reCLM‖ * ‖L₀‖) * (‖Complex.imCLM‖ * ‖L - L₀‖) := by
        gcongr
      _ = _ := by ring
  exact (norm_coverPoissonBilinear_sub_le H _ _ _ _).trans
    ((mul_le_mul_of_nonneg_left hinner (by
      dsimp [coverPoissonNormConstant]; positivity)).trans_eq (by ring))

theorem contDiff_tailoringFamily_cover (I : ToricInput n) (β s : ℝ) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => tailoringFamily I β s (lgCover x)) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact ((contMDiff_tailoringFamily_lgManifold I β s).comp (contMDiff_lgCover n)).contDiff

theorem contDiff_tailoringOriginal_cover (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => tailoringOriginal I β (lgCover x)) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact ((contMDiff_tailoringOriginal_lgManifold I β).comp (contMDiff_lgCover n)).contDiff

/-- The differential of the original normalized polynomial is the literal
finite sum of its monomial differentials. -/
theorem fderiv_tailoringOriginal_cover (I : ToricInput n) (β : ℝ)
    (x : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n => tailoringOriginal I β (lgCover z)) x =
      ∑ v ∈ I.vertices, monomial (Real.exp (-β) : ℂ) v (lgCover x) • exponentLinearMap v := by
  exact (HasFDerivAt.fun_sum (u := I.vertices)
    (fun v _ => hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x)).fderiv

theorem norm_fderiv_tailoringOriginal_cover_le (I : ToricInput n) (β : ℝ)
    (x : TangentCoordinates n) :
    ‖fderiv ℝ (fun z : TangentCoordinates n => tailoringOriginal I β (lgCover z)) x‖ ≤
      (∑ v ∈ I.vertices, ‖exponentLinearMap v‖) * Real.exp (supportHeight I x.1 - β) := by
  rw [fderiv_tailoringOriginal_cover]
  calc
    _ ≤ ∑ v ∈ I.vertices,
        ‖monomial (Real.exp (-β) : ℂ) v (lgCover x) • exponentLinearMap v‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ I.vertices,
        ‖exponentLinearMap v‖ * Real.exp (supportHeight I x.1 - β) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_smul, norm_tailoring_monomial I β ⟨v, hv⟩ (lgCover x),
        tailoringWeight_vertex I β ⟨v, hv⟩]
      have he := Real.exp_le_exp.mpr (sub_le_sub_right
        (I.pairing_le_supportHeight x.1 ⟨v, hv⟩) β)
      simpa only [mul_comm, lgCover] using
        mul_le_mul_of_nonneg_right he (norm_nonneg (exponentLinearMap v))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The first source `rankerror` bound for the actual tailored differential
and actual inverse Hessian. Its constant precedes `β,s,x,H`; only the fixed
positive lower Hessian bound enters it. -/
theorem tailoringFamily_exists_uniform_coverPlanePairing_error (I : ToricInput n)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β s : ℝ), s ∈ Icc (0 : ℝ) 1 →
      ∀ (x : TangentCoordinates n)
        (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        ‖coverPlanePairing H
            (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x) -
          coverPlanePairing H
            (fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x)‖ ≤
          C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I x.1 - β) ^ 2 := by
  obtain ⟨A, hA, hC1⟩ := tailoringFamily_exists_uniform_C1_bound I
  let B := ∑ v ∈ I.vertices, ‖exponentLinearMap v‖
  let P := coverPoissonNormConstant n * ‖Complex.reCLM‖ * ‖Complex.imCLM‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hP : 0 ≤ P := by dsimp [P, coverPoissonNormConstant]; positivity
  let C := 1 + P * c⁻¹ * A * (A + 2 * B)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun β s hs x H hlower => ?_⟩
  let L := fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x
  let L₀ := fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x
  let ε := Real.exp (-Real.sqrt β)
  let M := Real.exp (supportHeight I x.1 - β)
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hε₁ : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hd : ‖L - L₀‖ ≤ A * ε * M := by
    have hdif := fderiv_sub
      ((contDiff_tailoringFamily_cover I β s).differentiable (by simp) x)
      ((contDiff_tailoringOriginal_cover I β).differentiable (by simp) x)
    have hb := (le_add_of_nonneg_left (norm_nonneg _)).trans (hC1 β s hs x)
    change ‖fderiv ℝ ((fun z => tailoringFamily I β s (lgCover z)) -
      (fun z => tailoringOriginal I β (lgCover z))) x‖ ≤ _ at hb
    rw [hdif] at hb
    exact hb
  have hb : ‖L₀‖ ≤ B * M := norm_fderiv_tailoringOriginal_cover_le I β x
  have hn := norm_inverse_le_of_lowerBound H hc hlower
  have hpoly : ‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖) ≤
      A * (A + 2 * B) * ε * M ^ 2 := by
    have hdcoarse : ‖L - L₀‖ ≤ A * M :=
      hd.trans (by nlinarith [mul_nonneg hA.le hM])
    calc
      _ ≤ (A * ε * M) * (A * M + 2 * (B * M)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ P * ‖H.symm.toContinuousLinearMap‖ *
        (‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖)) :=
      (norm_coverPlanePairing_sub_le H L L₀).trans_eq (by ring)
    _ ≤ P * c⁻¹ * (A * (A + 2 * B) * ε * M ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hn hP
      · exact hpoly
      · positivity
      · positivity
    _ ≤ C * ε * M ^ 2 := by dsimp [C]; nlinarith [mul_nonneg hε (sq_nonneg M)]

end FsFltz
