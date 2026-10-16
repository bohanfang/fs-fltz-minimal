import FsFltz.Analysis.TailoringFiberProjection

/-!
# Uniform operator bounds for the actual tailored fiber projection

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1212–1220.
The numerator is bilinear in the actual differential. Its perturbation and
the already proved Poisson perturbation are divided by the actual positive
Poisson scalars. In particular, no projection-error bound is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

private def coverProjectionTensor
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q : TangentCoordinates n →L[ℝ] ℝ) :
    TangentCoordinates n →L[ℝ] TangentCoordinates n :=
  q.smulRight (coverHamiltonianVector H p) - p.smulRight (coverHamiltonianVector H q)

private theorem norm_coverProjectionTensor_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p q : TangentCoordinates n →L[ℝ] ℝ) :
    ‖coverProjectionTensor H p q‖ ≤
      2 * coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖p‖ * ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by dsimp [coverPoissonNormConstant]; positivity)
  intro v
  change ‖q v • coverHamiltonianVector H p - p v • coverHamiltonianVector H q‖ ≤ _
  calc
    _ ≤ ‖q v • coverHamiltonianVector H p‖ + ‖p v • coverHamiltonianVector H q‖ := norm_sub_le _ _
    _ = ‖q v‖ * ‖coverHamiltonianVector H p‖ + ‖p v‖ * ‖coverHamiltonianVector H q‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ (‖q‖ * ‖v‖) * (coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖p‖) +
        (‖p‖ * ‖v‖) * (coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖q‖) := by
      apply add_le_add
      · exact mul_le_mul (q.le_opNorm _) (norm_coverHamiltonianVector_le H p)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (p.le_opNorm _) (norm_coverHamiltonianVector_le H q)
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A fixed coordinate constant for the projection numerator. -/
def coverProjectionNormConstant (n : ℕ) : ℝ :=
  2 * coverPoissonNormConstant n * ‖Complex.reCLM‖ * ‖Complex.imCLM‖

theorem norm_coverFiberProjectionNumerator_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) :
    ‖coverFiberProjectionNumerator H L‖ ≤
      coverProjectionNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖L‖ ^ 2 := by
  have hp := ContinuousLinearMap.opNorm_comp_le Complex.reCLM L
  have hq := ContinuousLinearMap.opNorm_comp_le Complex.imCLM L
  have hmul := mul_le_mul hp hq (norm_nonneg _) (by positivity)
  calc
    _ ≤ 2 * coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        (‖Complex.reCLM.comp L‖ * ‖Complex.imCLM.comp L‖) :=
      (norm_coverProjectionTensor_le H _ _).trans_eq (by ring)
    _ ≤ 2 * coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        ((‖Complex.reCLM‖ * ‖L‖) * (‖Complex.imCLM‖ * ‖L‖)) :=
      mul_le_mul_of_nonneg_left hmul (by dsimp [coverPoissonNormConstant]; positivity)
    _ = _ := by dsimp [coverProjectionNormConstant]; ring

/-- Both changes of covectors contribute to the actual numerator error. -/
theorem norm_coverFiberProjectionNumerator_sub_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L L₀ : TangentCoordinates n →L[ℝ] ℂ) :
    ‖coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀‖ ≤
      coverProjectionNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        ‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖) := by
  let p := Complex.reCLM.comp L
  let q := Complex.imCLM.comp L
  let p₀ := Complex.reCLM.comp L₀
  let q₀ := Complex.imCLM.comp L₀
  have he : coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀ =
      coverProjectionTensor H (p - p₀) q + coverProjectionTensor H p₀ (q - q₀) := by
    apply ContinuousLinearMap.ext
    intro v
    dsimp only [p, q, p₀, q₀]
    simp only [coverFiberProjectionNumerator, coverProjectionTensor, sub_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, coverHamiltonianVector_sub, sub_smul, smul_sub]
    abel
  have hp : ‖p - p₀‖ ≤ ‖Complex.reCLM‖ * ‖L - L₀‖ := by
    rw [show p - p₀ = Complex.reCLM.comp (L - L₀) by
      exact (ContinuousLinearMap.comp_sub _ _ _).symm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hq : ‖q - q₀‖ ≤ ‖Complex.imCLM‖ * ‖L - L₀‖ := by
    rw [show q - q₀ = Complex.imCLM.comp (L - L₀) by
      exact (ContinuousLinearMap.comp_sub _ _ _).symm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hp₀ : ‖p₀‖ ≤ ‖Complex.reCLM‖ * ‖L₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hq₁ : ‖q‖ ≤ ‖Complex.imCLM‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hL : ‖L‖ ≤ ‖L - L₀‖ + ‖L₀‖ := by
    have he : L = (L - L₀) + L₀ := by abel
    conv_lhs => rw [he]
    exact norm_add_le _ _
  rw [he]
  calc
    _ ≤ ‖coverProjectionTensor H (p - p₀) q‖ + ‖coverProjectionTensor H p₀ (q - q₀)‖ :=
      norm_add_le _ _
    _ ≤ 2 * coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        (‖p - p₀‖ * ‖q‖ + ‖p₀‖ * ‖q - q₀‖) :=
      (add_le_add (norm_coverProjectionTensor_le H _ _) (norm_coverProjectionTensor_le H _ _)).trans_eq
        (by ring)
    _ ≤ 2 * coverPoissonNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
        ((‖Complex.reCLM‖ * ‖L - L₀‖) * (‖Complex.imCLM‖ * (‖L - L₀‖ + ‖L₀‖)) +
          (‖Complex.reCLM‖ * ‖L₀‖) * (‖Complex.imCLM‖ * ‖L - L₀‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [coverPoissonNormConstant]; positivity)
      apply add_le_add
      · exact mul_le_mul hp (hq₁.trans (by gcongr)) (norm_nonneg _) (by positivity)
      · exact mul_le_mul hp₀ hq (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [coverProjectionNormConstant]; ring

/-- Positive actual denominators give a quantitative rational perturbation
bound for the actual continuous linear projectors. -/
theorem norm_coverFiberProjection_sub_le_of_pos
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L L₀ : TangentCoordinates n →L[ℝ] ℂ)
    (hpi : 0 < coverPlanePairing H L) (hpi₀ : 0 < coverPlanePairing H L₀) :
    ‖coverFiberProjection H L - coverFiberProjection H L₀‖ ≤
      ‖coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀‖ /
          coverPlanePairing H L +
        ‖coverPlanePairing H L - coverPlanePairing H L₀‖ *
          ‖coverFiberProjectionNumerator H L₀‖ /
            (coverPlanePairing H L * coverPlanePairing H L₀) := by
  have he : coverFiberProjection H L - coverFiberProjection H L₀ =
      (coverPlanePairing H L)⁻¹ •
          (coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀) +
        ((coverPlanePairing H L)⁻¹ - (coverPlanePairing H L₀)⁻¹) •
          coverFiberProjectionNumerator H L₀ := by
    simp only [coverFiberProjection]
    simp only [sub_eq_add_neg, add_smul, neg_smul, smul_add, smul_neg]
    abel
  rw [he]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, norm_smul, norm_inv, Real.norm_of_nonneg hpi.le,
    inv_sub_inv hpi.ne' hpi₀.ne', norm_div, norm_mul,
    Real.norm_of_nonneg hpi.le, Real.norm_of_nonneg hpi₀.le,
    norm_sub_rev (coverPlanePairing H L₀) (coverPlanePairing H L)]
  ring

theorem norm_coverFiberProjection_le_of_pos
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : TangentCoordinates n →L[ℝ] ℂ) (hpi : 0 < coverPlanePairing H L) :
    ‖coverFiberProjection H L‖ ≤ 1 +
      ‖coverFiberProjectionNumerator H L‖ / coverPlanePairing H L := by
  exact (norm_add_le _ _).trans ((add_le_add ContinuousLinearMap.norm_id_le
    (le_of_eq (by rw [norm_smul, norm_inv, Real.norm_of_nonneg hpi.le]; ring))))

/-- The source's uniform projector estimate for the literal family and the
actual positive potential Hessian. The same constant also bounds the actual
projector itself. All constants are chosen before `β,s,x`; the estimates hold
on the entire end, with no upper radial cutoff or base coefficient. -/
theorem tailoringFamily_exists_uniform_fiberProjection_bounds
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ x : TangentCoordinates n,
        R ≤ Real.sqrt (realSquaredNorm x.1) →
        let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
        let L := fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x
        let L₀ := fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x
        ‖coverFiberProjection H L - coverFiberProjection H L₀‖ ≤
            C * Real.exp (-Real.sqrt β) ∧
          ‖coverFiberProjection H L‖ ≤ C := by
  obtain ⟨A, hA, hC1⟩ := tailoringFamily_exists_uniform_C1_bound I
  obtain ⟨E, hE, herror⟩ := tailoringFamily_exists_uniform_native_planePairing_error I hφ hc hlower
  obtain ⟨d₀, hd₀, R₀, hR₀, hdom⟩ :=
    tailoringOriginal_exists_uniform_native_planePairing_lowerBound I hφ hc hU hlower hupper
  obtain ⟨d₁, hd₁, R₁, _hR₁, β₀, hβ₀, hpositive⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  let B := ∑ v ∈ I.vertices, ‖exponentLinearMap v‖
  let D := coverProjectionNormConstant n * c⁻¹
  let d := min d₀ (d₁ / 2)
  let Ndiff := D * A * (A + 2 * B)
  let N₀ := D * B ^ 2
  let N := D * (A + B) ^ 2
  let Cdiff := Ndiff / d + E * N₀ / d ^ 2
  let Cnorm := 1 + N / d
  let C := 1 + Cdiff + Cnorm
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hD : 0 ≤ D := by dsimp [D, coverProjectionNormConstant, coverPoissonNormConstant]; positivity
  have hP : 0 ≤ coverProjectionNormConstant n := by
    dsimp [coverProjectionNormConstant, coverPoissonNormConstant]; positivity
  have hd : 0 < d := lt_min hd₀ (by positivity)
  have hNd : 0 ≤ Ndiff := by dsimp [Ndiff]; positivity
  have hN₀ : 0 ≤ N₀ := by dsimp [N₀]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hCd : 0 ≤ Cdiff := by dsimp [Cdiff]; positivity
  have hCn : 0 ≤ Cnorm := by dsimp [Cnorm]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max R₀ R₁, lt_of_lt_of_le hR₀ (le_max_left _ _), β₀, hβ₀, ?_⟩
  intro β hβ s hs x hx
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  let L := fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x
  let L₀ := fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x
  let ε := Real.exp (-Real.sqrt β)
  let M := Real.exp (supportHeight I x.1 - β)
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hε₁ : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  have hM : 0 < M := Real.exp_pos _
  have hdM : 0 < d * M ^ 2 := by positivity
  have hδ : ‖L - L₀‖ ≤ A * ε * M := by
    have hdif := fderiv_sub
      ((contDiff_tailoringFamily_cover I β s).differentiable (by simp) x)
      ((contDiff_tailoringOriginal_cover I β).differentiable (by simp) x)
    have hb := (le_add_of_nonneg_left (norm_nonneg _)).trans (hC1 β s hs x)
    change ‖fderiv ℝ ((fun z => tailoringFamily I β s (lgCover z)) -
      (fun z => tailoringOriginal I β (lgCover z))) x‖ ≤ _ at hb
    rw [hdif] at hb
    exact hb
  have hδcoarse : ‖L - L₀‖ ≤ A * M :=
    hδ.trans (by nlinarith [mul_nonneg hA.le hM.le])
  have hL₀ : ‖L₀‖ ≤ B * M := norm_fderiv_tailoringOriginal_cover_le I β x
  have hL : ‖L‖ ≤ (A + B) * M := by
    have he : L = (L - L₀) + L₀ := by abel
    calc
      _ ≤ ‖L - L₀‖ + ‖L₀‖ := by
        conv_lhs => rw [he]
        exact norm_add_le _ _
      _ ≤ A * M + B * M := add_le_add hδcoarse hL₀
      _ = _ := by ring
  have hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v := fun _ => rfl
  let hnd := nondegenerate_lambdaPotentialForm_potentialHessian hφ hc hlower x
  have hpi₀ : d * M ^ 2 ≤ coverPlanePairing H L₀ := by
    have hb := hdom β (lgCover x) ((le_max_left _ _).trans hx) hnd
    rw [planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd
      (contMDiff_tailoringOriginal_lgManifold I β)] at hb
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg M)).trans hb
  have hpi : d * M ^ 2 ≤ coverPlanePairing H L := by
    have hb := (hpositive β hβ s hs (lgCover x) hnd).2.1 ((le_max_right _ _).trans hx)
    rw [planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd
      (contMDiff_tailoringFamily_lgManifold I β s)] at hb
    calc
      d * M ^ 2 ≤ (d₁ / 2) * M ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg M)
      _ = d₁ * M ^ 2 / 2 := by ring
      _ ≤ _ := hb
  have hpair : ‖coverPlanePairing H L - coverPlanePairing H L₀‖ ≤ E * ε * M ^ 2 := by
    have hb := herror β s hs (lgCover x) hnd
    rw [planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd
      (contMDiff_tailoringFamily_lgManifold I β s),
      planePairing_lambdaPotentialForm_eq_cover hφ x H hH hnd
      (contMDiff_tailoringOriginal_lgManifold I β)] at hb
    exact hb
  have hinv : ‖H.symm.toContinuousLinearMap‖ ≤ c⁻¹ :=
    norm_potentialHessianEquiv_symm_le hc hlower _
  have hNumdiff : ‖coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀‖ ≤
      Ndiff * ε * M ^ 2 := by
    calc
      _ ≤ coverProjectionNormConstant n * ‖H.symm.toContinuousLinearMap‖ *
          ‖L - L₀‖ * (‖L - L₀‖ + 2 * ‖L₀‖) := norm_coverFiberProjectionNumerator_sub_le H L L₀
      _ ≤ coverProjectionNormConstant n * c⁻¹ *
          (A * ε * M) * (A * M + 2 * (B * M)) := by
        gcongr
      _ = _ := by dsimp [Ndiff, D]; ring
  have hNum₀ : ‖coverFiberProjectionNumerator H L₀‖ ≤ N₀ * M ^ 2 := by
    calc
      _ ≤ coverProjectionNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖L₀‖ ^ 2 :=
        norm_coverFiberProjectionNumerator_le H L₀
      _ ≤ coverProjectionNormConstant n * c⁻¹ * (B * M) ^ 2 := by gcongr
      _ = _ := by dsimp [N₀, D]; ring
  have hNum : ‖coverFiberProjectionNumerator H L‖ ≤ N * M ^ 2 := by
    calc
      _ ≤ coverProjectionNormConstant n * ‖H.symm.toContinuousLinearMap‖ * ‖L‖ ^ 2 :=
        norm_coverFiberProjectionNumerator_le H L
      _ ≤ coverProjectionNormConstant n * c⁻¹ * ((A + B) * M) ^ 2 := by gcongr
      _ = _ := by dsimp [N, D]; ring
  have hterm₁ : ‖coverFiberProjectionNumerator H L - coverFiberProjectionNumerator H L₀‖ /
      coverPlanePairing H L ≤ (Ndiff / d) * ε := by
    calc
      _ ≤ (Ndiff * ε * M ^ 2) / (d * M ^ 2) := div_le_div₀ (by positivity) hNumdiff hdM hpi
      _ = _ := by field_simp
  have hden : (d * M ^ 2) * (d * M ^ 2) ≤
      coverPlanePairing H L * coverPlanePairing H L₀ :=
    mul_le_mul hpi hpi₀ hdM.le ((hdM.trans_le hpi).le)
  have hterm₂ : ‖coverPlanePairing H L - coverPlanePairing H L₀‖ *
      ‖coverFiberProjectionNumerator H L₀‖ /
        (coverPlanePairing H L * coverPlanePairing H L₀) ≤ (E * N₀ / d ^ 2) * ε := by
    calc
      _ ≤ (E * ε * M ^ 2) * (N₀ * M ^ 2) / ((d * M ^ 2) * (d * M ^ 2)) :=
        div_le_div₀ (by positivity) (mul_le_mul hpair hNum₀ (norm_nonneg _) (by positivity))
          (by positivity) hden
      _ = _ := by field_simp
  constructor
  · calc
      _ ≤ (Ndiff / d) * ε + (E * N₀ / d ^ 2) * ε :=
        (norm_coverFiberProjection_sub_le_of_pos H L L₀ (hdM.trans_le hpi)
          (hdM.trans_le hpi₀)).trans (add_le_add hterm₁ hterm₂)
      _ = Cdiff * ε := by dsimp [Cdiff]; ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hε
  · calc
      _ ≤ 1 + ‖coverFiberProjectionNumerator H L‖ / coverPlanePairing H L :=
        norm_coverFiberProjection_le_of_pos H L (hdM.trans_le hpi)
      _ ≤ 1 + (N * M ^ 2) / (d * M ^ 2) := by
        exact add_le_add_right (div_le_div₀ (by positivity) hNum hdM hpi) 1
      _ = Cnorm := by dsimp [Cnorm]; field_simp
      _ ≤ C := by dsimp [C]; linarith

end FsFltz
