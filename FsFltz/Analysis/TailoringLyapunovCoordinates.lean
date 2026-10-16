import FsFltz.Analysis.TailoringGoodDifferential
import FsFltz.Analysis.PotentialComplexPositivity

/-!
# Coordinate estimates for the actual intrinsic Lyapunov calculation

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1478–1489.
The actual tangent planes admit an exponentially small correction of their
standard complex rotation. Contraction against every actual tangent vector
is the actual restricted potential primitive.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

theorem norm_coordinateComplexStructure (v : TangentCoordinates n) :
    ‖coordinateComplexStructure n v‖ = ‖v‖ := by
  simp only [coordinateComplexStructure_apply, Prod.norm_def, norm_neg, max_comm]

/-- An actual endpoint tangent vector has an exponentially nearby actual
tangent vector representing its standard complex rotation. -/
theorem tailoringEndpoint_exists_uniform_nearby_rotated_tangent (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ v : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
      ∃ w : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w = 0 ∧
        ‖w - coordinateComplexStructure n v‖ ≤ C * Real.exp (-Real.sqrt β) * ‖v‖ := by
  obtain ⟨A, hA, B, hB, hlead⟩ := tailoringEndpoint_exists_uniform_nearby_leading_tangent I
  obtain ⟨D, hD, B', _, hactual⟩ := tailoringEndpoint_exists_uniform_nearby_actual_tangent I
  refine ⟨D * (1 + A) + A, by positivity, max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ x hx v hv
  let ε := Real.exp (-Real.sqrt β)
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hεone : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  obtain ⟨u, hu, hdist⟩ := hlead β ((le_max_left _ _).trans hβ) x hx v hv
  have hJu : tailoringLeadingDifferential I β (lgCover x) (coordinateComplexStructure n u) = 0 := by
    rw [tailoringLeadingDifferential_complexStructure, hu, mul_zero]
  obtain ⟨w, hw, hdist'⟩ := hactual β ((le_max_right _ _).trans hβ) x hx _ hJu
  have hun : ‖u‖ ≤ (1 + A) * ‖v‖ := by
    have htri : ‖u‖ ≤ ‖v‖ + ‖v - u‖ := norm_le_insert _ _
    have hsmall : A * ε * ‖v‖ ≤ A * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hA.le hεone) (norm_nonneg _)
    linarith
  refine ⟨w, hw, ?_⟩
  calc
    _ ≤ ‖w - coordinateComplexStructure n u‖ +
        ‖coordinateComplexStructure n u - coordinateComplexStructure n v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖coordinateComplexStructure n u - w‖ + ‖u - v‖ := by
      rw [norm_sub_rev w, ← map_sub, norm_coordinateComplexStructure]
    _ ≤ D * ε * ((1 + A) * ‖v‖) + A * ε * ‖v‖ := by
      apply add_le_add
      · rw [norm_coordinateComplexStructure] at hdist'
        exact hdist'.trans (mul_le_mul_of_nonneg_left hun (by positivity))
      · simpa only [norm_sub_rev u] using hdist
    _ = _ := by ring

/-- Coordinate pairing in the primitive obeys a fixed-dimensional bound. -/
theorem norm_coordinate_pairing_le (p : RealSpace n) (v : TangentCoordinates n) :
    ‖∑ j, p j * v.2 j‖ ≤ (n : ℝ) * ‖p‖ * ‖v‖ := by
  calc
    _ ≤ ∑ j : Fin n, ‖p j * v.2 j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖p‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm p j)
        ((norm_le_pi_norm v.2 j).trans (norm_snd_le v)) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

/-- The cover vector of the actual projected field contracts against every
actual tangent with precisely the restricted potential primitive. -/
theorem tailoring_projectedLiouville_contraction
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    {φ : RealSpace n → ℝ}
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (q : TangentCoordinates n)
    (hq : lgCoverTangent x q =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)))
    (v : TangentCoordinates n)
    (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x v) =
      ∑ j, coordinateGradient φ x.1 j * v.2 j := by
  have hker : complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
      (lgCoverTangent x v) = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)] at hv
    exact hv
  rw [hq, (lgManifold n).rankTwoFiberProjection_contraction
    ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
    ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) _
    (by simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hker, Complex.zero_re])
    (by simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, hker, Complex.zero_im]),
    (lgManifold n).liouvilleVector_contraction (lambdaPotentialForm φ) (lgCover x)
      ((lgManifold n).liouvilleEquation_exists (lambdaPotentialForm φ) (lgCover x) hnd),
    lambdaPotentialForm_lgCover]

/-- The primitive of an actual intrinsic vector is quantitatively separated
from the retained conormal only by its vector norm and the proved tangent
error. This is the bound consumed by bad-region conormal separation. -/
theorem tailoringEndpoint_exists_uniform_projectedLiouville_conormal_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ A : ℝ, 0 < A ∧ ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ (hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
        (q : TangentCoordinates n),
      lgCoverTangent x q = (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) →
      ∃ t : ℂ, ‖(fun k => (coordinateGradient φ x.1 k : ℂ)) -
          t • tailoringRetainedNormal I β (lgCover x)‖ ≤
        A * Real.exp (-Real.sqrt β) * ‖coordinateGradient φ x.1‖ + D * ‖q‖ := by
  obtain ⟨C, hC, B, hB, hactual⟩ := tailoringEndpoint_exists_uniform_nearby_actual_tangent I
  obtain ⟨B', _, hG⟩ := tailoringEndpoint_exists_uniform_retainedNormal_ne_zero I
  let V := 2 * U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  refine ⟨1 + 4 * n * C, by positivity, 1 + 4 * V * (1 + C), by positivity,
    max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ x hx hnd q hq
  let ε := Real.exp (-Real.sqrt β)
  let p := coordinateGradient φ x.1
  let η := (n : ℝ) * C * ε * ‖p‖ + V * (1 + C) * ‖q‖
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hεone : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg β))
  have hpair (v : TangentCoordinates n)
      (hv : tailoringLeadingDifferential I β (lgCover x) v = 0) :
      ‖∑ k, p k * v.2 k‖ ≤ η * ‖v‖ := by
    obtain ⟨w, hw, hdist⟩ := hactual β ((le_max_left _ _).trans hβ) x hx v hv
    have hnorm : ‖w‖ ≤ (1 + C) * ‖v‖ := by
      have htri : ‖w‖ ≤ ‖v‖ + ‖v - w‖ := norm_le_insert _ _
      have hsmall : C * ε * ‖v‖ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC.le hεone) (norm_nonneg _)
      linarith
    have heq : (∑ k, p k * v.2 k) =
        (∑ k, p k * (v - w).2 k) + ∑ k, p k * w.2 k := by
      change (∑ k, p k * v.2 k) =
        (∑ k, p k * (v.2 k - w.2 k)) + ∑ k, p k * w.2 k
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    have hcontract := tailoring_projectedLiouville_contraction I β x hnd q hq w hw
    calc
      _ ≤ ‖∑ k, p k * (v - w).2 k‖ + ‖∑ k, p k * w.2 k‖ := by rw [heq]; exact norm_add_le _ _
      _ ≤ (n : ℝ) * ‖p‖ * ‖v - w‖ + V * ‖q‖ * ‖w‖ := by
        apply add_le_add (norm_coordinate_pairing_le p (v - w))
        rw [← hcontract]
        exact exteriorDerivative_lambdaPotentialForm_norm_le hφ hc.le hU.le hlower hupper x q w
      _ ≤ (n : ℝ) * ‖p‖ * (C * ε * ‖v‖) + V * ‖q‖ * ((1 + C) * ‖v‖) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hdist (by positivity))
          (mul_le_mul_of_nonneg_left hnorm (by positivity))
      _ = _ := by dsimp [η]; ring
  obtain ⟨t, ht⟩ := exists_retained_line_approximation_of_leading_pairing_bound
    I β (lgCover x) (hG β ((le_max_right _ _).trans hβ) (lgCover x) hx) p hη (Or.inr hpair)
  refine ⟨t, ht.trans ?_⟩
  dsimp [η]
  have hp := norm_nonneg p
  have hqn := norm_nonneg q
  have hε := Real.exp_pos (-Real.sqrt β)
  dsimp [ε]
  nlinarith

/-- The Liouville equation on a nearby rotated tangent gives a quantitative
lower energy bound. All error terms are evaluations of the actual form. -/
theorem tailoring_projectedLiouville_energy_lower
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c U : ℝ} (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (q : TangentCoordinates n)
    (hq : lgCoverTangent x q =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)))
    (w : TangentCoordinates n)
    (hw : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w = 0)
    {η K : ℝ} (hK : 0 ≤ K)
    (hdist : ‖w - coordinateComplexStructure n q‖ ≤ η * ‖q‖)
    (hgrad : ‖coordinateGradient φ x.1‖ ≤ K * ‖q‖) :
    c * ‖q‖ ^ 2 -
      (2 * U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ 2 + n * K) *
        η * ‖q‖ ^ 2 ≤
      (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x q) := by
  let e := w - coordinateComplexStructure n q
  let V := 2 * U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let Ω (v : TangentCoordinates n) :=
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
      (lgCoverTangent x q) (lgCoverTangent x v)
  let primitiveEval (v : TangentCoordinates n) := ∑ j, coordinateGradient φ x.1 j * v.2 j
  have hcon : Ω w = primitiveEval w := tailoring_projectedLiouville_contraction I β x hnd q hq w hw
  have hΩe : Ω e = Ω w - Ω (coordinateComplexStructure n q) := by
    dsimp [Ω, e]
    rw [map_sub, evalTwo_sub_right]
  have hlame : primitiveEval e = primitiveEval w - primitiveEval (coordinateComplexStructure n q) := by
    change (∑ j, coordinateGradient φ x.1 j * (w.2 j - q.1 j)) = _
    simp [primitiveEval, coordinateComplexStructure_apply, mul_sub, Finset.sum_sub_distrib]
  have hderiv : (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
      (lgCoverTangent x q) = primitiveEval (coordinateComplexStructure n q) := by
    rw [scalarDerivative_potential_lgCover hφ, fderiv_eq_coordinateGradient_pairing]
    rfl
  have hωbound : ‖Ω e‖ ≤ V * η * ‖q‖ ^ 2 := by
    exact (exteriorDerivative_lambdaPotentialForm_norm_le hφ hc.le hU.le hlower hupper x q e).trans
      ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ V * ‖q‖)).trans_eq (by ring))
  have hlambound : ‖primitiveEval e‖ ≤ (n : ℝ) * K * η * ‖q‖ ^ 2 := by
    exact (norm_coordinate_pairing_le (coordinateGradient φ x.1) e).trans
      ((mul_le_mul (mul_le_mul_of_nonneg_left hgrad (by positivity)) hdist
        (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have hlo := exteriorDerivative_lambdaPotentialForm_complex_lower hφ hc.le hlower x q
  change c * ‖q‖ ^ 2 ≤ Ω (coordinateComplexStructure n q) at hlo
  rw [hderiv]
  have hωmin : -V * η * ‖q‖ ^ 2 ≤ Ω e := by
    have h := (neg_abs_le (Ω e)).trans' (neg_le_neg hωbound)
    simpa only [Real.norm_eq_abs, neg_mul] using h
  have hlammax : primitiveEval e ≤ (n : ℝ) * K * η * ‖q‖ ^ 2 :=
    (le_abs_self _).trans hlambound
  change c * ‖q‖ ^ 2 - (V + n * K) * η * ‖q‖ ^ 2 ≤ _
  nlinarith

end FsFltz
