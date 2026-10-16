import FsFltz.Analysis.TailoringPoissonEstimates
import FsFltz.Analysis.TailoringSimplex

/-!
# Exact differential and radial error of the tailored endpoint

Source: `geometric-part-fsf-proof.tex`, `sec:critical`, `eq:exactdF`
and `eq:Gchi`, lines 1328–1352. All coefficients below are computed from
the literal finite cutoffs. The tangent estimate consumes the exact
decomposition and uniform cutoff derivative bound on the entire endpoint
fiber; it does not assume any critical-point or full-core conclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff

variable {n : ℕ}

/-- The source's literal retained coefficient `qᵥ = χᵥ mᵥ`. -/
def tailoringRetainedMonomial (I : ToricInput n) (β : ℝ)
    (v : Lattice n) (y : LGSpace n) : ℂ :=
  (tailoringCutoff I β v y.1 : ℂ) * monomial (Real.exp (-β) : ℂ) v y

/-- The complex-linear part of the exact tailored differential. -/
def tailoringLeadingDifferential (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) : TangentCoordinates n →L[ℝ] ℂ :=
  ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y • exponentLinearMap v

/-- The actual radial cutoff-error covector, before extending by zero
on angular directions. -/
def tailoringRadialError (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) : RealSpace n →L[ℝ] ℂ :=
  (∑ v ∈ I.vertices, monomial (Real.exp (-β) : ℂ) v y •
    (Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β v) y.1))) -
      Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β 0) y.1)

theorem sum_tailoringRetainedMonomial_eq_cutoff_of_fiber
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hy : tailoringFamily I β 1 y = 1) :
    ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y =
      (tailoringCutoff I β 0 y.1 : ℂ) := by
  have h := (Set.ext_iff.mp (tailoringFamily_one_fiber I β) y).mp hy
  change -(tailoringCutoff I β 0 y.1 : ℂ) +
    ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y = 0 at h
  linear_combination h

private theorem hasFDerivAt_cutoff_cover (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (x : TangentCoordinates n) :
    HasFDerivAt (fun z : TangentCoordinates n => (tailoringCutoff I β a z.1 : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (tailoringCutoff I β a) x.1).comp
        (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)))) x := by
  exact Complex.ofRealCLM.hasFDerivAt.comp x
    (((tailoringCutoff_contDiff I β a).differentiable (by simp) x.1).hasFDerivAt.comp x
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).hasFDerivAt)

/-- The exact defining-equation differential, including every cutoff term. -/
theorem fderiv_tailoringEquation_cover (I : ToricInput n) (β : ℝ)
    (x : TangentCoordinates n) :
    fderiv ℝ (fun z => tailoringEquation I β (lgCover z)) x =
      tailoringLeadingDifferential I β (lgCover x) +
        (tailoringRadialError I β (lgCover x)).comp
          (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)) := by
  have h := ((hasFDerivAt_cutoff_cover I β 0 x).neg.add
    (HasFDerivAt.fun_sum (u := I.vertices) (fun v _ =>
      (hasFDerivAt_cutoff_cover I β v x).mul
        (hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x)))).fderiv
  change fderiv ℝ (fun z => tailoringEquation I β (lgCover z)) x = _ at h
  rw [h]
  apply ContinuousLinearMap.ext
  intro z
  simp only [tailoringLeadingDifferential, tailoringRadialError,
    tailoringRetainedMonomial, add_apply,
    neg_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.fst,
    smul_eq_mul, lgCover]
  rw [Finset.sum_add_distrib]
  simp only [mul_assoc]
  abel

/-- Flatness of the small-monomial cutoff makes the actual endpoint family
differential equal the defining-equation differential at every fiber point. -/
theorem fderiv_tailoringFamily_one_eq_equation_of_fiber
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x =
      fderiv ℝ (fun z => tailoringEquation I β (lgCover z)) x := by
  have hη : tailoringEta I β (lgCover x) = 1 := by
    by_contra hη
    have h := norm_tailoringFamily_lt_one_of_eta_ne_one I β
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) (lgCover x) hη
    rw [hx, norm_one] at h
    exact (lt_irrefl _ h).elim
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
  have hF : DifferentiableAt ℝ F x :=
    ((hasFDerivAt_cutoff_cover I β 0 x).neg.add
      (HasFDerivAt.fun_sum (u := I.vertices) (fun v _ =>
        (hasFDerivAt_cutoff_cover I β v x).mul
          (hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x)))).differentiableAt
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


/-- Every retained monomial is at most the actual maximal nonconstant magnitude. -/
theorem norm_tailoringRetainedMonomial_le_max (I : ToricInput n) (β : ℝ)
    (v : Lattice n) (hv : v ∈ I.vertices) (y : LGSpace n) :
    ‖tailoringRetainedMonomial I β v y‖ ≤ Real.exp (supportHeight I y.1 - β) := by
  rw [tailoringRetainedMonomial, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tailoringCutoff_nonneg I β v y.1)]
  apply (mul_le_of_le_one_left (norm_nonneg _) (tailoringCutoff_le_one I β v y.1)).trans
  rw [norm_tailoring_monomial I β ⟨v, hv⟩ y, tailoringWeight_vertex I β ⟨v, hv⟩]
  exact Real.exp_le_exp.mpr (sub_le_sub_right (I.pairing_le_supportHeight y.1 ⟨v, hv⟩) β)

/-- The exact lower bound `M ≥ 1 / |V|` on the entire endpoint fiber. -/
theorem tailoringEndpoint_max_monomial_lower (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hy : tailoringFamily I β 1 y = 1) :
    1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hN1 : (1 : ℝ) ≤ I.vertices.card := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  by_cases hM : 1 ≤ Real.exp (supportHeight I y.1 - β)
  · exact (one_div_le_one_div_of_le zero_lt_one hN1).trans (by simpa using hM)
  have hweight : supportHeight I y.1 - β ≤ 0 :=
    (Real.exp_le_one_iff.mp (le_of_not_ge hM))
  have hχ : tailoringCutoff I β 0 y.1 = 1 := by
    apply tailoringCutoff_eq_one_of_maximal
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_zero]
    exact (sub_le_sub_right (I.pairing_le_supportHeight y.1 ⟨a, ha⟩) β).trans hweight
  have hsum := sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β y hy
  rw [hχ, Complex.ofReal_one] at hsum
  have hbound : (1 : ℝ) ≤ I.vertices.card * Real.exp (supportHeight I y.1 - β) := by
    calc
      1 = ‖∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y‖ := by rw [hsum, norm_one]
      _ ≤ ∑ v ∈ I.vertices, ‖tailoringRetainedMonomial I β v y‖ := norm_sum_le _ _
      _ ≤ ∑ _v ∈ I.vertices, Real.exp (supportHeight I y.1 - β) :=
        Finset.sum_le_sum fun v hv => norm_tailoringRetainedMonomial_le_max I β v hv y
      _ = _ := by simp
  exact (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hbound)

/-- A support-maximizing vertex is completely uncut on the endpoint fiber
once the prescribed square-root cutoff gap exceeds `log |V|`. -/
theorem tailoringEndpoint_maximizing_cutoff_eq_one (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hy : tailoringFamily I β 1 y = 1)
    (hβ : Real.log (I.vertices.card : ℝ) ≤ Real.sqrt β)
    (v : {v : Lattice n // v ∈ I.vertices}) (hv : pairing v.val y.1 = supportHeight I y.1) :
    tailoringCutoff I β v.val y.1 = 1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hlog := (Real.log_le_iff_le_exp (one_div_pos.mpr hN)).mpr
    (tailoringEndpoint_max_monomial_lower I β y hy)
  rw [Real.log_div (by norm_num) hN.ne', Real.log_one, zero_sub] at hlog
  apply tailoringCutoff_eq_one_of_gap
  intro a ha
  rw [tailoringWeight_vertex I β v, hv]
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rw [tailoringWeight_zero]
    linarith
  · rw [tailoringWeight_vertex I β ⟨a, ha⟩]
    have := I.pairing_le_supportHeight y.1 ⟨a, ha⟩
    have := Real.sqrt_nonneg β
    linarith

private theorem norm_monomial_cutoff_derivative_le (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (v : Lattice n) (hv : v ∈ I.vertices)
    {D : ℝ} (hD : 0 ≤ D) (hb : ‖fderiv ℝ (tailoringCutoff I β v) y.1‖ ≤ D) :
    ‖monomial (Real.exp (-β) : ℂ) v y •
      (Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β v) y.1))‖ ≤
      (‖Complex.ofRealCLM‖ * D) *
        (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β))) := by
  by_cases hd : fderiv ℝ (tailoringCutoff I β v) y.1 = 0
  · rw [norm_smul, hd, ContinuousLinearMap.comp_zero, norm_zero, mul_zero]
    positivity
  have hm : ‖monomial (Real.exp (-β) : ℂ) v y‖ ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β)) := by
    rw [norm_tailoring_monomial I β ⟨v, hv⟩ y]
    exact tailoringCutoff_changed_exp_bound I β v y.1 (Or.inr hd)
  rw [norm_smul]
  exact (mul_le_mul hm ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) (norm_nonneg _) (by positivity)).trans_eq
      (mul_comm _ _)

/-- The exact radial error has the uniform exponentially small bound on
all logarithmic points, before imposing the endpoint equation. -/
theorem tailoringRadialError_exists_uniform_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, ∀ y : LGSpace n,
      ‖tailoringRadialError I β y‖ ≤
        C * (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β))) := by
  obtain ⟨D, hD, hb⟩ := tailoringCutoffs_exists_uniform_bound_iteratedFDeriv I 1
  have hd (β : ℝ) (a : Lattice n) (ha : a ∈ tailoringExponents I) (u : RealSpace n) :
      ‖fderiv ℝ (tailoringCutoff I β a) u‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using hb β a ha u
  let C := ((I.vertices.card : ℝ) + 1) * (‖Complex.ofRealCLM‖ * D)
  refine ⟨C, by dsimp [C]; positivity, fun β y => ?_⟩
  let δ := Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β))
  have hconst : ‖Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β 0) y.1)‖ ≤
      (‖Complex.ofRealCLM‖ * D) * δ := by
    by_cases hz : fderiv ℝ (tailoringCutoff I β 0) y.1 = 0
    · simp only [hz, ContinuousLinearMap.comp_zero, norm_zero]
      dsimp [δ]
      positivity
    have he := tailoringCutoff_changed_exp_bound I β 0 y.1 (Or.inr hz)
    simp only [tailoringWeight_zero, Real.exp_zero] at he
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hd β 0 (Finset.mem_insert_self _ _) y.1)
        (norm_nonneg _))).trans (le_mul_of_one_le_right (by positivity) he)
  calc
    ‖tailoringRadialError I β y‖ ≤
        (∑ v ∈ I.vertices, ‖monomial (Real.exp (-β) : ℂ) v y •
          (Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β v) y.1))‖) +
        ‖Complex.ofRealCLM.comp (fderiv ℝ (tailoringCutoff I β 0) y.1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ _v ∈ I.vertices, (‖Complex.ofRealCLM‖ * D) * δ) +
        (‖Complex.ofRealCLM‖ * D) * δ := by
      apply add_le_add _ hconst
      exact Finset.sum_le_sum fun v hv =>
        norm_monomial_cutoff_derivative_le I β y v hv hD
          (hd β v (Finset.mem_insert_of_mem hv) y.1)
    _ = C * δ := by simp only [Finset.sum_const, nsmul_eq_mul, C]; ring

/-- On the entire endpoint fiber the error is `O(exp(-√β) M)`, with one
constant depending only on the original finite toric input. -/
theorem tailoringEndpoint_exists_uniform_radialError_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, ∀ y : LGSpace n,
      tailoringFamily I β 1 y = 1 →
      ‖tailoringRadialError I β y‖ ≤
        C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨D, hD, hb⟩ := tailoringRadialError_exists_uniform_bound I
  let C := 1 + D * I.vertices.card
  refine ⟨C, by dsimp [C]; positivity, fun β y hy => ?_⟩
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hN1 : (1 : ℝ) ≤ I.vertices.card := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hmax : max 1 (Real.exp (supportHeight I y.1 - β)) ≤
      I.vertices.card * Real.exp (supportHeight I y.1 - β) := by
    apply max_le
    · have h := (div_le_iff₀ hN).mp (tailoringEndpoint_max_monomial_lower I β y hy)
      simpa only [mul_comm] using h
    · exact le_mul_of_one_le_left (Real.exp_pos _).le hN1
  calc
    _ ≤ D * (Real.exp (-Real.sqrt β) *
        (I.vertices.card * Real.exp (supportHeight I y.1 - β))) :=
      (hb β y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le) hD)
    _ ≤ C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I y.1 - β) := by
      have hDC : D * I.vertices.card ≤ C := by dsimp [C]; linarith
      have h := mul_le_mul_of_nonneg_right hDC
        (mul_nonneg (Real.exp_pos (-Real.sqrt β)).le
          (Real.exp_pos (supportHeight I y.1 - β)).le)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- The exact equation and error estimate control every actual equation
tangent vector through its leading complex hyperplane covector. -/
theorem tailoringEndpoint_exists_uniform_tangent_error_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, ∀ x : TangentCoordinates n,
      tailoringFamily I β 1 (lgCover x) = 1 → ∀ v : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
      ‖tailoringLeadingDifferential I β (lgCover x) v‖ ≤
        C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I x.1 - β) * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := tailoringEndpoint_exists_uniform_radialError_bound I
  refine ⟨C, hC, fun β x hx v hv => ?_⟩
  rw [fderiv_tailoringFamily_one_eq_equation_of_fiber I β x hx] at hv
  rw [fderiv_tailoringEquation_cover, add_apply, ContinuousLinearMap.comp_apply] at hv
  have he : tailoringLeadingDifferential I β (lgCover x) v =
      -tailoringRadialError I β (lgCover x) v.1 := eq_neg_of_add_eq_zero_left hv
  rw [he, norm_neg]
  exact ((tailoringRadialError I β (lgCover x)).le_opNorm v.1).trans
    (mul_le_mul (hb β (lgCover x) hx) (norm_fst_le v) (norm_nonneg _) (by positivity))

end FsFltz
