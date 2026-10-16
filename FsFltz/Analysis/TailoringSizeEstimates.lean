import FsFltz.Analysis.TailoringFamily

/-!
# Bounds for the prescribed small-monomial transition

Source: `geometric-part-fsf-proof.tex`, `eq:fs` and `eq:C1`, lines 1097–1114.
The size and transition below are the existing quotient functions evaluated
at angle zero. Their independence of the angle is proved explicitly.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

def tailoringSizeSquared (I : ToricInput n) (β : ℝ) (u : RealSpace n) : ℝ :=
  ∑ v ∈ I.vertices, Real.exp (tailoringWeight β v u) ^ 2

theorem tailoringSizeSquared_pos (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    0 < tailoringSizeSquared I β u :=
  Finset.sum_pos (fun _v _ => sq_pos_of_pos (Real.exp_pos _)) I.vertices_nonempty

theorem tailoringMonomialSize_eq (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringMonomialSize I β y = Real.sqrt (tailoringSizeSquared I β y.1) := by
  unfold tailoringMonomialSize tailoringSizeSquared
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [norm_tailoring_monomial I β ⟨v, hv⟩ y]

theorem contDiff_tailoringSizeSquared (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (tailoringSizeSquared I β) := by
  unfold tailoringSizeSquared tailoringWeight pairing
  fun_prop

def tailoringPairingBound (I : ToricInput n) : ℝ :=
  1 + ∑ v ∈ I.vertices, ‖pairingCLM v‖

theorem tailoringPairingBound_pos (I : ToricInput n) : 0 < tailoringPairingBound I := by
  have := Finset.sum_nonneg (fun v (_ : v ∈ I.vertices) => norm_nonneg (pairingCLM v))
  unfold tailoringPairingBound
  linarith

theorem norm_pairingCLM_le_tailoringPairingBound (I : ToricInput n)
    {v : Lattice n} (hv : v ∈ I.vertices) : ‖pairingCLM v‖ ≤ tailoringPairingBound I := by
  have := Finset.single_le_sum (fun v (_ : v ∈ I.vertices) => norm_nonneg (pairingCLM v)) hv
  unfold tailoringPairingBound
  linarith

private theorem hasFDerivAt_tailoringWeight (β : ℝ) (v : Lattice n) (u : RealSpace n) :
    HasFDerivAt (tailoringWeight β v) (pairingCLM v) u := by
  change HasFDerivAt (fun u => pairing v u - β * tailoringNu v) _ u
  simpa only [pairingCLM_apply] using
    (pairingCLM v).hasFDerivAt.sub_const (β * tailoringNu v)

theorem norm_fderiv_tailoringSizeSquared_le (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) :
    ‖fderiv ℝ (tailoringSizeSquared I β) u‖ ≤
      2 * tailoringPairingBound I * tailoringSizeSquared I β u := by
  have hd (v : Lattice n) :=
    ((Real.hasDerivAt_exp (tailoringWeight β v u)).comp_hasFDerivAt u
      (hasFDerivAt_tailoringWeight β v u)).pow 2
  have he := (HasFDerivAt.fun_sum (u := I.vertices) (fun v _ => hd v)).fderiv
  change fderiv ℝ (tailoringSizeSquared I β) u = _ at he
  rw [he]
  calc
    _ ≤ ∑ v ∈ I.vertices, ‖(2 • Real.exp (tailoringWeight β v u) ^ (2 - 1)) •
      (Real.exp (tailoringWeight β v u) • pairingCLM v)‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ I.vertices, 2 * tailoringPairingBound I *
      Real.exp (tailoringWeight β v u) ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      simp only [norm_smul, Real.norm_eq_abs, Nat.reduceSub, pow_one, nsmul_eq_mul,
        abs_mul, abs_of_pos (Real.exp_pos _), Nat.cast_ofNat,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h := norm_pairingCLM_le_tailoringPairingBound I hv
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg (Real.exp (tailoringWeight β v u)))]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem contDiff_tailoringSize (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (fun u => Real.sqrt (tailoringSizeSquared I β u)) :=
  (contDiff_tailoringSizeSquared I β).sqrt
    (fun u => ne_of_gt (tailoringSizeSquared_pos I β u))

theorem norm_fderiv_tailoringSize_le (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    ‖fderiv ℝ (fun u => Real.sqrt (tailoringSizeSquared I β u)) u‖ ≤
      tailoringPairingBound I * Real.sqrt (tailoringSizeSquared I β u) := by
  let q := tailoringSizeSquared I β u
  have hq : 0 < q := tailoringSizeSquared_pos I β u
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [((contDiff_tailoringSizeSquared I β).differentiable (by simp) u).hasFDerivAt.sqrt
    hq.ne' |>.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hb := norm_fderiv_tailoringSizeSquared_le I β u
  have he := Real.sq_sqrt hq.le
  dsimp only [q] at hs he
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  calc
    _ ≤ 2 * tailoringPairingBound I * tailoringSizeSquared I β u := hb
    _ = _ := by linear_combination -2 * tailoringPairingBound I * he

def tailoringEtaScalar (I : ToricInput n) (r : ℝ) : ℝ :=
  Real.smoothTransition ((r - tailoringSmallConstant I) / tailoringSmallConstant I)

theorem contDiff_tailoringEtaScalar (I : ToricInput n) :
    ContDiff ℝ ∞ (tailoringEtaScalar I) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem tailoringEta_eq (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringEta I β y =
      tailoringEtaScalar I (Real.sqrt (tailoringSizeSquared I β y.1)) := by
  rw [tailoringEta, tailoringMonomialSize_eq]
  rfl

theorem contDiff_tailoringEta_real (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (fun u : RealSpace n => tailoringEta I β (u, 0)) := by
  simpa only [tailoringEta_eq, Function.comp_def] using
    (contDiff_tailoringEtaScalar I).comp (contDiff_tailoringSize I β)

theorem tailoringEtaScalar_fderiv_hasCompactSupport (I : ToricInput n) :
    HasCompactSupport (fderiv ℝ (tailoringEtaScalar I)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Icc (tailoringSmallConstant I) (2 * tailoringSmallConstant I)))
  intro x hx
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have he : tailoringEtaScalar I =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.le)
        (tailoringSmallConstant_pos I).le
    rw [he.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := ℝ) (0 : ℝ)) x
  · have he : tailoringEtaScalar I =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (tailoringSmallConstant_pos I)]
      linarith
    rw [he.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := ℝ) (1 : ℝ)) x

/-- The fixed scalar transition has a globally bounded differential. -/
theorem tailoringEtaScalar_exists_fderiv_bound (I : ToricInput n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r, ‖fderiv ℝ (tailoringEtaScalar I) r‖ ≤ D := by
  obtain ⟨D, hD, hb⟩ := (tailoringEtaScalar_fderiv_hasCompactSupport I).exists_bound_iteratedFDeriv
      ((contDiff_tailoringEtaScalar I).fderiv_right (by simp)) 0
  refine ⟨D, hD, fun r => ?_⟩
  simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl r

theorem fderiv_tailoringEta_real_eq_zero_of_plateau (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (h : tailoringEta I β (u, 0) = 0 ∨ tailoringEta I β (u, 0) = 1) :
    fderiv ℝ (fun u : RealSpace n => tailoringEta I β (u, 0)) u = 0 := by
  rcases h with h | h
  · apply IsLocalMin.fderiv_eq_zero
    exact Eventually.of_forall (fun y => by dsimp only; rw [h]; exact tailoringEta_nonneg I β (y, 0))
  · apply IsLocalMax.fderiv_eq_zero
    exact Eventually.of_forall (fun y => by dsimp only; rw [h]; exact tailoringEta_le_one I β (y, 0))

/-- A single bound for the derivative of the literal `η(S)`, independent of `β,u`. -/
theorem tailoringEta_exists_uniform_fderiv_bound (I : ToricInput n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (β : ℝ) (u : RealSpace n),
      ‖fderiv ℝ (fun u : RealSpace n => tailoringEta I β (u, 0)) u‖ ≤ D := by
  obtain ⟨D, hD, hb⟩ := tailoringEtaScalar_exists_fderiv_bound I
  have hL := tailoringPairingBound_pos I
  have hc := tailoringSmallConstant_pos I
  refine ⟨D * tailoringPairingBound I * (2 * tailoringSmallConstant I),
    by positivity, fun β u => ?_⟩
  by_cases h : tailoringEta I β (u, 0) = 0 ∨ tailoringEta I β (u, 0) = 1
  · rw [fderiv_tailoringEta_real_eq_zero_of_plateau I β u h, norm_zero]
    positivity
  have hS : Real.sqrt (tailoringSizeSquared I β u) ≤ 2 * tailoringSmallConstant I := by
    have hn : tailoringEta I β (u, 0) ≠ 1 := fun he => h (Or.inr he)
    have := lt_of_not_ge (fun he => hn ((tailoringEta_eq_one_iff I β (u, 0)).mpr he))
    rw [tailoringMonomialSize_eq] at this
    exact this.le
  have he : (fun u : RealSpace n => tailoringEta I β (u, 0)) =
      tailoringEtaScalar I ∘ (fun u => Real.sqrt (tailoringSizeSquared I β u)) := by
    funext y
    exact tailoringEta_eq I β (y, 0)
  rw [he, fderiv_comp u
    ((contDiff_tailoringEtaScalar I).differentiable (by simp) _)
    ((contDiff_tailoringSize I β).differentiable (by simp) u)]
  calc
    _ ≤ ‖fderiv ℝ (tailoringEtaScalar I) (Real.sqrt (tailoringSizeSquared I β u))‖ *
      ‖fderiv ℝ (fun u => Real.sqrt (tailoringSizeSquared I β u)) u‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ D * (tailoringPairingBound I * Real.sqrt (tailoringSizeSquared I β u)) :=
      mul_le_mul (hb _) (norm_fderiv_tailoringSize_le I β u) (norm_nonneg _)
        hD
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hS (by positivity)

theorem tailoringMonomialSize_le_card_mul_max (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    tailoringMonomialSize I β y ≤ I.vertices.card * Real.exp (supportHeight I y.1 - β) := by
  have hN : 1 ≤ I.vertices.card := I.vertices_nonempty.card_pos
  have hM (v : Lattice n) (hv : v ∈ I.vertices) :
      Real.exp (tailoringWeight β v y.1) ≤ Real.exp (supportHeight I y.1 - β) := by
    rw [tailoringWeight_vertex I β ⟨v, hv⟩]
    exact Real.exp_le_exp.mpr (sub_le_sub_right (I.pairing_le_supportHeight y.1 ⟨v, hv⟩) β)
  rw [tailoringMonomialSize_eq]
  apply (Real.sqrt_le_left (by positivity)).mpr
  calc
    _ ≤ ∑ _v ∈ I.vertices, Real.exp (supportHeight I y.1 - β) ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      exact pow_le_pow_left₀ (Real.exp_pos _).le (hM v hv) 2
    _ = I.vertices.card * Real.exp (supportHeight I y.1 - β) ^ 2 := by simp
    _ ≤ _ := by
      have hN' : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast hN
      have := mul_le_mul_of_nonneg_right hN' (sq_nonneg (Real.exp (supportHeight I y.1 - β)))
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg I.vertices.card : (0:ℝ) ≤ _)
      nlinarith

end FsFltz
