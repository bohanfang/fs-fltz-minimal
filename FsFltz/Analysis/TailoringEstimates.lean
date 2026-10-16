import FsFltz.Analysis.TailoringSizeEstimates
import FsFltz.Geometry.QuotientFormBridge

/-!
# The C¹ error of the literal tailoring family

Source: `geometric-part-fsf-proof.tex`, `eq:fs` and `eq:C1`, lines 1100–1114.
The differential is the actual Fréchet derivative on logarithmic covering
coordinates of the existing quotient family. All constants precede `β,s,u`.
-/

noncomputable section

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

/-- The literal correction bracket in `eq:fs`. -/
def tailoringCorrection (I : ToricInput n) (β : ℝ) (y : LGSpace n) : ℂ :=
  (1 - (tailoringCutoff I β 0 y.1 : ℂ)) +
    ∑ v ∈ I.vertices, ((tailoringCutoff I β v y.1 : ℂ) - 1) *
      monomial (Real.exp (-β) : ℂ) v y

theorem tailoringFamily_sub_original (I : ToricInput n) (β s : ℝ) (y : LGSpace n) :
    tailoringFamily I β s y - tailoringOriginal I β y =
      (s * tailoringEta I β y : ℝ) * tailoringCorrection I β y := by
  unfold tailoringFamily tailoringCorrection
  ring

private theorem norm_cutoff_sub_one_le (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n) :
    ‖(tailoringCutoff I β a u : ℂ) - 1‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (tailoringCutoff_le_one I β a u))]
  have := tailoringCutoff_nonneg I β a u
  linarith

private theorem norm_changed_monomial_le (I : ToricInput n) (β : ℝ)
    (v : Lattice n) (hv : v ∈ I.vertices) (y : LGSpace n) :
    ‖((tailoringCutoff I β v y.1 : ℂ) - 1) * monomial (Real.exp (-β) : ℂ) v y‖ ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β)) := by
  by_cases hc : tailoringCutoff I β v y.1 = 1
  · simp only [hc, Complex.ofReal_one, sub_self, zero_mul, norm_zero]
    positivity
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_cutoff_sub_one_le I β v y.1)).trans
    (by rw [norm_tailoring_monomial I β ⟨v, hv⟩ y]
        exact tailoringCutoff_changed_exp_bound I β v y.1 (Or.inl hc))

private theorem norm_changed_constant_le (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    ‖1 - (tailoringCutoff I β 0 u : ℂ)‖ ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I u - β)) := by
  by_cases hc : tailoringCutoff I β 0 u = 1
  · simp only [hc, Complex.ofReal_one, sub_self, norm_zero]
    positivity
  have hb := tailoringCutoff_changed_exp_bound I β 0 u (Or.inl hc)
  simp only [tailoringWeight_zero, Real.exp_zero] at hb
  have hn : ‖1 - (tailoringCutoff I β 0 u : ℂ)‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact norm_cutoff_sub_one_le I β 0 u
  exact hn.trans hb

theorem norm_tailoringCorrection_le (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    ‖tailoringCorrection I β y‖ ≤ (I.vertices.card + 1) *
      (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β))) := by
  calc
    _ ≤ ‖1 - (tailoringCutoff I β 0 y.1 : ℂ)‖ +
      ‖∑ v ∈ I.vertices, ((tailoringCutoff I β v y.1 : ℂ) - 1) *
        monomial (Real.exp (-β) : ℂ) v y‖ := norm_add_le _ _
    _ ≤ Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β)) +
      ∑ _v ∈ I.vertices, Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I y.1 - β)) :=
      add_le_add (norm_changed_constant_le I β y.1)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => norm_changed_monomial_le I β v hv y)))
    _ = _ := by simp; ring

private def cutoffCover (I : ToricInput n) (β : ℝ) (a : Lattice n)
    (x : TangentCoordinates n) : ℂ := (tailoringCutoff I β a x.1 : ℂ)

private theorem contDiff_cutoffCover (I : ToricInput n) (β : ℝ) (a : Lattice n) :
    ContDiff ℝ ∞ (cutoffCover I β a) :=
  Complex.ofRealCLM.contDiff.comp ((tailoringCutoff_contDiff I β a).comp contDiff_fst)

private theorem fderiv_cutoffCover (I : ToricInput n) (β : ℝ) (a : Lattice n)
    (x : TangentCoordinates n) :
    fderiv ℝ (cutoffCover I β a) x = Complex.ofRealCLM.comp
      ((fderiv ℝ (tailoringCutoff I β a) x.1).comp
        (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))) := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp x
    (((tailoringCutoff_contDiff I β a).differentiable (by simp) x.1).hasFDerivAt.comp x
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).hasFDerivAt)).fderiv

private theorem norm_fderiv_cutoffCover_le (I : ToricInput n) (β : ℝ) (a : Lattice n)
    (x : TangentCoordinates n) {D : ℝ}
    (hb : ‖fderiv ℝ (tailoringCutoff I β a) x.1‖ ≤ D) :
    ‖fderiv ℝ (cutoffCover I β a) x‖ ≤ ‖Complex.ofRealCLM‖ * D := by
  rw [fderiv_cutoffCover]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le _ _ _))).trans hb

private theorem contDiff_monomialCover (β : ℝ) (v : Lattice n) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => monomial (Real.exp (-β) : ℂ) v (lgCover x)) := by
  have he : (fun x : TangentCoordinates n => monomial (Real.exp (-β) : ℂ) v (lgCover x)) =
      (fun x => (Real.exp (-β) : ℂ) * Complex.exp (exponentLinearMap v x)) := by
    funext x
    simp only [lgCover, monomial_angleQuotient, exponentLinearMap_eq_pairing, mul_comm Complex.I]
  rw [he]
  exact contDiff_const.mul (Complex.contDiff_exp.comp (exponentLinearMap v).contDiff)

private theorem norm_fderiv_changed_monomial_le (I : ToricInput n) (β : ℝ)
    (v : Lattice n) (hv : v ∈ I.vertices) (x : TangentCoordinates n)
    {D : ℝ} (hD : 0 ≤ D)
    (hb : ‖fderiv ℝ (tailoringCutoff I β v) x.1‖ ≤ D) :
    ‖fderiv ℝ (fun z : TangentCoordinates n => (cutoffCover I β v z - 1) *
      monomial (Real.exp (-β) : ℂ) v (lgCover z)) x‖ ≤
      (‖exponentLinearMap v‖ + ‖Complex.ofRealCLM‖ * D) *
        (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))) := by
  have hc := (contDiff_cutoffCover I β v).differentiable (by simp) x
  have hm := hasFDerivAt_monomial_representatives (Real.exp (-β) : ℂ) v x
  have he := ((hc.hasFDerivAt.sub_const 1).mul hm).fderiv
  change fderiv ℝ (fun z : TangentCoordinates n => (cutoffCover I β v z - 1) *
    monomial (Real.exp (-β) : ℂ) v (lgCover z)) x = _ at he
  rw [he]
  by_cases hχ : tailoringCutoff I β v x.1 = 1
  · have hz := tailoringCutoff_fderiv_eq_zero_of_eq_one I β v x.1 hχ
    rw [fderiv_cutoffCover, hz]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, cutoffCover, hχ, Complex.ofReal_one, sub_self,
      norm_zero, zero_mul, mul_zero, add_zero]
    positivity
  have hs : ‖monomial (Real.exp (-β) : ℂ) v (lgCover x)‖ ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β)) := by
    rw [norm_tailoring_monomial I β ⟨v, hv⟩ (lgCover x)]
    exact tailoringCutoff_changed_exp_bound I β v x.1 (Or.inl hχ)
  calc
    _ ≤ ‖(cutoffCover I β v x - 1) •
      (monomial (Real.exp (-β) : ℂ) v (lgCover x) • exponentLinearMap v)‖ +
      ‖monomial (Real.exp (-β) : ℂ) v (lgCover x) • fderiv ℝ (cutoffCover I β v) x‖ := norm_add_le _ _
    _ ≤ 1 * (‖monomial (Real.exp (-β) : ℂ) v (lgCover x)‖ * ‖exponentLinearMap v‖) +
      ‖monomial (Real.exp (-β) : ℂ) v (lgCover x)‖ * (‖Complex.ofRealCLM‖ * D) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right (norm_cutoff_sub_one_le I β v x.1) (by positivity))
        (mul_le_mul_of_nonneg_left (norm_fderiv_cutoffCover_le I β v x hb) (norm_nonneg _))
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hs (show 0 ≤ ‖exponentLinearMap v‖ + ‖Complex.ofRealCLM‖ * D by positivity)
      nlinarith

private theorem contDiff_tailoringCorrection_cover (I : ToricInput n) (β : ℝ) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => tailoringCorrection I β (lgCover x)) := by
  exact (contDiff_const.sub (contDiff_cutoffCover I β 0)).add
    (ContDiff.sum (fun v _ => ((contDiff_cutoffCover I β v).sub contDiff_const).mul
      (contDiff_monomialCover β v)))

private theorem norm_fderiv_changed_constant_le (I : ToricInput n) (β : ℝ)
    (x : TangentCoordinates n) {D : ℝ} (hD : 0 ≤ D)
    (hb : ‖fderiv ℝ (tailoringCutoff I β 0) x.1‖ ≤ D) :
    ‖fderiv ℝ (fun z : TangentCoordinates n => 1 - cutoffCover I β 0 z) x‖ ≤
      (‖Complex.ofRealCLM‖ * D) *
        (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))) := by
  rw [fderiv_const_sub, norm_neg]
  by_cases hχ : tailoringCutoff I β 0 x.1 = 1
  · rw [fderiv_cutoffCover, tailoringCutoff_fderiv_eq_zero_of_eq_one I β 0 x.1 hχ]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, norm_zero]
    positivity
  have hs := tailoringCutoff_changed_exp_bound I β 0 x.1 (Or.inl hχ)
  simp only [tailoringWeight_zero, Real.exp_zero] at hs
  exact (norm_fderiv_cutoffCover_le I β 0 x hb).trans
    (le_mul_of_one_le_right (by positivity) hs)

/-- The entire literal correction bracket has a differential bounded by
`C exp(-sqrt β) max(1,M)` in covering coordinates. -/
theorem tailoringCorrection_exists_uniform_fderiv_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (x : TangentCoordinates n),
      ‖fderiv ℝ (fun z : TangentCoordinates n => tailoringCorrection I β (lgCover z)) x‖ ≤
        C * (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))) := by
  obtain ⟨D, hD, hb⟩ := tailoringCutoffs_exists_uniform_bound_iteratedFDeriv I 1
  have hd (β : ℝ) (a : Lattice n) (ha : a ∈ tailoringExponents I) (u : RealSpace n) :
      ‖fderiv ℝ (tailoringCutoff I β a) u‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using hb β a ha u
  let C := ‖Complex.ofRealCLM‖ * D +
    ∑ v ∈ I.vertices, (‖exponentLinearMap v‖ + ‖Complex.ofRealCLM‖ * D)
  refine ⟨C, add_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => by positivity)), fun β x => ?_⟩
  have hterm (v : Lattice n) : DifferentiableAt ℝ (fun z : TangentCoordinates n =>
      (cutoffCover I β v z - 1) * monomial (Real.exp (-β) : ℂ) v (lgCover z)) x :=
    (((contDiff_cutoffCover I β v).sub contDiff_const).mul
      (contDiff_monomialCover β v)).differentiable (by simp) x
  have hc : DifferentiableAt ℝ (fun z : TangentCoordinates n => 1 - cutoffCover I β 0 z) x :=
    (contDiff_const.sub (contDiff_cutoffCover I β 0)).differentiable (by simp) x
  have hder := (hc.hasFDerivAt.add (HasFDerivAt.fun_sum (u := I.vertices)
    (fun v _ => (hterm v).hasFDerivAt))).fderiv
  change fderiv ℝ (fun z : TangentCoordinates n => tailoringCorrection I β (lgCover z)) x = _ at hder
  rw [hder]
  calc
    _ ≤ ‖fderiv ℝ (fun z => 1 - cutoffCover I β 0 z) x‖ +
      ∑ v ∈ I.vertices, ‖fderiv ℝ (fun z => (cutoffCover I β v z - 1) *
        monomial (Real.exp (-β) : ℂ) v (lgCover z)) x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (‖Complex.ofRealCLM‖ * D) *
        (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))) +
      ∑ v ∈ I.vertices, (‖exponentLinearMap v‖ + ‖Complex.ofRealCLM‖ * D) *
        (Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))) := by
      apply add_le_add
      · exact norm_fderiv_changed_constant_le I β x hD
          (hd β 0 (Finset.mem_insert_self _ _) x.1)
      · apply Finset.sum_le_sum
        intro v hv
        exact norm_fderiv_changed_monomial_le I β v hv x hD
          (hd β v (Finset.mem_insert_of_mem hv) x.1)
    _ = _ := by rw [← Finset.sum_mul, ← add_mul]

private theorem max_le_mul_monomial_of_eta_ne_zero (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hη : tailoringEta I β y ≠ 0) :
    max 1 (Real.exp (supportHeight I y.1 - β)) ≤
      (1 + I.vertices.card / tailoringSmallConstant I) * Real.exp (supportHeight I y.1 - β) := by
  have hc := tailoringSmallConstant_pos I
  have hM := Real.exp_pos (supportHeight I y.1 - β)
  have hS : tailoringSmallConstant I < tailoringMonomialSize I β y :=
    lt_of_not_ge (fun h => hη ((tailoringEta_eq_zero_iff I β y).mpr h))
  have hSM := tailoringMonomialSize_le_card_mul_max I β y
  have hNM : 1 ≤ I.vertices.card * Real.exp (supportHeight I y.1 - β) /
      tailoringSmallConstant I := by
    rw [le_div_iff₀ hc]
    linarith
  apply max_le
  · have he : I.vertices.card * Real.exp (supportHeight I y.1 - β) /
        tailoringSmallConstant I = (I.vertices.card / tailoringSmallConstant I) *
          Real.exp (supportHeight I y.1 - β) := by ring
    rw [he] at hNM
    nlinarith
  · have hN : (0 : ℝ) ≤ I.vertices.card / tailoringSmallConstant I := by positivity
    nlinarith

private def etaCover (I : ToricInput n) (β s : ℝ) (x : TangentCoordinates n) : ℂ :=
  (s * tailoringEta I β (lgCover x) : ℝ)

private theorem etaCover_eq (I : ToricInput n) (β s : ℝ) :
    etaCover I β s = fun x : TangentCoordinates n =>
      (s : ℂ) * (tailoringEta I β (x.1, 0) : ℂ) := by
  funext x
  simp only [etaCover, tailoringEta_eq, Complex.ofReal_mul, lgCover]

private theorem contDiff_etaCover (I : ToricInput n) (β s : ℝ) :
    ContDiff ℝ ∞ (etaCover I β s) := by
  rw [etaCover_eq]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((contDiff_tailoringEta_real I β).comp contDiff_fst))

private theorem fderiv_etaCover (I : ToricInput n) (β s : ℝ)
    (x : TangentCoordinates n) :
    fderiv ℝ (etaCover I β s) x = (s : ℂ) • Complex.ofRealCLM.comp
      ((fderiv ℝ (fun u : RealSpace n => tailoringEta I β (u, 0)) x.1).comp
        (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))) := by
  rw [etaCover_eq]
  exact ((Complex.ofRealCLM.hasFDerivAt.comp x
    (((contDiff_tailoringEta_real I β).differentiable (by simp) x.1).hasFDerivAt.comp x
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).hasFDerivAt)).const_mul (s : ℂ)).fderiv

private theorem norm_etaCover_le (I : ToricInput n) (β : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : TangentCoordinates n) : ‖etaCover I β s x‖ ≤ 1 := by
  rw [etaCover, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hs.1 (tailoringEta_nonneg I β (lgCover x)))]
  exact (mul_le_mul_of_nonneg_left (tailoringEta_le_one I β (lgCover x)) hs.1).trans
    (by simpa using hs.2)

private theorem norm_fderiv_etaCover_le (I : ToricInput n) (β : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : TangentCoordinates n) {D : ℝ}
    (hb : ‖fderiv ℝ (fun u : RealSpace n => tailoringEta I β (u, 0)) x.1‖ ≤ D) :
    ‖fderiv ℝ (etaCover I β s) x‖ ≤ ‖Complex.ofRealCLM‖ * D := by
  rw [fderiv_etaCover, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  refine (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le _ _ _))).trans hb

/-- The actual C¹ tailoring error in logarithmic covering coordinates.
The constant is independent of `β`, the point, and the interpolation parameter.
The coordinate maximum norm is used; fixed-dimensional norm equivalence gives
the Euclidean version of the manuscript with a different constant. -/
theorem tailoringFamily_exists_uniform_C1_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
      ∀ x : TangentCoordinates n,
        ‖tailoringFamily I β s (lgCover x) - tailoringOriginal I β (lgCover x)‖ +
          ‖fderiv ℝ (fun z : TangentCoordinates n =>
            tailoringFamily I β s (lgCover z) - tailoringOriginal I β (lgCover z)) x‖ ≤
          C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I x.1 - β) := by
  obtain ⟨B, hB, hb⟩ := tailoringCorrection_exists_uniform_fderiv_bound I
  obtain ⟨D, hD, hd⟩ := tailoringEta_exists_uniform_fderiv_bound I
  let N : ℝ := I.vertices.card + 1
  let A := 1 + I.vertices.card / tailoringSmallConstant I
  let C := N + B + N * (‖Complex.ofRealCLM‖ * D)
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 < A := by dsimp [A]; have := tailoringSmallConstant_pos I; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C * A, mul_pos hC hA, fun β s hs x => ?_⟩
  let e := Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I x.1 - β))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hfun : (fun z : TangentCoordinates n =>
      tailoringFamily I β s (lgCover z) - tailoringOriginal I β (lgCover z)) =
      fun z => etaCover I β s z * tailoringCorrection I β (lgCover z) :=
    funext (fun z => tailoringFamily_sub_original I β s (lgCover z))
  have ha := (contDiff_etaCover I β s).differentiable (by simp) x
  have hc := (contDiff_tailoringCorrection_cover I β).differentiable (by simp) x
  have hp := (ha.hasFDerivAt.mul hc.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => etaCover I β s z * tailoringCorrection I β (lgCover z)) x = _ at hp
  have hnorm : ‖fderiv ℝ (fun z => etaCover I β s z * tailoringCorrection I β (lgCover z)) x‖ ≤
      ‖etaCover I β s x‖ * ‖fderiv ℝ (fun z => tailoringCorrection I β (lgCover z)) x‖ +
      ‖tailoringCorrection I β (lgCover x)‖ * ‖fderiv ℝ (etaCover I β s) x‖ := by
    rw [hp]
    simpa only [norm_smul] using norm_add_le
      (etaCover I β s x • fderiv ℝ (fun z => tailoringCorrection I β (lgCover z)) x)
      (tailoringCorrection I β (lgCover x) • fderiv ℝ (etaCover I β s) x)
  rw [tailoringFamily_sub_original I β s (lgCover x), hfun]
  change ‖etaCover I β s x * tailoringCorrection I β (lgCover x)‖ + _ ≤ _
  by_cases hη : tailoringEta I β (lgCover x) = 0
  · have hu : tailoringEta I β (x.1, 0) = 0 := by
      simpa only [tailoringEta_eq, lgCover] using hη
    have hz : etaCover I β s x = 0 := by simp only [etaCover, hη, mul_zero, Complex.ofReal_zero]
    have hdz : fderiv ℝ (etaCover I β s) x = 0 := by
      rw [fderiv_etaCover, fderiv_tailoringEta_real_eq_zero_of_plateau I β x.1 (Or.inl hu)]
      simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
      apply ContinuousLinearMap.ext
      intro q
      change (s : ℂ) * 0 = 0
      exact mul_zero _
    have hdn : ‖fderiv ℝ (etaCover I β s) x‖ = 0 := by rw [hdz, norm_zero]
    rw [hz, norm_zero, hdn, zero_mul, mul_zero, zero_add] at hnorm
    simp only [hz, zero_mul, norm_zero, zero_add]
    exact hnorm.trans (by positivity)
  have hv : ‖etaCover I β s x * tailoringCorrection I β (lgCover x)‖ ≤ N * e := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_etaCover_le I β hs x)).trans
      (norm_tailoringCorrection_le I β (lgCover x))
  have hdiff : ‖fderiv ℝ (fun z => etaCover I β s z * tailoringCorrection I β (lgCover z)) x‖ ≤
      (B + N * (‖Complex.ofRealCLM‖ * D)) * e := by
    refine hnorm.trans ?_
    calc
      _ ≤ 1 * (B * e) + (N * e) * (‖Complex.ofRealCLM‖ * D) :=
        add_le_add
          (mul_le_mul (norm_etaCover_le I β hs x) (hb β x) (norm_nonneg _) (by norm_num))
          (mul_le_mul (norm_tailoringCorrection_le I β (lgCover x))
            (norm_fderiv_etaCover_le I β hs x (hd β x.1)) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hmax := max_le_mul_monomial_of_eta_ne_zero I β (lgCover x) hη
  calc
    _ ≤ C * e := by dsimp only [C]; nlinarith [hv, hdiff]
    _ ≤ C * (Real.exp (-Real.sqrt β) * (A * Real.exp (supportHeight I x.1 - β))) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
    _ = _ := by ring

end FsFltz
