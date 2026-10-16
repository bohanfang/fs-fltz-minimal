import FsFltz.Analysis.TailoringCutoffs
import FsFltz.SmoothTorus

/-!
# The literal finite tailoring family

Source: `geometric-part-fsf-proof.tex`, `eq:fs`, lines 1098–1120.
The normalized monomials, the small-monomial cutoff and the family are actual
functions on the quotient torus. The endpoint fiber identity is a set equality;
no regularity or Liouville comparison is built into its statement.
-/

noncomputable section

open scoped BigOperators Manifold ContDiff

namespace FsFltz

variable {n : ℕ}

def tailoringSmallConstant (I : ToricInput n) : ℝ :=
  1 / (8 * (I.vertices.card + 1))

theorem tailoringSmallConstant_pos (I : ToricInput n) : 0 < tailoringSmallConstant I := by
  unfold tailoringSmallConstant
  positivity

theorem tailoringSmallConstant_size (I : ToricInput n) :
    4 * I.vertices.card * tailoringSmallConstant I < 1 := by
  unfold tailoringSmallConstant
  have hn : (0 : ℝ) ≤ I.vertices.card := Nat.cast_nonneg _
  rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]
  linarith

theorem two_mul_tailoringSmallConstant_lt_one (I : ToricInput n) :
    2 * tailoringSmallConstant I < 1 := by
  unfold tailoringSmallConstant
  have hn : (0 : ℝ) ≤ I.vertices.card := Nat.cast_nonneg _
  rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]
  linarith

/-- The source's Euclidean norm of the vector of normalized monomials. -/
def tailoringMonomialSize (I : ToricInput n) (β : ℝ) (y : LGSpace n) : ℝ :=
  Real.sqrt (∑ v ∈ I.vertices, ‖monomial (Real.exp (-β) : ℂ) v y‖ ^ 2)

theorem norm_monomial_le_tailoringMonomialSize (I : ToricInput n) (β : ℝ)
    {v : Lattice n} (hv : v ∈ I.vertices) (y : LGSpace n) :
    ‖monomial (Real.exp (-β) : ℂ) v y‖ ≤ tailoringMonomialSize I β y := by
  change _ ≤ Real.sqrt _
  apply (Real.le_sqrt (norm_nonneg _)
    (Finset.sum_nonneg fun a (_ha : a ∈ I.vertices) =>
      sq_nonneg ‖monomial (Real.exp (-β) : ℂ) a y‖)).mpr
  exact Finset.single_le_sum
    (fun a (_ha : a ∈ I.vertices) => sq_nonneg ‖monomial (Real.exp (-β) : ℂ) a y‖) hv

/-- A fixed smooth scalar transition, evaluated at the actual size `S`. -/
def tailoringEta (I : ToricInput n) (β : ℝ) (y : LGSpace n) : ℝ :=
  Real.smoothTransition
    ((tailoringMonomialSize I β y - tailoringSmallConstant I) / tailoringSmallConstant I)

theorem tailoringEta_nonneg (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    0 ≤ tailoringEta I β y := Real.smoothTransition.nonneg _

theorem tailoringEta_le_one (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringEta I β y ≤ 1 := Real.smoothTransition.le_one _

theorem tailoringEta_eq_one_iff (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringEta I β y = 1 ↔ 2 * tailoringSmallConstant I ≤ tailoringMonomialSize I β y := by
  rw [tailoringEta, Real.smoothTransition.eq_one_iff_one_le,
    le_div_iff₀ (tailoringSmallConstant_pos I)]
  constructor <;> intro h <;> linarith

theorem tailoringEta_eq_zero_iff (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringEta I β y = 0 ↔ tailoringMonomialSize I β y ≤ tailoringSmallConstant I := by
  rw [tailoringEta, Real.smoothTransition.zero_iff_nonpos,
    div_le_iff₀ (tailoringSmallConstant_pos I)]
  simp

/-- The normalized polynomial at the coefficient-one endpoint. -/
def tailoringOriginal (I : ToricInput n) (β : ℝ) (y : LGSpace n) : ℂ :=
  ∑ v ∈ I.vertices, monomial (Real.exp (-β) : ℂ) v y

/-- The defining function of the tailored hypersurface `Hβ`. -/
def tailoringEquation (I : ToricInput n) (β : ℝ) (y : LGSpace n) : ℂ :=
  -(tailoringCutoff I β 0 y.1 : ℂ) +
    ∑ v ∈ I.vertices, (tailoringCutoff I β v y.1 : ℂ) * monomial (Real.exp (-β) : ℂ) v y

/-- The precise homotopy in `eq:fs`, including the small-monomial cutoff. -/
def tailoringFamily (I : ToricInput n) (β s : ℝ) (y : LGSpace n) : ℂ :=
  tailoringOriginal I β y + (s * tailoringEta I β y : ℝ) *
    ((1 - (tailoringCutoff I β 0 y.1 : ℂ)) +
      ∑ v ∈ I.vertices, ((tailoringCutoff I β v y.1 : ℂ) - 1) *
        monomial (Real.exp (-β) : ℂ) v y)

@[simp] theorem tailoringFamily_zero (I : ToricInput n) (β : ℝ) (y : LGSpace n) :
    tailoringFamily I β 0 y = tailoringOriginal I β y := by
  simp [tailoringFamily]

theorem tailoringCutoff_zero_eq_one_of_eta_ne_one (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hη : tailoringEta I β y ≠ 1) : tailoringCutoff I β 0 y.1 = 1 := by
  have hS : tailoringMonomialSize I β y < 2 * tailoringSmallConstant I :=
    lt_of_not_ge (fun h => hη ((tailoringEta_eq_one_iff I β y).mpr h))
  apply tailoringCutoff_eq_one_of_maximal
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact le_rfl
  rw [tailoringWeight_zero]
  have hm : ‖monomial (Real.exp (-β) : ℂ) a y‖ < 1 :=
    (norm_monomial_le_tailoringMonomialSize I β ha y).trans_lt
      (hS.trans (two_mul_tailoringSmallConstant_lt_one I))
  rw [norm_tailoring_monomial I β ⟨a, ha⟩ y] at hm
  exact (Real.exp_lt_one_iff.mp hm).le

theorem norm_tailoring_weighted_sum_le (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (w : Lattice n → ℝ) (hw : ∀ v ∈ I.vertices, 0 ≤ w v ∧ w v ≤ 1) :
    ‖∑ v ∈ I.vertices, (w v : ℂ) * monomial (Real.exp (-β) : ℂ) v y‖ ≤
      I.vertices.card * tailoringMonomialSize I β y := by
  calc
    _ ≤ ∑ v ∈ I.vertices, ‖(w v : ℂ) * monomial (Real.exp (-β) : ℂ) v y‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ I.vertices, tailoringMonomialSize I β y := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw v hv).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw v hv).2).trans
        (norm_monomial_le_tailoringMonomialSize I β hv y)
    _ = _ := by simp

theorem norm_tailoring_weighted_sum_lt_one_of_eta_ne_one (I : ToricInput n)
    (β : ℝ) (y : LGSpace n) (hη : tailoringEta I β y ≠ 1)
    (w : Lattice n → ℝ) (hw : ∀ v ∈ I.vertices, 0 ≤ w v ∧ w v ≤ 1) :
    ‖∑ v ∈ I.vertices, (w v : ℂ) * monomial (Real.exp (-β) : ℂ) v y‖ < 1 := by
  have hS : tailoringMonomialSize I β y ≤ 2 * tailoringSmallConstant I :=
    (lt_of_not_ge (fun h => hη ((tailoringEta_eq_one_iff I β y).mpr h))).le
  apply (norm_tailoring_weighted_sum_le I β y w hw).trans_lt
  have hN : (0 : ℝ) ≤ I.vertices.card := Nat.cast_nonneg _
  have hc := tailoringSmallConstant_pos I
  have hb := tailoringSmallConstant_size I
  have hs := mul_le_mul_of_nonneg_left hS hN
  nlinarith

theorem tailoringFamily_weighted_sum (I : ToricInput n) (β s : ℝ) (y : LGSpace n) :
    tailoringFamily I β s y =
      (s * tailoringEta I β y : ℝ) * (1 - (tailoringCutoff I β 0 y.1 : ℂ)) +
      ∑ v ∈ I.vertices, ((1 + s * tailoringEta I β y *
        (tailoringCutoff I β v y.1 - 1) : ℝ) : ℂ) * monomial (Real.exp (-β) : ℂ) v y := by
  have hs : (∑ v ∈ I.vertices, ((1 + s * tailoringEta I β y *
      (tailoringCutoff I β v y.1 - 1) : ℝ) : ℂ) * monomial (Real.exp (-β) : ℂ) v y) =
      tailoringOriginal I β y + (s * tailoringEta I β y : ℝ) *
        ∑ v ∈ I.vertices, ((tailoringCutoff I β v y.1 : ℂ) - 1) *
          monomial (Real.exp (-β) : ℂ) v y := by
    unfold tailoringOriginal
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    push_cast
    ring
  rw [hs]
  unfold tailoringFamily
  ring

theorem tailoringFamily_weight_mem_Icc (I : ToricInput n) (β : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : LGSpace n) (v : Lattice n) :
    0 ≤ 1 + s * tailoringEta I β y * (tailoringCutoff I β v y.1 - 1) ∧
      1 + s * tailoringEta I β y * (tailoringCutoff I β v y.1 - 1) ≤ 1 := by
  have hη0 := tailoringEta_nonneg I β y
  have hη1 := tailoringEta_le_one I β y
  have hχ0 := tailoringCutoff_nonneg I β v y.1
  have hχ1 := tailoringCutoff_le_one I β v y.1
  have ht0 : 0 ≤ s * tailoringEta I β y := mul_nonneg hs.1 hη0
  have ht1 : s * tailoringEta I β y ≤ 1 :=
    (mul_le_mul_of_nonneg_left hη1 hs.1).trans (by simpa using hs.2)
  have hp0 := mul_nonneg ht0 hχ0
  have hp1 := mul_le_mul_of_nonneg_left hχ1 ht0
  constructor <;> nlinarith

theorem norm_tailoringFamily_lt_one_of_eta_ne_one (I : ToricInput n) (β : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (y : LGSpace n)
    (hη : tailoringEta I β y ≠ 1) : ‖tailoringFamily I β s y‖ < 1 := by
  rw [tailoringFamily_weighted_sum, tailoringCutoff_zero_eq_one_of_eta_ne_one I β y hη]
  simp only [Complex.ofReal_one, sub_self, mul_zero, zero_add]
  exact norm_tailoring_weighted_sum_lt_one_of_eta_ne_one I β y hη _
    (fun v _ => tailoringFamily_weight_mem_Icc I β hs y v)

theorem tailoringEquation_ne_zero_of_eta_ne_one (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hη : tailoringEta I β y ≠ 1) : tailoringEquation I β y ≠ 0 := by
  have hb := norm_tailoring_weighted_sum_lt_one_of_eta_ne_one I β y hη
    (fun v => tailoringCutoff I β v y.1)
    (fun v _ => ⟨tailoringCutoff_nonneg I β v y.1, tailoringCutoff_le_one I β v y.1⟩)
  intro he
  unfold tailoringEquation at he
  rw [tailoringCutoff_zero_eq_one_of_eta_ne_one I β y hη] at he
  have he' : (∑ v ∈ I.vertices, (tailoringCutoff I β v y.1 : ℂ) *
      monomial (Real.exp (-β) : ℂ) v y) = 1 := by
    simp only [Complex.ofReal_one] at he
    linear_combination he
  rw [he'] at hb
  norm_num at hb

theorem tailoringFamily_one_sub_one_of_eta_eq_one (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hη : tailoringEta I β y = 1) :
    tailoringFamily I β 1 y - 1 = tailoringEquation I β y := by
  rw [tailoringFamily_weighted_sum, hη]
  simp only [mul_one, one_mul, add_sub_cancel, Complex.ofReal_one]
  unfold tailoringEquation
  ring

/-- The endpoint's entire fiber, with the actual small-monomial cutoff,
is exactly the hypersurface defined by the all-pairs cutoffs. -/
theorem tailoringFamily_one_fiber (I : ToricInput n) (β : ℝ) :
    {y : LGSpace n | tailoringFamily I β 1 y = 1} =
      {y : LGSpace n | tailoringEquation I β y = 0} := by
  ext y
  change tailoringFamily I β 1 y = 1 ↔ tailoringEquation I β y = 0
  by_cases hη : tailoringEta I β y = 1
  · rw [← tailoringFamily_one_sub_one_of_eta_eq_one I β y hη, sub_eq_zero]
  · have hf := norm_tailoringFamily_lt_one_of_eta_ne_one I β
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) y hη
    have hf' : tailoringFamily I β 1 y ≠ 1 := by
      intro he
      rw [he] at hf
      norm_num at hf
    exact iff_of_false hf' (tailoringEquation_ne_zero_of_eta_ne_one I β y hη)

/-- The apparent norm in `S` is smooth: its square is a strictly positive
finite sum of exponentials in the real quotient coordinates. -/
theorem contMDiff_tailoringMonomialSize (I : ToricInput n) (β : ℝ) :
    ContMDiff (lgModel n) 𝓘(ℝ, ℝ) ∞ (tailoringMonomialSize I β) := by
  let f : RealSpace n → ℝ := fun u =>
    ∑ v ∈ I.vertices, (Real.exp (tailoringWeight β v u)) ^ 2
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f, tailoringWeight, pairing]
    fun_prop
  have hp : ∀ u, f u ≠ 0 := by
    intro u
    exact ne_of_gt (Finset.sum_pos (fun v _ => sq_pos_of_pos (Real.exp_pos _))
      I.vertices_nonempty)
  have hs : ContMDiff (lgModel n) 𝓘(ℝ, ℝ) ∞
      (fun y : LGSpace n => Real.sqrt (f y.1)) :=
    (hf.sqrt hp).contMDiff.comp contMDiff_fst
  apply hs.congr
  intro y
  unfold tailoringMonomialSize
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [norm_tailoring_monomial I β ⟨v, hv⟩ y]

theorem contMDiff_tailoringEta (I : ToricInput n) (β : ℝ) :
    ContMDiff (lgModel n) 𝓘(ℝ, ℝ) ∞ (tailoringEta I β) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ =>
      Real.smoothTransition ((x - tailoringSmallConstant I) / tailoringSmallConstant I)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  exact h.contMDiff.comp (contMDiff_tailoringMonomialSize I β)

/-- Joint smoothness of the actual parameterized family on the quotient,
including its small-monomial transition. -/
theorem contMDiff_tailoringFamily (I : ToricInput n) (β : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2) := by
  have hmul {f g : ℝ × LGSpace n → ℂ}
      (hf : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ f)
      (hg : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ g) :
      ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞ (fun p => f p * g p) :=
    (show ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).contMDiff.comp (hf.prodMk_space hg)
  have hm (v : Lattice n) : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => monomial (Real.exp (-β) : ℂ) v p.2) :=
    (contMDiff_monomial _ v).comp contMDiff_snd
  have hc (v : Lattice n) : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × LGSpace n => (tailoringCutoff I β v p.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp
      (((tailoringCutoff_contDiff I β v).contMDiff.comp contMDiff_fst).comp contMDiff_snd)
  have hη : ContMDiff (𝓘(ℝ, ℝ).prod (lgModel n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => p.1 * tailoringEta I β p.2) :=
    (show ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).contMDiff.comp
      (contMDiff_fst.prodMk_space ((contMDiff_tailoringEta I β).comp contMDiff_snd))
  exact (ContMDiff.sum (fun v _ => hm v)).add
    (hmul (Complex.ofRealCLM.contDiff.contMDiff.comp hη)
      ((contMDiff_const.sub (hc 0)).add
        (ContMDiff.sum (fun v _ => hmul ((hc v).sub contMDiff_const) (hm v)))))

end FsFltz
