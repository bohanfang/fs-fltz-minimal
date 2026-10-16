import FsFltz.Analysis.FiniteSupportGrowth

/-!
# Relative exponential tails of the original finite monomial support

Source: `geometric-part-fsf-proof.tex`, `lem:dominant`, lines 703–708:
normalized monomials away from a maximizing face are small. These bounds
derive the coefficient ratio and any requested deficit cutoff from the
original finite input. The dominant-face producer consumes them after
constructing a proper face containing the near-maximal vertices.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Every monomial is bounded by an exponentially small deficit factor
times the actual maximum, with a coefficient-ratio constant derived from
the original finite tuple. -/
theorem ToricInput.exists_monomial_deficit_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n,
      ∀ v : {v : Lattice n // v ∈ I.vertices},
        ‖monomial (I.coeff v) v.val y‖ ≤
          C * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
            maxMonomialMagnitude I y := by
  obtain ⟨A, hA, hcoeff⟩ := I.exists_pos_coeff_lowerBound
  let S : ℝ := ∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖
  have hS : 0 < S := by
    obtain ⟨v, hv⟩ := I.vertices_nonempty
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨⟨v, hv⟩, Finset.mem_univ _, norm_pos_iff.mpr (I.coeff_ne_zero _)⟩
  refine ⟨S / A, div_pos hS hA, ?_⟩
  intro y v
  have hvS : ‖I.coeff v‖ ≤ S :=
    Finset.single_le_sum (f := fun w => ‖I.coeff w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
  obtain ⟨w, hw⟩ := I.supportHeight_attained y.1
  have hM : A * Real.exp (supportHeight I y.1) ≤ maxMonomialMagnitude I y := by
    calc
      A * Real.exp (supportHeight I y.1) ≤ ‖I.coeff w‖ * Real.exp (supportHeight I y.1) :=
        mul_le_mul_of_nonneg_right (hcoeff w) (Real.exp_pos _).le
      _ = ‖monomial (I.coeff w) w.val y‖ := by rw [norm_monomial, hw]
      _ ≤ maxMonomialMagnitude I y := I.norm_monomial_le_maxMonomialMagnitude y w
  have hexp : Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
      Real.exp (supportHeight I y.1) = Real.exp (pairing v.val y.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖monomial (I.coeff v) v.val y‖ = ‖I.coeff v‖ * Real.exp (pairing v.val y.1) :=
      norm_monomial _ _ _
    _ ≤ S * Real.exp (pairing v.val y.1) :=
      mul_le_mul_of_nonneg_right hvS (Real.exp_pos _).le
    _ = S / A * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
        (A * Real.exp (supportHeight I y.1)) := by
      rw [mul_assoc, mul_left_comm _ A, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hA), hexp]
    _ ≤ S / A * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
        maxMonomialMagnitude I y :=
      mul_le_mul_of_nonneg_left hM (by positivity)

/-- Any requested positive relative tolerance is achieved by one positive
pairing-deficit cutoff, uniformly over the ambient and the finite vertices. -/
theorem ToricInput.exists_monomial_tail_cutoff (I : ToricInput n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ y : LGSpace n,
      ∀ v : {v : Lattice n // v ∈ I.vertices},
        D ≤ supportHeight I y.1 - pairing v.val y.1 →
          ‖monomial (I.coeff v) v.val y‖ ≤ ε * maxMonomialMagnitude I y := by
  obtain ⟨C, hC, hbound⟩ := I.exists_monomial_deficit_bound
  refine ⟨max 1 (Real.log (C / ε)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro y v hD
  have hgap : Real.log (C / ε) ≤ supportHeight I y.1 - pairing v.val y.1 :=
    (le_max_right _ _).trans hD
  have hexp : C * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) ≤ ε := by
    calc
      C * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) ≤
          C * Real.exp (-Real.log (C / ε)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hgap)) hC.le
      _ = ε := by
        rw [Real.exp_neg, Real.exp_log (div_pos hC hε)]
        field_simp
  exact (hbound y v).trans
    (mul_le_mul_of_nonneg_right hexp (I.maxMonomialMagnitude_pos y).le)

end FsFltz
