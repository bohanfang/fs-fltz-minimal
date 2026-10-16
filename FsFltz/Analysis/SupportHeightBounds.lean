import FsFltz.Analysis.FiniteSupportGrowth

/-!
# Euclidean support-height bounds for the original finite input

Source: `geometric-part-fsf-proof.tex`, `lem:margin`, lines 753–756:
the support height is comparable to the homogeneous radial coordinate.
Here the original quadratic potential has radial coordinate
`sqrt (realSquaredNorm u)`. The lower bound consumes interior containment;
the upper bound is finite-support Cauchy–Schwarz. No end bound is an input.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Cauchy–Schwarz for the literal lattice/dual pairing and the prescribed
based Euclidean lengths. -/
theorem pairing_le_euclidean_norm_mul (v : Lattice n) (u : RealSpace n) :
    pairing v u ≤ Real.sqrt (realSquaredNorm (latticeReal v)) *
      Real.sqrt (realSquaredNorm u) := by
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

/-- Both support-height bounds are derived from the original finite input.
The positive upper constant is one plus the total finite vertex length. -/
theorem ToricInput.exists_supportHeight_linear_bounds (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ H : ℝ, 0 < H ∧ ∀ u : RealSpace n,
      c * Real.sqrt (realSquaredNorm u) ≤ supportHeight I u ∧
        supportHeight I u ≤ H * Real.sqrt (realSquaredNorm u) := by
  obtain ⟨c, hc, hlow⟩ := I.exists_pairing_ge_euclidean
  let S : ℝ := ∑ v : {v : Lattice n // v ∈ I.vertices},
    Real.sqrt (realSquaredNorm (latticeReal v.val))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  refine ⟨c, hc, 1 + S, by positivity, ?_⟩
  intro u
  constructor
  · obtain ⟨v, hv, hpair⟩ := hlow u
    exact hpair.trans (I.pairing_le_supportHeight u ⟨v, hv⟩)
  · obtain ⟨v, hv⟩ := I.supportHeight_attained u
    rw [← hv]
    have hvS : Real.sqrt (realSquaredNorm (latticeReal v.val)) ≤ S :=
      Finset.single_le_sum
        (f := fun w : {v : Lattice n // v ∈ I.vertices} =>
          Real.sqrt (realSquaredNorm (latticeReal w.val)))
        (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ v)
    calc
      pairing v.val u ≤ Real.sqrt (realSquaredNorm (latticeReal v.val)) *
          Real.sqrt (realSquaredNorm u) := pairing_le_euclidean_norm_mul _ _
      _ ≤ (1 + S) * Real.sqrt (realSquaredNorm u) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end FsFltz
