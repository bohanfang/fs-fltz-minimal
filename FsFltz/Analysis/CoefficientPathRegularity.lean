import FsFltz.Analysis.CoefficientPathEstimates
import FsFltz.Analysis.SupportHeightBounds
import FsFltz.Analysis.OriginalRegularFiber

/-!
# One common regular-value region for the coefficient path

Source: `geometric-part-fsf-proof.tex`, `lem:dominant`, lines 697–709,
and the exceptional-cylinder/critical-value bound at lines 838–856.
Finite coefficient bounds control the whole common cylinder; the proved
uniform dominance excludes critical points outside it. All constants are
chosen before the path parameter and the far complex value.
-/

noncomputable section
open scoped BigOperators Manifold ContDiff

namespace FsFltz

variable {n : ℕ}

/-- The actual polynomial path is uniformly bounded on every radial cylinder. -/
theorem ToricInput.coefficientPath_W_bound_on_radial_cylinder
    (I : ToricInput n) (L : ℝ) :
    ∃ B > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      Real.sqrt (realSquaredNorm y.1) ≤ L → ‖W (I.alongCoefficientPath t) y‖ ≤ B := by
  obtain ⟨A, C, hA, hC, hcoeff⟩ := I.coefficientPath_uniform_norm_bounds
  obtain ⟨c, hc, H, hH, hsupport⟩ := I.exists_supportHeight_linear_bounds
  have hcard : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  refine ⟨(I.vertices.card : ℝ) * C * Real.exp (H * L), by positivity, ?_⟩
  intro t ht y hy
  unfold W
  calc
    ‖∑ v, monomial ((I.alongCoefficientPath t).coeff v) v.val y‖ ≤
        ∑ v : {v : Lattice n // v ∈ I.vertices},
          ‖monomial ((I.alongCoefficientPath t).coeff v) v.val y‖ := norm_sum_le _ _
    _ ≤ ∑ _v : {v : Lattice n // v ∈ I.vertices}, C * Real.exp (H * L) := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_monomial]
      apply mul_le_mul (hcoeff t ht v).2
        (Real.exp_le_exp.mpr ((I.pairing_le_supportHeight y.1 v).trans
          ((hsupport y.1).2.trans (mul_le_mul_of_nonneg_left hy hH.le))))
        (Real.exp_pos _).le hC.le
    _ = _ := by simp [mul_assoc]

/-- One base disk contains all critical values along the entire prescribed path. -/
theorem ToricInput.coefficientPath_a_pos_of_large_value (I : ToricInput n) :
    ∃ B > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      B < ‖W (I.alongCoefficientPath t) y‖ → 0 < a (I.alongCoefficientPath t) y := by
  obtain ⟨L, hL, hpos⟩ := I.coefficientPath_a_pos_on_radial_end
  obtain ⟨B, hB, hbound⟩ := I.coefficientPath_W_bound_on_radial_cylinder L
  refine ⟨B, hB, ?_⟩
  intro t ht y hy
  apply hpos t ht y
  by_contra h
  exact (not_le_of_gt hy) (hbound t ht y (le_of_not_ge h))

namespace Geometry

/-- Every complex value outside one fixed disk is a regular value of every
path member in the native quotient geometry. -/
theorem ToricInput.coefficientPath_far_regular (I : ToricInput n) :
    ∃ B > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : (lgManifold n).Point,
      B < ‖W (I.alongCoefficientPath t) y‖ →
        Function.Surjective (complexDifferential (lgManifold n)
          (W (I.alongCoefficientPath t)) y) := by
  obtain ⟨B, hB, hpos⟩ := I.coefficientPath_a_pos_of_large_value
  exact ⟨B, hB, fun t ht y hy => complexDifferential_W_surjective_of_a_pos
    (I.alongCoefficientPath t) y (hpos t ht y hy)⟩

end Geometry
end FsFltz
