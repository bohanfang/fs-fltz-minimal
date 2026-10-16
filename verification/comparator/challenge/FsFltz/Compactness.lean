import FsFltz.Regularity
import Mathlib.Topology.Order.Compact

/-!
# Compact quadratic sublevels and the prescribed magnitude maximum

Source: `geoemtric-part-fsf.tex`, `sec:initial`, lines 261–262. The compact
set is a subset of the actual quotient ambient `M_ℝ × T`. Its logarithmic
coordinates lie in a finite Euclidean box and its angle coordinates lie in
the compact period-`2π` torus. Continuity of the quotient-defined `W` then
proves that `sublevelMagnitudeSup` is an attained maximum for every
nonnegative potential level. No end bound or geometric existence assumption
is used.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Compactness of the period-`2π` quotient torus. The positivity instance is
local, avoiding a global instance on arbitrary quotient periods. -/
theorem isCompact_torus_univ : IsCompact (Set.univ : Set (Torus n)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  exact isCompact_univ

/-- The quadratic sublevel contains the zero logarithmic coordinate. -/
theorem phi0_sublevel_nonempty (A : ℝ) (hA : 0 ≤ A) :
    ({y : LGSpace n | phi0 y ≤ A} : Set (LGSpace n)).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  change realSquaredNorm (0 : RealSpace n) / 2 ≤ A
  simpa only [realSquaredNorm, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, zero_div] using hA

/-- Compactness of the actual quadratic potential sublevel. The coordinate
bound is Euclidean, independently of the library's norm on function spaces. -/
theorem isCompact_phi0_sublevel (A : ℝ) (hA : 0 ≤ A) :
    IsCompact {y : LGSpace n | phi0 y ≤ A} := by
  let box : Set (RealSpace n) :=
    {u | ∀ j, u j ∈ Set.Icc (-Real.sqrt (2 * A)) (Real.sqrt (2 * A))}
  have hbox : IsCompact box := isCompact_pi_infinite fun _ => isCompact_Icc
  have hclosed : IsClosed {y : LGSpace n | phi0 y ≤ A} :=
    isClosed_le continuous_phi0 continuous_const
  apply (hbox.prod isCompact_torus_univ).of_isClosed_subset hclosed
  intro y hy
  refine ⟨?_, Set.mem_univ _⟩
  intro j
  have hcoord : (y.1 j) ^ 2 ≤ realSquaredNorm y.1 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (y.1 i)) (Finset.mem_univ j)
  have hsum : realSquaredNorm y.1 ≤ 2 * A := by
    change realSquaredNorm y.1 / 2 ≤ A at hy
    linarith
  have hsqrt : (Real.sqrt (2 * A)) ^ 2 = 2 * A :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hA)
  have habs : |y.1 j| ≤ Real.sqrt (2 * A) := by
    have hsq : (y.1 j) ^ 2 ≤ (Real.sqrt (2 * A)) ^ 2 := by
      rw [hsqrt]
      exact hcoord.trans hsum
    simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using sq_le_sq.mp hsq
  exact abs_le.mp habs

/-- The actual magnitude image is compact, not an unspecified bound set. -/
theorem isCompact_sublevelMagnitudes (I : ToricInput n) (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (sublevelMagnitudes I A) :=
  (isCompact_phi0_sublevel A hA).image (continuous_W I).norm

/-- The magnitude image is nonempty whenever the quadratic level is
nonnegative; this supplies the necessary real-supremum hypothesis. -/
theorem sublevelMagnitudes_nonempty (I : ToricInput n) (A : ℝ) (hA : 0 ≤ A) :
    (sublevelMagnitudes I A).Nonempty :=
  (phi0_sublevel_nonempty (n := n) A hA).image (fun y => ‖W I y‖)

/-- The formula-defined number `M(A)` is an attained maximum on the stated
nonempty compact set (`sec:initial`, lines 261–262). -/
theorem sublevelMaximumAttained (I : ToricInput n) (A : ℝ) (hA : 0 ≤ A) :
    SublevelMaximumAttained I A := by
  have hc := isCompact_sublevelMagnitudes I A hA
  have hne := sublevelMagnitudes_nonempty I A hA
  constructor
  · intro y hy
    exact le_csSup hc.bddAbove ⟨y, hy, rfl⟩
  · obtain ⟨y, hy, heq⟩ := hc.sSup_mem hne
    exact ⟨y, hy, heq⟩

/-- The attained magnitude maximum is nonnegative. -/
theorem sublevelMagnitudeSup_nonneg (I : ToricInput n) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ sublevelMagnitudeSup I A := by
  obtain ⟨y, _, hy⟩ := (sublevelMaximumAttained I A hA).2
  rw [← hy]
  exact norm_nonneg _

end FsFltz
