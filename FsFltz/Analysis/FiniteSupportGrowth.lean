import FsFltz.Analytic
import FsFltz.ToricFaces
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Exponential growth of the finite monomial support

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 57–71, and
`geometric-part-fsf-proof.tex`, `lem:dominant`, lines 697–709. The growth
estimate is proved from interior containment and nonzero finite coefficients.
The Euclidean radius is `sqrt (realSquaredNorm u)`, rather than the supremum
norm on the coordinate function space. Gradient noncancellation and the
geometric conclusions of `thm:target` remain separate results.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology

variable {n : ℕ}

/-- The magnitude of a descended monomial is independent of its angle. -/
theorem norm_monomial (c : ℂ) (v : Lattice n) (y : LGSpace n) :
    ‖monomial c v y‖ = ‖c‖ * Real.exp (pairing v y.1) := by
  simp [monomial, Complex.norm_exp, Circle.norm_coe]

/-- Interior containment forces the actual finite coefficient support to be
nonempty, before any maximum or minimum is used. -/
theorem ToricInput.vertices_nonempty (I : ToricInput n) : I.vertices.Nonempty := by
  by_contra h
  have he : I.vertices = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hzero := interior_subset I.zero_interior
  simp [latticePolytope, he] at hzero

/-- The maximum magnitude of the actual finite monomials. The range is finite
and nonempty, and attainment is proved below. -/
def maxMonomialMagnitude (I : ToricInput n) (y : LGSpace n) : ℝ :=
  sSup (Set.range (fun v : {v : Lattice n // v ∈ I.vertices} =>
    ‖monomial (I.coeff v) v.val y‖))

/-- The source's finite maximum is attained by an input monomial. -/
theorem ToricInput.maxMonomialMagnitude_attained (I : ToricInput n) (y : LGSpace n) :
    ∃ v : {v : Lattice n // v ∈ I.vertices},
      ‖monomial (I.coeff v) v.val y‖ = maxMonomialMagnitude I y := by
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  let : Nonempty {v : Lattice n // v ∈ I.vertices} := ⟨⟨v, hv⟩⟩
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

/-- Each monomial norm lies below the attained finite maximum. -/
theorem ToricInput.norm_monomial_le_maxMonomialMagnitude (I : ToricInput n)
    (y : LGSpace n) (v : {v : Lattice n // v ∈ I.vertices}) :
    ‖monomial (I.coeff v) v.val y‖ ≤ maxMonomialMagnitude I y := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨v, rfl⟩

/-- The finite maximum is strictly positive for every point of the original
quotient ambient, since all input coefficients are nonzero. -/
theorem ToricInput.maxMonomialMagnitude_pos (I : ToricInput n) (y : LGSpace n) :
    0 < maxMonomialMagnitude I y := by
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  let w : {v : Lattice n // v ∈ I.vertices} := ⟨v, hv⟩
  have hpos : 0 < ‖monomial (I.coeff w) w.val y‖ := by
    rw [norm_monomial]
    exact mul_pos (norm_pos_iff.mpr (I.coeff_ne_zero w)) (Real.exp_pos _)
  exact hpos.trans_le (I.norm_monomial_le_maxMonomialMagnitude y w)

/-- The finite support height used in the dominant-face and ambient-margin
estimates, computed from the actual input vertices. -/
def supportHeight (I : ToricInput n) (u : RealSpace n) : ℝ :=
  sSup (Set.range (fun v : {v : Lattice n // v ∈ I.vertices} => pairing v.val u))

/-- The finite support height is attained by a vertex. -/
theorem ToricInput.supportHeight_attained (I : ToricInput n) (u : RealSpace n) :
    ∃ v : {v : Lattice n // v ∈ I.vertices}, pairing v.val u = supportHeight I u := by
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  let : Nonempty {v : Lattice n // v ∈ I.vertices} := ⟨⟨v, hv⟩⟩
  exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)

/-- Every vertex pairing lies below the actual finite support height. -/
theorem ToricInput.pairing_le_supportHeight (I : ToricInput n) (u : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices}) : pairing v.val u ≤ supportHeight I u := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨v, rfl⟩

private theorem euclidean_norm_eq (u : RealSpace n) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (realSquaredNorm u) := by
  rw [EuclideanSpace.norm_eq]
  simp [realSquaredNorm, Real.norm_eq_abs]

private theorem pi_norm_le_euclidean (u : RealSpace n) :
    ‖u‖ ≤ Real.sqrt (realSquaredNorm u) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  simpa only [euclidean_norm_eq] using
    (PiLp.norm_apply_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) j)

/-- A uniform Euclidean lower support bound, proved directly from the small
ball furnished by `zero_interior` and the convex-hull supporting inequality.
This is the combinatorial producer of `lem:dominant`'s exponential growth. -/
theorem ToricInput.exists_pairing_ge_euclidean (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : RealSpace n, ∃ v ∈ I.vertices,
      c * Real.sqrt (realSquaredNorm u) ≤ pairing v u := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp I.zero_interior)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro u
  by_cases hu : u = 0
  · obtain ⟨v, hv⟩ := I.vertices_nonempty
    exact ⟨v, hv, by simp [hu, realSquaredNorm, pairing]⟩
  let r := Real.sqrt (realSquaredNorm u)
  have hr : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr hu) (pi_norm_le_euclidean u)
  let x : RealSpace n := (ε / 2 / r) • u
  have hx : x ∈ latticePolytope I.vertices := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    change ‖(ε / 2 / r) • u‖ < ε
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      ε / 2 / r * ‖u‖ ≤ ε / 2 / r * r :=
        mul_le_mul_of_nonneg_left (pi_norm_le_euclidean u) (by positivity)
      _ = ε / 2 := div_mul_cancel₀ _ (ne_of_gt hr)
      _ < ε := half_lt_self hε
  let ℓ : RealSpace n →ₗ[ℝ] ℝ :=
    { toFun := fun z => ∑ j, z j * u j
      map_add' := by
        intro z w
        simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t z
        simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hℓ : ℓ u = r ^ 2 := by
    change (∑ j, u j * u j) = Real.sqrt (realSquaredNorm u) ^ 2
    rw [Real.sq_sqrt (realSquaredNorm_nonneg u)]
    simp [realSquaredNorm, pow_two]
  have hxℓ : ℓ x = ε / 2 * r := by
    rw [show x = (ε / 2 / r) • u from rfl, map_smul, smul_eq_mul, hℓ]
    field_simp
  obtain ⟨v, hv, hmax⟩ := I.vertices.exists_max_image (fun v => ℓ (latticeReal v))
    I.vertices_nonempty
  have hbound := latticePolytope_le I.vertices ℓ (ℓ (latticeReal v)) hmax x hx
  refine ⟨v, hv, ?_⟩
  simpa only [hxℓ, r, ℓ, LinearMap.coe_mk, AddHom.coe_mk, latticeReal, pairing]
    using hbound

/-- Finiteness and nonvanishing give a strictly positive coefficient lower
bound. This is derived from the input, rather than assumed as analytic data. -/
theorem ToricInput.exists_pos_coeff_lowerBound (I : ToricInput n) :
    ∃ A : ℝ, 0 < A ∧ ∀ v : {v : Lattice n // v ∈ I.vertices}, A ≤ ‖I.coeff v‖ := by
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  let : Nonempty {v : Lattice n // v ∈ I.vertices} := ⟨⟨v, hv⟩⟩
  obtain ⟨w, _, hw⟩ := Finset.univ.exists_min_image
    (fun v : {v : Lattice n // v ∈ I.vertices} => ‖I.coeff v‖) Finset.univ_nonempty
  exact ⟨‖I.coeff w‖, norm_pos_iff.mpr (I.coeff_ne_zero w),
    fun v => hw v (Finset.mem_univ v)⟩

/-- The exponential-growth half of `lem:dominant` holds on the entire original
ambient. Its constants are constructed from the finite input's interior ball
and positive coefficient minimum. No bound on `W` or `G` is an input. -/
theorem ToricInput.maxMonomialMagnitude_exponential_lowerBound (I : ToricInput n) :
    ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧ ∀ y : LGSpace n,
      A * Real.exp (c * Real.sqrt (realSquaredNorm y.1)) ≤ maxMonomialMagnitude I y := by
  obtain ⟨A, hA, hcoeff⟩ := I.exists_pos_coeff_lowerBound
  obtain ⟨c, hc, hsupport⟩ := I.exists_pairing_ge_euclidean
  refine ⟨A, hA, c, hc, ?_⟩
  intro y
  obtain ⟨v, hv, hpair⟩ := hsupport y.1
  let w : {v : Lattice n // v ∈ I.vertices} := ⟨v, hv⟩
  calc
    A * Real.exp (c * Real.sqrt (realSquaredNorm y.1)) ≤
        ‖I.coeff w‖ * Real.exp (pairing v y.1) :=
      mul_le_mul (hcoeff w) (Real.exp_le_exp.mpr hpair)
        (Real.exp_pos _).le (norm_nonneg _)
    _ = ‖monomial (I.coeff w) w.val y‖ := (norm_monomial _ _ _).symm
    _ ≤ maxMonomialMagnitude I y := I.norm_monomial_le_maxMonomialMagnitude y w

/-- Expanding the actual `b0 = u · G` interchanges its two finite sums. -/
theorem b0_eq_sum_pairing_monomial (I : ToricInput n) (y : LGSpace n) :
    b0 I y = ∑ v : {v : Lattice n // v ∈ I.vertices},
      (pairing v.val y.1 : ℂ) * monomial (I.coeff v) v.val y := by
  simp only [b0, G, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [pairing, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem deficit_mul_exp_le (p h : ℝ) :
    (h - p) * Real.exp p ≤ Real.exp h := by
  have he : (h - p) * Real.exp (-(h - p)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (by
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)))
  calc
    (h - p) * Real.exp p = ((h - p) * Real.exp (-(h - p))) * Real.exp h := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 * Real.exp h := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp h := one_mul _

/-- The finite deficit estimate behind `lem:margin`, lines 753–757:
the logarithmic derivative error is bounded by coefficient mass times
the exponential of support height, uniformly in the quotient angle. -/
theorem ToricInput.b0_sub_supportHeight_mul_W_le (I : ToricInput n) (y : LGSpace n) :
    ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
      (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) *
        Real.exp (supportHeight I y.1) := by
  rw [b0_eq_sum_pairing_monomial, W, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ v : {v : Lattice n // v ∈ I.vertices},
        ((pairing v.val y.1 : ℂ) * monomial (I.coeff v) v.val y -
          (supportHeight I y.1 : ℂ) * monomial (I.coeff v) v.val y)‖ ≤
        ∑ v : {v : Lattice n // v ∈ I.vertices},
          ‖(pairing v.val y.1 : ℂ) * monomial (I.coeff v) v.val y -
            (supportHeight I y.1 : ℂ) * monomial (I.coeff v) v.val y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ v : {v : Lattice n // v ∈ I.vertices},
        ‖I.coeff v‖ * Real.exp (supportHeight I y.1) := by
      apply Finset.sum_le_sum
      intro v _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (I.pairing_le_supportHeight y.1 v)),
        norm_monomial]
      calc
        -(pairing v.val y.1 - supportHeight I y.1) *
            (‖I.coeff v‖ * Real.exp (pairing v.val y.1)) =
            ‖I.coeff v‖ * ((supportHeight I y.1 - pairing v.val y.1) *
              Real.exp (pairing v.val y.1)) := by ring
        _ ≤ ‖I.coeff v‖ * Real.exp (supportHeight I y.1) :=
          mul_le_mul_of_nonneg_left (deficit_mul_exp_le _ _)
            (norm_nonneg _)
    _ = (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) *
        Real.exp (supportHeight I y.1) := (Finset.sum_mul _ _ _).symm

/-- The actual finite-support error estimate used by `lem:margin`: one positive
constant works at every point of the original ambient. Its coefficient mass
and minimum are derived from `ToricInput`; no end bound is assumed. -/
theorem ToricInput.exists_b0_sub_supportHeight_mul_W_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n,
      ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤ C * maxMonomialMagnitude I y := by
  obtain ⟨A, hA, hcoeff⟩ := I.exists_pos_coeff_lowerBound
  let S : ℝ := ∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖
  have hS : 0 < S := by
    obtain ⟨v, hv⟩ := I.vertices_nonempty
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨⟨v, hv⟩, Finset.mem_univ _, norm_pos_iff.mpr (I.coeff_ne_zero _)⟩
  refine ⟨S / A, div_pos hS hA, ?_⟩
  intro y
  obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
  have hM : A * Real.exp (supportHeight I y.1) ≤ maxMonomialMagnitude I y := by
    calc
      A * Real.exp (supportHeight I y.1) ≤ ‖I.coeff v‖ * Real.exp (supportHeight I y.1) :=
        mul_le_mul_of_nonneg_right (hcoeff v) (Real.exp_pos _).le
      _ = ‖monomial (I.coeff v) v.val y‖ := by rw [norm_monomial, hv]
      _ ≤ maxMonomialMagnitude I y := I.norm_monomial_le_maxMonomialMagnitude y v
  calc
    ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
        S * Real.exp (supportHeight I y.1) := I.b0_sub_supportHeight_mul_W_le y
    _ = S / A * (A * Real.exp (supportHeight I y.1)) := by field_simp
    _ ≤ S / A * maxMonomialMagnitude I y :=
      mul_le_mul_of_nonneg_left hM (div_pos hS hA).le

end FsFltz
