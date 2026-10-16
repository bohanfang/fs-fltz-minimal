import FsFltz.Analysis.FiniteSupportGrowth
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Surjectivity of the native toric superpotential

Source: `geometric-part-fsf-proof.tex`, `lem:surjective`, lines 820–836.
The support is the actual input vertex set from `geoemtric-part-fsf.tex`,
`sec:data`, lines 57–71. The proof restricts the quotient-defined `W` to
an integral monomial curve, clears its negative exponents, and applies the
fundamental theorem of algebra. No geometric comparison data are inputs.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Integral pairing for the monomial curve in `lem:surjective`. -/
def integerPairing (v w : Lattice n) : ℤ := ∑ j, v j * w j

/-- Scalar extension of the integral pairing agrees with the original pairing. -/
theorem pairing_latticeReal (v w : Lattice n) :
    pairing v (latticeReal w) = (integerPairing v w : ℝ) := by
  simp [pairing, latticeReal, integerPairing]

private def coordinatePolynomial (v : Lattice n) : Polynomial ℤ :=
  ∑ j : Fin n, Polynomial.monomial j.val (v j)

private theorem coordinatePolynomial_coeff (v : Lattice n) (j : Fin n) :
    (coordinatePolynomial v).coeff j.val = v j := by
  classical
  rw [coordinatePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Polynomial.coeff_monomial, Fin.val_inj, hkj]
  · simp

private theorem coordinatePolynomial_ne_zero (v : Lattice n) (hv : v ≠ 0) :
    coordinatePolynomial v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hj := congrArg (fun p : Polynomial ℤ => p.coeff j.val) h
  simpa [coordinatePolynomial_coeff] using hj

private theorem coordinatePolynomial_eval (v : Lattice n) (N : ℤ) :
    (coordinatePolynomial v).eval N = integerPairing v (fun j => N ^ j.val) := by
  simp [coordinatePolynomial, integerPairing, Polynomial.eval_finsetSum]

/-- A nonzero integral direction separates all vertices of any finite support.
The explicit direction `(1,N,…,N^(n-1))` avoids the finite root sets of the
nonzero difference polynomials, as in `lem:surjective`, lines 825–829. -/
theorem exists_separating_integer_direction (V : Finset (Lattice n)) (hn : 1 ≤ n) :
    ∃ w : Lattice n, w ≠ 0 ∧
      Function.Injective (fun v : {v : Lattice n // v ∈ V} => integerPairing v.val w) := by
  classical
  let A := {v : Lattice n // v ∈ V}
  let pairs : Set (A × A) := {p | p.1 ≠ p.2}
  let bad : Set ℤ := ⋃ p ∈ pairs, {N | (coordinatePolynomial (p.1.val - p.2.val)).IsRoot N}
  have hfinite : bad.Finite := by
    apply (Set.toFinite pairs).biUnion
    intro p hp
    apply Polynomial.finite_setOfPred_isRoot
    apply coordinatePolynomial_ne_zero
    intro h
    apply hp
    exact Subtype.ext (sub_eq_zero.mp h)
  obtain ⟨N, hN⟩ := hfinite.exists_notMem
  refine ⟨fun j => N ^ j.val, ?_, ?_⟩
  · intro h
    have hj := congrFun h ⟨0, by omega⟩
    norm_num at hj
  · intro v v' heq
    by_contra hne
    apply hN
    apply Set.mem_iUnion.mpr
    refine ⟨(v, v'), Set.mem_iUnion.mpr ⟨hne, ?_⟩⟩
    change (coordinatePolynomial (v.val - v'.val)).eval N = 0
    rw [coordinatePolynomial_eval]
    simpa [integerPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr heq

/-- The integral monomial curve is a point of the original quotient ambient.
Complex logarithms provide real representative coordinates; no new torus or
Laurent-polynomial hierarchy is introduced. -/
def monomialCurve (w : Lattice n) (t : ℂ) : LGSpace n :=
  (fun j => (w j : ℝ) * (Complex.log t).re,
    angleQuotient (fun j => (w j : ℝ) * (Complex.log t).im))

/-- The native descended monomial restricts exactly to an integer power. -/
theorem monomial_monomialCurve (c : ℂ) (v w : Lattice n) (t : ℂ) (ht : t ≠ 0) :
    monomial c v (monomialCurve w t) = c * t ^ integerPairing v w := by
  rw [monomialCurve, monomial_angleQuotient]
  have hpair (r : ℝ) : pairing v (fun j => (w j : ℝ) * r) =
      (integerPairing v w : ℝ) * r := by
    simp [pairing, integerPairing, Finset.sum_mul, mul_assoc]
  rw [hpair, hpair]
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [show (integerPairing v w : ℂ) * ((Complex.log t).re : ℂ) +
      (integerPairing v w : ℂ) * ((Complex.log t).im : ℂ) * Complex.I =
      (integerPairing v w : ℂ) * Complex.log t by
        rw [mul_assoc, ← mul_add, Complex.re_add_im]]
  rw [Complex.exp_int_mul, Complex.exp_log ht]

/-- Exact finite Laurent sum along the monomial curve, consumed by the
surjectivity proof rather than assumed as a representation of `W`. -/
theorem W_monomialCurve (I : ToricInput n) (w : Lattice n) (t : ℂ) (ht : t ≠ 0) :
    W I (monomialCurve w t) = ∑ v : {v : Lattice n // v ∈ I.vertices},
      I.coeff v * t ^ integerPairing v.val w := by
  simp only [W, monomial_monomialCurve _ _ _ _ ht]

/-- Interior containment forces both signs along every nonzero integral
direction. This rules out the one-sided Laurent supports that need not be
surjective onto zero. -/
theorem ToricInput.integerPairing_both_signs (I : ToricInput n) (w : Lattice n)
    (hw : w ≠ 0) :
    (∃ v ∈ I.vertices, integerPairing v w < 0) ∧
      (∃ v ∈ I.vertices, 0 < integerPairing v w) := by
  obtain ⟨c, hc, hsupport⟩ := I.exists_pairing_ge_euclidean
  have hj : ∃ j, w j ≠ 0 := by
    by_contra h
    apply hw
    funext j
    simpa using (not_exists.mp h) j
  obtain ⟨j, hj⟩ := hj
  have hr : 0 < Real.sqrt (realSquaredNorm (latticeReal w)) := by
    apply Real.sqrt_pos.mpr
    apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
    refine ⟨j, Finset.mem_univ j, ?_⟩
    exact sq_pos_of_ne_zero (by change (w j : ℝ) ≠ 0; exact_mod_cast hj)
  have hrneg : Real.sqrt (realSquaredNorm (-latticeReal w)) =
      Real.sqrt (realSquaredNorm (latticeReal w)) := by
    simp [realSquaredNorm, Pi.neg_apply]
  constructor
  · obtain ⟨v, hv, h⟩ := hsupport (-latticeReal w)
    refine ⟨v, hv, ?_⟩
    have hpos : 0 < - (integerPairing v w : ℝ) := by
      apply (mul_pos hc hr).trans_le
      simpa [pairing, latticeReal, integerPairing, hrneg,
        Finset.sum_neg_distrib] using h
    exact_mod_cast (neg_pos.mp hpos)
  · obtain ⟨v, hv, h⟩ := hsupport (latticeReal w)
    refine ⟨v, hv, ?_⟩
    have hpos : 0 < (integerPairing v w : ℝ) :=
      (mul_pos hc hr).trans_le (by simpa [pairing_latticeReal] using h)
    exact_mod_cast hpos

private theorem shifted_monomial_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (e : A → ℕ) (he : Function.Injective e) (c : A → ℂ) (a : A) :
    (∑ i : A, Polynomial.monomial (e i) (c i)).coeff (e a) = c a := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, he.eq_iff]

private theorem exists_nonzero_laurent_root {A : Type*} [Fintype A] [Nonempty A]
    (d : A → ℤ) (hd : Function.Injective d) (c : A → ℂ) (hc : ∀ a, c a ≠ 0)
    (hneg : ∃ a, d a < 0) (hpos : ∃ b, 0 < d b) (z : ℂ) :
    ∃ t : ℂ, t ≠ 0 ∧ ∑ a : A, c a * t ^ d a = z := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.univ.exists_min_image d Finset.univ_nonempty
  have hmin (i : A) : d a ≤ d i := ha i (Finset.mem_univ i)
  obtain ⟨a', ha'⟩ := hneg
  have hda : d a < 0 := (hmin a').trans_lt ha'
  obtain ⟨b, hdb⟩ := hpos
  let e : A → ℕ := fun i => (d i - d a).toNat
  have hecast (i : A) : (e i : ℤ) = d i - d a :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmin i))
  have he : Function.Injective e := by
    intro i j hij
    apply hd
    have := congrArg (fun k : ℕ => (k : ℤ)) hij
    rw [hecast, hecast] at this
    omega
  let k : ℕ := (-d a).toNat
  have hkcast : (k : ℤ) = -d a := Int.toNat_of_nonneg (by omega)
  have hk : k ≠ 0 := by omega
  have heb : e b ≠ 0 := by have := hecast b; omega
  have hebk : e b ≠ k := by have := hecast b; omega
  have hea : e a = 0 := by simp [e]
  let P : Polynomial ℂ := (∑ i : A, Polynomial.monomial (e i) (c i)) -
    Polynomial.monomial k z
  have hP0 : P.coeff 0 = c a := by
    change ((∑ i : A, Polynomial.monomial (e i) (c i)) -
      Polynomial.monomial k z).coeff 0 = c a
    rw [Polynomial.coeff_sub, ← hea, shifted_monomial_coeff e he c a, hea]
    simp [Polynomial.coeff_monomial, hk]
  have hPb : P.coeff (e b) = c b := by
    change ((∑ i : A, Polynomial.monomial (e i) (c i)) -
      Polynomial.monomial k z).coeff (e b) = c b
    rw [Polynomial.coeff_sub, shifted_monomial_coeff e he c b]
    simp [Polynomial.coeff_monomial, Ne.symm hebk]
  have hdegree : 0 < P.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    by_contra h
    have hdeg : P.natDegree = 0 := by omega
    have hzero : P.coeff (e b) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact hc b (hPb.symm.trans hzero)
  obtain ⟨t, ht⟩ := Complex.exists_root hdegree
  have htne : t ≠ 0 := by
    intro h
    have hzero : P.coeff 0 = 0 := (Polynomial.coeff_zero_eq_eval_zero P).trans
      (by simpa [h] using ht)
    exact hc a (hP0.symm.trans hzero)
  have hpow (i : A) : t ^ e i = t ^ d i * t ^ k := by
    rw [← zpow_natCast, hecast, sub_eq_add_neg, zpow_add₀ htne,
      ← hkcast, zpow_natCast]
  have heval : P.eval t = (∑ i : A, c i * t ^ d i - z) * t ^ k := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial]
    simp only [hpow, ← mul_assoc, ← Finset.sum_mul, sub_mul]
  refine ⟨t, htne, ?_⟩
  have hmul : (∑ i : A, c i * t ^ d i - z) * t ^ k = 0 := heval.symm.trans ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (pow_ne_zero _ htne))

/-- The nonempty-fiber lemma of the source, proved for the native toric input
and original quotient-defined superpotential. -/
theorem ToricInput.W_surjective (I : ToricInput n) : Function.Surjective (W I) := by
  classical
  obtain ⟨w, hw, hinj⟩ := exists_separating_integer_direction I.vertices I.positive_rank
  obtain ⟨hneg, hpos⟩ := I.integerPairing_both_signs w hw
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  let A := {v : Lattice n // v ∈ I.vertices}
  let : Nonempty A := ⟨⟨v, hv⟩⟩
  intro z
  obtain ⟨t, ht, hz⟩ := exists_nonzero_laurent_root
    (fun v : A => integerPairing v.val w) hinj I.coeff I.coeff_ne_zero
    (by obtain ⟨a, ha, h⟩ := hneg; exact ⟨⟨a, ha⟩, h⟩)
    (by obtain ⟨b, hb, h⟩ := hpos; exact ⟨⟨b, hb⟩, h⟩) z
  exact ⟨monomialCurve w t, (W_monomialCurve I w t ht).trans hz⟩

/-- Every specified full far fiber is nonempty before truncation or a
completion marking is constructed. -/
theorem ToricInput.fullFiber_nonempty (I : ToricInput n) (R : ℝ) :
    (FullFiber I R).Nonempty := I.W_surjective (R : ℂ)

/-- The literal ratio set has a point for every radius, by surjectivity.
Positivity of its denominators and boundedness remain separate end estimates. -/
theorem ToricInput.ratioSet_nonempty (I : ToricInput n) (R : ℝ) :
    (ratioSet I R).Nonempty := by
  obtain ⟨y, hy⟩ := I.W_surjective (R : ℂ)
  refine ⟨endRatio I y, y, ?_, rfl⟩
  change R ≤ ‖W I y‖
  rw [hy, Complex.norm_real, Real.norm_eq_abs]
  exact le_abs_self R

end FsFltz
