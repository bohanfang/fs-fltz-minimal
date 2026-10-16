import FsFltz.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Differentials of the superpotential in real representative coordinates

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 68–85, and `sec:initial`,
lines 253–256 and 317–321. The formula called `dW` is proved to be the actual
Fréchet differential on the real covering coordinates, and likewise for
`dAbsWSq`. This does not assert a quotient smooth-manifold or differential-form
descent bridge.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- A single complex coordinate covector on the real logarithmic cover. -/
def complexCoordinateLinearMap (j : Fin n) : TangentCoordinates n →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))) +
  Complex.I • Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)))

theorem complexCoordinateLinearMap_apply (j : Fin n) (q : TangentCoordinates n) :
    complexCoordinateLinearMap j q = (q.1 j : ℂ) + Complex.I * (q.2 j : ℂ) := by
  simp [complexCoordinateLinearMap]

/-- The integral exponent as a real continuous linear functional. -/
def exponentLinearMap (v : Lattice n) : TangentCoordinates n →L[ℝ] ℂ :=
  ∑ j, (v j : ℂ) • complexCoordinateLinearMap j

theorem exponentLinearMap_apply (v : Lattice n) (q : TangentCoordinates n) :
    exponentLinearMap v q =
      ∑ j, (v j : ℂ) * ((q.1 j : ℂ) + Complex.I * (q.2 j : ℂ)) := by
  simp [exponentLinearMap, complexCoordinateLinearMap_apply]

/-- This continuous linear map is exactly the source exponent on representatives. -/
theorem exponentLinearMap_eq_pairing (v : Lattice n) (q : TangentCoordinates n) :
    exponentLinearMap v q = (pairing v q.1 : ℂ) + Complex.I * (pairing v q.2 : ℂ) := by
  rw [exponentLinearMap_apply]
  simp only [pairing, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual derivative map of the finite Laurent sum, before collecting
terms by tangent coordinate. -/
def dWLinearMap (I : ToricInput n) (y : LGSpace n) : TangentCoordinates n →L[ℝ] ℂ :=
  ∑ v : {v : Lattice n // v ∈ I.vertices},
    monomial (I.coeff v) v.val y • exponentLinearMap v.val

/-- Collecting the finite sum gives exactly the specified `G` and `dW` formula. -/
theorem dWLinearMap_apply (I : ToricInput n) (y : LGSpace n) (q : TangentCoordinates n) :
    dWLinearMap I y q = dW I y q := by
  simp only [dWLinearMap, sum_apply, smul_apply,
    smul_eq_mul, exponentLinearMap_apply, Finset.mul_sum, dW, G, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Each descended monomial has the expected differential on the real cover. -/
theorem hasFDerivAt_monomial_representatives (c : ℂ) (v : Lattice n)
    (x : TangentCoordinates n) :
    HasFDerivAt (fun z : TangentCoordinates n => monomial c v (z.1, angleQuotient z.2))
      (monomial c v (x.1, angleQuotient x.2) • exponentLinearMap v) x := by
  have hexp := (Complex.hasStrictFDerivAt_exp_real (exponentLinearMap v x)).hasFDerivAt.comp x
    (exponentLinearMap v).hasFDerivAt
  have h := hexp.const_mul c
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, smul_smul,
    monomial_angleQuotient, exponentLinearMap_eq_pairing,
    mul_comm Complex.I] using h

/-- The explicit `dW` covector is the actual Fréchet derivative of `W` in real
representative coordinates. No end-bound or geometric conclusion is assumed. -/
theorem hasFDerivAt_W_representatives (I : ToricInput n) (x : TangentCoordinates n) :
    HasFDerivAt (fun z : TangentCoordinates n => W I (z.1, angleQuotient z.2))
      (dWLinearMap I (x.1, angleQuotient x.2)) x := by
  simpa only [W, dWLinearMap] using
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun v _ => hasFDerivAt_monomial_representatives (I.coeff v) v.val x)

/-- Applying the actual differential gives the previously defined coordinate formula. -/
theorem fderiv_W_representatives_apply (I : ToricInput n) (x q : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n => W I (z.1, angleQuotient z.2)) x q =
      dW I (x.1, angleQuotient x.2) q := by
  rw [(hasFDerivAt_W_representatives I x).fderiv, dWLinearMap_apply]

/-- The real differential of the squared magnitude, as a continuous linear map. -/
def dAbsWSqLinearMap (I : ToricInput n) (y : LGSpace n) : TangentCoordinates n →L[ℝ] ℝ :=
  (2 • (innerSL ℝ) (W I y)).comp (dWLinearMap I y)

/-- The map equals the prescribed expression `2 Re(W̄ dW)`. -/
theorem dAbsWSqLinearMap_apply (I : ToricInput n) (y : LGSpace n)
    (q : TangentCoordinates n) : dAbsWSqLinearMap I y q = dAbsWSq I y q := by
  simp [dAbsWSqLinearMap, dWLinearMap_apply, dAbsWSq, real_inner_eq_re_inner,
    RCLike.inner_apply, mul_comm]
  ring

/-- The squared-magnitude expression is the actual differential on the cover. -/
theorem hasFDerivAt_absWSq_representatives (I : ToricInput n) (x : TangentCoordinates n) :
    HasFDerivAt (fun z : TangentCoordinates n => Complex.normSq (W I (z.1, angleQuotient z.2)))
      (dAbsWSqLinearMap I (x.1, angleQuotient x.2)) x := by
  simpa only [Function.comp_def, ← Complex.normSq_eq_norm_sq, dAbsWSqLinearMap] using
    (hasStrictFDerivAt_norm_sq (W I (x.1, angleQuotient x.2))).hasFDerivAt.comp x
      (hasFDerivAt_W_representatives I x)

/-- Applying the actual differential of `|W|²` gives the admissibility formula. -/
theorem fderiv_absWSq_representatives_apply (I : ToricInput n) (x q : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n =>
      Complex.normSq (W I (z.1, angleQuotient z.2))) x q =
      dAbsWSq I (x.1, angleQuotient x.2) q := by
  rw [(hasFDerivAt_absWSq_representatives I x).fderiv, dAbsWSqLinearMap_apply]

end FsFltz
