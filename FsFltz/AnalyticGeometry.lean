import FsFltz.Analytic
import FsFltz.CoordinateGeometry

/-!
# Pointwise geometry of the explicit ambient coordinate formulas

This module connects the formulas in `Analytic` to the proved linear algebra
in `CoordinateGeometry`. Source: `geoemtric-part-fsf.tex`, `sec:data`, lines
74–86. The conclusions are pointwise statements about coordinate forms.
Smooth descent, exterior differentiation, and manifold-level symplecticity
remain separate foundational bridges.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- Identify real logarithmic tangent coordinates with complex vectors. -/
def tangentComplexCoordinates (q : TangentCoordinates n) : Fin n → ℂ :=
  fun j => (q.1 j : ℂ) + Complex.I * (q.2 j : ℂ)

/-- The standard complex structure sends `(δu, δθ)` to `(-δθ, δu)`. -/
def complexStructureCoordinates (q : TangentCoordinates n) : TangentCoordinates n :=
  (-q.2, q.1)

theorem tangentComplexCoordinates_re (q : TangentCoordinates n) (j : Fin n) :
    (tangentComplexCoordinates q j).re = q.1 j := by
  simp [tangentComplexCoordinates]

theorem tangentComplexCoordinates_im (q : TangentCoordinates n) (j : Fin n) :
    (tangentComplexCoordinates q j).im = q.2 j := by
  simp [tangentComplexCoordinates]

/-- The coordinate identification is injective. -/
theorem tangentComplexCoordinates_injective :
    Function.Injective (tangentComplexCoordinates : TangentCoordinates n → Fin n → ℂ) := by
  intro q r h
  apply Prod.ext
  · funext j
    simpa [tangentComplexCoordinates] using congrArg Complex.re (congrFun h j)
  · funext j
    simpa [tangentComplexCoordinates] using congrArg Complex.im (congrFun h j)

/-- The coordinate identification represents every complex tangent vector. -/
theorem tangentComplexCoordinates_surjective :
    Function.Surjective (tangentComplexCoordinates : TangentCoordinates n → Fin n → ℂ) := by
  intro z
  refine ⟨(fun j => (z j).re, fun j => (z j).im), ?_⟩
  funext j
  apply Complex.ext <;> simp [tangentComplexCoordinates]

theorem tangentComplexCoordinates_zero :
    tangentComplexCoordinates (0 : TangentCoordinates n) = 0 := by
  funext j
  simp [tangentComplexCoordinates]

/-- The same standard complex structure is used in the generic calculation. -/
theorem tangentComplexCoordinates_complexStructure (q : TangentCoordinates n) :
    tangentComplexCoordinates (complexStructureCoordinates q) =
      CoordinateGeometry.complexStructure (tangentComplexCoordinates q) := by
  funext j
  apply Complex.ext <;>
    simp [tangentComplexCoordinates, complexStructureCoordinates,
      CoordinateGeometry.complexStructure]

/-- The explicit `dW` expression is the generic logarithmic covector. -/
theorem dW_eq_evaluation (I : ToricInput n) (y : LGSpace n) (q : TangentCoordinates n) :
    dW I y q = CoordinateGeometry.evaluation (G I y) (tangentComplexCoordinates q) := rfl

/-- The actual coordinate candidate for `dλ_K` agrees with the generic form. -/
theorem omegaKCoordinates_eq_omega (I : ToricInput n) (K : ℝ) (y : LGSpace n)
    (q r : TangentCoordinates n) :
    omegaKCoordinates I K y q r = CoordinateGeometry.omega (G I y) K
      (tangentComplexCoordinates q) (tangentComplexCoordinates r) := by
  unfold omegaKCoordinates CoordinateGeometry.omega
  rw [← dW_eq_evaluation, ← dW_eq_evaluation]
  congr 1
  · unfold omega0Coordinates
    change _ = Complex.imAddGroupHom (∑ j,
      conj (tangentComplexCoordinates q j) * tangentComplexCoordinates r j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [tangentComplexCoordinates, Complex.mul_im, Complex.mul_re]
    ring
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- Positivity for every nonzero real tangent vector and every `K ≥ 0`. -/
theorem omegaKCoordinates_complexStructure_pos (I : ToricInput n) (y : LGSpace n)
    {K : ℝ} (hK : 0 ≤ K) (q : TangentCoordinates n) (hq : q ≠ 0) :
    0 < omegaKCoordinates I K y q (complexStructureCoordinates q) := by
  rw [omegaKCoordinates_eq_omega, tangentComplexCoordinates_complexStructure]
  apply CoordinateGeometry.omega_complexStructure_pos (G I y) _ hK
  intro h
  apply hq
  apply tangentComplexCoordinates_injective
  exact h.trans tangentComplexCoordinates_zero.symm

/-- Pointwise nondegeneracy of the prescribed coordinate two-form. -/
theorem omegaKCoordinates_nondegenerate (I : ToricInput n) (y : LGSpace n)
    {K : ℝ} (hK : 0 ≤ K) (q : TangentCoordinates n)
    (hq : ∀ r, omegaKCoordinates I K y q r = 0) : q = 0 := by
  apply tangentComplexCoordinates_injective
  rw [tangentComplexCoordinates_zero]
  apply CoordinateGeometry.omega_nondegenerate (G I y) _ hK
  intro z
  obtain ⟨r, rfl⟩ := tangentComplexCoordinates_surjective z
  rw [← omegaKCoordinates_eq_omega]
  exact hq r

/-- The real radial vector, regarded as a complex tangent vector. -/
def radialComplexCoordinates (y : LGSpace n) : Fin n → ℂ := fun j => y.1 j

/-- The source scalar `b₀` is the generic covector on the radial vector. -/
theorem evaluation_radialComplexCoordinates (I : ToricInput n) (y : LGSpace n) :
    CoordinateGeometry.evaluation (G I y) (radialComplexCoordinates y) = b0 I y := by
  simp only [CoordinateGeometry.evaluation, radialComplexCoordinates, b0]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The explicit coordinate vector is the proved inverse-system solution. -/
theorem tangentComplexCoordinates_liouville (I : ToricInput n) (K : ℝ) (y : LGSpace n) :
    tangentComplexCoordinates (liouvilleCoordinates I K y) =
      CoordinateGeometry.liouville (G I y) (radialComplexCoordinates y) (W I y) K := by
  funext j
  apply Complex.ext <;>
    simp [tangentComplexCoordinates, liouvilleCoordinates, CoordinateGeometry.liouville,
      CoordinateGeometry.derivativeNormSq, a, evaluation_radialComplexCoordinates,
      radialComplexCoordinates, mul_assoc, Complex.mul_re, Complex.mul_im] <;> ring

/-- The explicit primitive agrees with the pointwise generic primitive. -/
theorem lambdaKCoordinates_eq_primitive (I : ToricInput n) (K : ℝ) (y : LGSpace n)
    (q : TangentCoordinates n) :
    lambdaKCoordinates I K y q =
      CoordinateGeometry.primitive (G I y) (radialComplexCoordinates y) (W I y) K
        (tangentComplexCoordinates q) := by
  unfold lambdaKCoordinates CoordinateGeometry.primitive
  rw [← dW_eq_evaluation]
  congr 1
  · unfold lambda0Coordinates
    change _ = Complex.imAddGroupHom (∑ j,
      conj (radialComplexCoordinates y j) * tangentComplexCoordinates q j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [radialComplexCoordinates, tangentComplexCoordinates, Complex.mul_im]
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- The input-defined vector satisfies the contraction equation for the
prescribed coordinate form and primitive for every `K ≥ 0`.
This establishes the algebraic Liouville equation, without claiming its
smooth descended manifold realization. -/
theorem omegaKCoordinates_liouville (I : ToricInput n) (y : LGSpace n)
    {K : ℝ} (hK : 0 ≤ K) (q : TangentCoordinates n) :
    omegaKCoordinates I K y (liouvilleCoordinates I K y) q =
      lambdaKCoordinates I K y q := by
  rw [omegaKCoordinates_eq_omega, tangentComplexCoordinates_liouville,
    CoordinateGeometry.omega_liouville _ _ _ hK, lambdaKCoordinates_eq_primitive]

end FsFltz
