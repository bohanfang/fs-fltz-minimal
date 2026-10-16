import FsFltz.Geometry.SymplecticBasis

/-!
# Nondegeneracy under cylindrical stretching

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. Stretching the Liouville radius replaces the differential by
`f * (omega + (a - 1) dr ∧ lambda)`, where `a` is the stretch derivative and
`f` is the positive radial weight. The algebra below proves nondegeneracy
from the original differential, its Liouville contraction equation, and
`dr(Z) = 1`. It does not assume symplecticity of the stretched primitive.

The manifold consumer requires the explicit differential evaluation formula.
The smooth gluing and derivation of that formula are separate obligations;
this module alone does not construct a completion.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

namespace SymplecticAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A cylindrical rank-one deformation of a nondegenerate alternating form
has trivial kernel whenever its radial slope is nonzero. -/
theorem cylindricalTwist_kernel (omega : E [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (homega : ∀ v, (∀ w, omega ![v, w] = 0) → v = 0)
    (alpha : E → ℝ) (ρ : E →ₗ[ℝ] ℝ) (Z : E)
    (hZ : ∀ w, omega ![Z, w] = alpha w) (hρ : ρ Z = 1)
    {a : ℝ} (ha : a ≠ 0) (v : E)
    (hv : ∀ w, omega ![v, w] + (a - 1) * (ρ v * alpha w - ρ w * alpha v) = 0) : v = 0 := by
  have halphaZ : alpha Z = 0 := by
    rw [← hZ Z]
    exact omega.map_eq_zero_of_eq ![Z, Z] (i := 0) (j := 1) rfl (by decide)
  have halphav : alpha v = 0 := by
    have hh := hv Z
    rw [twoForm_swap omega v Z, hZ v, halphaZ, hρ] at hh
    have hmul : a * alpha v = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp hmul).resolve_left ha
  have hmodified : v + ((a - 1) * ρ v) • Z = 0 := by
    apply homega
    intro w
    rw [omega.map_vecCons_add, omega.map_vecCons_smul, hZ w]
    have hh := hv w
    rw [halphav] at hh
    simpa only [smul_eq_mul, mul_zero, sub_zero, mul_assoc] using hh
  have hρv : ρ v = 0 := by
    have hh := congrArg ρ hmodified
    simp only [map_add, map_smul, hρ, smul_eq_mul, mul_one, map_zero] at hh
    have hmul : a * ρ v = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp hmul).resolve_left ha
  simpa only [hρv, mul_zero, zero_smul, add_zero] using hmodified

/-- Multiplication by a nonzero radial weight preserves the preceding kernel
calculation. Positive weights and positive slopes satisfy these hypotheses. -/
theorem scaledCylindricalTwist_kernel (omega : E [⋀^Fin 2]→ₗ[ℝ] ℝ)
    (homega : ∀ v, (∀ w, omega ![v, w] = 0) → v = 0)
    (alpha : E → ℝ) (ρ : E →ₗ[ℝ] ℝ) (Z : E)
    (hZ : ∀ w, omega ![Z, w] = alpha w) (hρ : ρ Z = 1)
    {a f : ℝ} (ha : a ≠ 0) (hf : f ≠ 0) (v : E)
    (hv : ∀ w, f * (omega ![v, w] + (a - 1) * (ρ v * alpha w - ρ w * alpha v)) = 0) : v = 0 := by
  apply cylindricalTwist_kernel omega homega alpha ρ Z hZ hρ ha v
  intro w
  exact (mul_eq_zero.mp (hv w)).resolve_left hf

end SymplecticAlgebra

namespace SmoothManifold

/-- Nondegeneracy of an actual new exterior derivative from its cylindrical
evaluation formula. The original primitive supplies the contraction equation;
the new differential's nondegeneracy is proved, rather than an input field. -/
theorem nondegenerate_of_cylindricalDerivative {d : ℕ} (M : SmoothManifold d)
    (alpha η : M.Form 1) (x : M.Point) (Z : M.Tangent x)
    (ρ : M.Tangent x →L[ℝ] ℝ)
    (homega : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hZ : ∀ w, evalTwo (M.exteriorDerivative alpha) x Z w = evalOne alpha x w)
    (hρ : ρ Z = 1) {a f : ℝ} (ha : a ≠ 0) (hf : f ≠ 0)
    (hformula : ∀ v w, evalTwo (M.exteriorDerivative η) x v w =
      f * (evalTwo (M.exteriorDerivative alpha) x v w +
        (a - 1) * (ρ v * evalOne alpha x w - ρ w * evalOne alpha x v))) :
    M.Nondegenerate (M.exteriorDerivative η) x := by
  intro v hv
  apply SymplecticAlgebra.scaledCylindricalTwist_kernel
    ((M.exteriorDerivative alpha x).toAlternatingMap) homega (evalOne alpha x)
    ρ.toLinearMap Z hZ hρ ha hf v
  intro w
  exact (hformula v w).symm.trans (hv w)

end SmoothManifold

end FsFltz.Geometry
