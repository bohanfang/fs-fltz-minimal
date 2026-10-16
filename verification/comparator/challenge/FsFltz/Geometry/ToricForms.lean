import FsFltz.Geometry.Smooth
import FsFltz.QuotientGeometry

/-!
# Actual quotient differential forms

The constructions use the actual manifold derivative. Angular covectors are
the pullback of `Im(conj(q) dq)` along a unit-circle coordinate, without choosing
a global real angle. Source: `sec:data`, lines 68–97; `sec:lean`, lines 778–814.
Identifying their representative-coordinate expressions and proving the
symplectic exterior-derivative calculation are separate bridges.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators ComplexConjugate

namespace FsFltz.Geometry
open SmoothManifold

/-- Actual differential of a real scalar function. -/
def differentialCovector {d : ℕ} (M : SmoothManifold d) (f : M.Point → ℝ)
    (x : M.Point) : M.Tangent x →L[ℝ] ℝ :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) f x

/-- Actual differential of a complex function, viewed as a real linear map. -/
def complexDifferential {d : ℕ} (M : SmoothManifold d) (f : M.Point → ℂ)
    (x : M.Point) : M.Tangent x →L[ℝ] ℂ :=
  mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℂ)) f x

/-- The angular covector pulled back from a unit-circle-valued map `q`.
Smoothness and unit modulus are established for the torus coordinate maps;
the formula itself uses no global angle or chosen derivative operator. -/
def phaseCovector {d : ℕ} (M : SmoothManifold d) (q : M.Point → ℂ)
    (x : M.Point) : M.Tangent x →L[ℝ] ℝ :=
  Complex.imCLM.comp ((conj (q x) • ContinuousLinearMap.id ℝ ℂ).comp
    (complexDifferential M q x))

/-- Convert an actual covector into the native alternating one-form fiber. -/
def covectorForm {d : ℕ} (M : SmoothManifold d)
    (a : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) : M.Form 1 :=
  fun x => ContinuousAlternatingMap.ofSubsingleton ℝ (M.Tangent x) ℝ (0 : Fin 1) (a x)

@[simp]
theorem evalOne_covectorForm {d : ℕ} (M : SmoothManifold d)
    (a : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) (x : M.Point) (v : M.Tangent x) :
    evalOne (covectorForm M a) x v = a x v := by
  simp [evalOne, covectorForm]

theorem phaseCovector_apply {d : ℕ} (M : SmoothManifold d) (q : M.Point → ℂ)
    (x : M.Point) (v : M.Tangent x) :
    phaseCovector M q x v = (conj (q x) * complexDifferential M q x v).im := by
  simp [phaseCovector]

def lgCircleCoordinate {n : ℕ} (j : Fin n) (y : (lgManifold n).Point) : ℂ :=
  AddCircle.toCircle (y.2 j)

def cotangentCircleCoordinate {n : ℕ} (j : Fin n) (y : (cotangentManifold n).Point) : ℂ :=
  AddCircle.toCircle (y.1 j)

/-- Actual `du_j` and descended `d theta_j` on `Y`. -/
def lgLogCovector {n : ℕ} (j : Fin n) (y : (lgManifold n).Point) :=
  differentialCovector (lgManifold n) (fun x => x.1 j) y

def lgAngleCovector {n : ℕ} (j : Fin n) (y : (lgManifold n).Point) :=
  phaseCovector (lgManifold n) (lgCircleCoordinate j) y

/-- Actual `dp_j` and descended `d theta_j` on the specified cotangent model. -/
def cotangentMomentumCovector {n : ℕ} (j : Fin n) (y : (cotangentManifold n).Point) :=
  differentialCovector (cotangentManifold n) (fun x => x.2 j) y

def cotangentAngleCovector {n : ℕ} (j : Fin n) (y : (cotangentManifold n).Point) :=
  phaseCovector (cotangentManifold n) (cotangentCircleCoordinate j) y

/-- The source's literal `lambda0 = sum u_j d theta_j`. -/
def lambda0Form (n : ℕ) : (lgManifold n).Form 1 :=
  covectorForm (lgManifold n) (fun y => ∑ j, y.1 j • lgAngleCovector j y)

/-- The literal pullback of `lambda_C = (x dy - y dx)/2` by `W`, using
the actual manifold differential of the already quotient-defined `W`. -/
def superpotentialPlaneForm {n : ℕ} (I : ToricInput n) : (lgManifold n).Form 1 :=
  covectorForm (lgManifold n) (fun y =>
    (1 / 2 : ℝ) • ((W I y).re • Complex.imCLM.comp
      (complexDifferential (lgManifold n) (W I) y) -
      (W I y).im • Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) y)))

/-- The prescribed ambient primitive for every real coefficient `K`.
Its symplecticity for nonnegative `K` is a separate geometric calculation. -/
def lambdaKForm {n : ℕ} (I : ToricInput n) (K : ℝ) : (lgManifold n).Form 1 :=
  lambda0Form n + K • superpotentialPlaneForm I

/-- The based cotangent primitive `sum p_j d theta_j`. -/
def lambdaCanForm (n : ℕ) : (cotangentManifold n).Form 1 :=
  covectorForm (cotangentManifold n) (fun y => ∑ j, y.2 j • cotangentAngleCovector j y)

theorem superpotentialPlaneForm_apply {n : ℕ} (I : ToricInput n)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y) :
    evalOne (superpotentialPlaneForm I) y v =
      (1 / 2 : ℝ) * ((W I y).re * (complexDifferential (lgManifold n) (W I) y v).im -
        (W I y).im * (complexDifferential (lgManifold n) (W I) y v).re) := by
  simp [superpotentialPlaneForm]

end FsFltz.Geometry
