import FsFltz.Analysis.ConvexLegendre
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Legendre map in finite product coordinates

The coordinate gradient on `ι → ℝ`, with its native product norm, agrees
with the Riesz gradient after the canonical continuous linear equivalence
from Euclidean space. This supplies the coordinate form of `lem:potential`
in `geometric-part-fsf-proof.tex`, lines 631–635, for the based real spaces.
-/

noncomputable section

open Function
open scoped ContDiff

namespace FsFltz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gradient coordinates in the fixed coordinate basis. -/
def coordinateGradient (φ : (ι → ℝ) → ℝ) (u : ι → ℝ) (j : ι) : ℝ :=
  fderiv ℝ φ u (Pi.single j 1)

/-- The native coordinate gradient is the Euclidean Riesz gradient under
the canonical change of norm. -/
theorem coordinateGradient_eq_euclidean_gradient {φ : (ι → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (u : ι → ℝ) :
    coordinateGradient φ u = (EuclideanSpace.equiv ι ℝ)
      (gradient (φ ∘ EuclideanSpace.equiv ι ℝ) ((EuclideanSpace.equiv ι ℝ).symm u)) := by
  ext j
  let e := EuclideanSpace.equiv ι ℝ
  change (fderiv ℝ φ u) (Pi.single j 1) = (gradient (φ ∘ e) (e.symm u)).ofLp j
  have hh := inner_gradient_left (f := φ ∘ e) (x := e.symm u)
    (y := EuclideanSpace.single j (1 : ℝ))
  rw [EuclideanSpace.inner_single_right,
    fderiv_comp (e.symm u) (hφ _) e.differentiableAt, e.fderiv] at hh
  have he : e (EuclideanSpace.single j (1 : ℝ)) = Pi.single j 1 := rfl
  simpa only [one_mul, conj_trivial, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, e.apply_symm_apply, he]
    using hh.symm

/-- The coordinate gradient is smooth in the original product norm. -/
theorem contDiff_coordinateGradient {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (coordinateGradient φ) := by
  let e := EuclideanSpace.equiv ι ℝ
  have he : coordinateGradient φ = fun u => e (gradient (φ ∘ e) (e.symm u)) :=
    funext (coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by simp)))
  rw [he]
  exact e.contDiff.comp ((contDiff_gradient (hφ.comp e.contDiff)).comp e.symm.contDiff)

/-- The Legendre map in the native coordinate model, transported from the
Euclidean gradient by the canonical continuous linear equivalence. -/
def coordinateGradientHomeomorph {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v) :
    (ι → ℝ) ≃ₜ (ι → ℝ) :=
  (EuclideanSpace.equiv ι ℝ).symm.toHomeomorph.trans
    ((gradientHomeomorph (hφ.comp (EuclideanSpace.equiv ι ℝ).contDiff) hc hbound).trans
      (EuclideanSpace.equiv ι ℝ).toHomeomorph)

@[simp]
theorem coordinateGradientHomeomorph_apply {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v) (u : ι → ℝ) :
    coordinateGradientHomeomorph hφ hc hbound u = coordinateGradient φ u := by
  exact (coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by simp)) u).symm

omit [DecidableEq ι] in
/-- Smoothness of the global inverse in the native product norm. -/
theorem contDiff_symm_coordinateGradientHomeomorph {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v) :
    ContDiff ℝ ∞ (coordinateGradientHomeomorph hφ hc hbound).symm := by
  let e := EuclideanSpace.equiv ι ℝ
  exact e.contDiff.comp
    ((contDiff_symm_gradientHomeomorph (hφ.comp e.contDiff) hc hbound).comp e.symm.contDiff)

/-- Bijection of the literal coordinate gradient, rather than an abstract copy. -/
theorem bijective_coordinateGradient_of_uniform_hessian {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hbound : ∀ x v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v) :
    Bijective (coordinateGradient φ) := by
  have he : (coordinateGradientHomeomorph hφ hc hbound : (ι → ℝ) → (ι → ℝ)) =
      coordinateGradient φ := funext (coordinateGradientHomeomorph_apply hφ hc hbound)
  rw [← he]
  exact (coordinateGradientHomeomorph hφ hc hbound).bijective

end FsFltz
