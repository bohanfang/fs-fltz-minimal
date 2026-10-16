import FsFltz.Analysis.PotentialPathFiberBounds
import FsFltz.Analysis.CompatiblePotentialLegendre

/-!
# Analytic data of the potential selected for the retained endpoint

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 568–643,
and `prop:endpoint`, lines 1922–1959. These data concern the two selected
functions and their actual gradients; they contain no ribbon, marking,
comparison chain, or core assertion.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace FsFltz
variable {n : ℕ}

/-- The quantitative analytic properties and literal Legendre maps of the
same homogeneous potential and its smooth extension. -/
structure RetainedLegendrePotential (φEnd φ : RealSpace n → ℝ) where
  smooth : ContDiff ℝ ∞ φ
  end_c1 : ContDiff ℝ 1 φEnd
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  hessian_lower : ∀ u v : EuclideanSpace ℝ (Fin n), lower * ‖v‖ ^ 2 ≤
    inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v
  hessian_upper : ∀ u v : EuclideanSpace ℝ (Fin n),
    inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ upper * ‖v‖ ^ 2
  radius : ℝ
  radius_pos : 0 < radius
  end_eq : ∀ u, radius ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u
  endGradient : RealSpace n ≃ₜ RealSpace n
  gradient : RealSpace n ≃ₜ RealSpace n
  endGradient_eq : ∀ u, endGradient u = coordinateGradient φEnd u
  endGradient_zero : endGradient 0 = 0
  gradient_eq : ∀ u, gradient u = coordinateGradient φ u
  inverse_smooth : ContDiff ℝ ∞ gradient.symm

/-- Positive Hessians and Euler's identity imply strict positivity of the
homogeneous potential in every nonzero direction. -/
theorem IsStronglyCompatibleEndPotential.positive {I : ToricInput n}
    {φ : RealSpace n → ℝ} (h : IsStronglyCompatibleEndPotential I φ)
    (h1 : ContDiff ℝ 1 φ) (u : RealSpace n) (hu : u ≠ 0) : 0 < φ u := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let x := e.symm u
  have hx : x ≠ 0 := by
    intro hx
    apply hu
    have he := congrArg e hx
    simpa [x, e] using he
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he := inner_hessian_self_eq_two_mul_on_homogeneous_end
    (φ := φ ∘ e) (φEnd := φ ∘ e) (h1.comp e.contDiff)
    (fun y hy => (h.smooth (e y) (by simpa [e] using hy)).comp y e.contDiff.contDiffAt)
    (fun r hr y => by simp only [Function.comp_apply, map_smul, h.homogeneous r hr])
    (R := ‖x‖ / 2) (by positivity) (fun _ _ => rfl) (x := x) (by linarith)
  have hp := h.hessian_pos x hx x hx
  rw [he] at hp
  have hp' : 0 < (φ ∘ e) x := by linarith
  change 0 < φ (e (e.symm u)) at hp'
  rwa [e.apply_symm_apply] at hp'

end FsFltz
