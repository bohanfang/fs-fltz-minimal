import FsFltz.Analysis.CompatiblePotentialStar
import FsFltz.Analysis.CompatiblePotentialPerturbation
import FsFltz.Analysis.PotentialHessian
import FsFltz.Analysis.StrongConvexLegendre

/-!
# Existence of the strongly compatible homogeneous potential

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 560–624.
The positive quadratic coefficient is chosen using compactness of the actual
polar facets. Its Hessian is measured in the fixed Euclidean coordinates.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace FsFltz

variable {n : ℕ}

/-- The literal strong end condition in `lem:potential`: smoothness off zero,
degree two, positive Hessian in the prescribed basis, and facet-star inclusion. -/
structure IsStronglyCompatibleEndPotential (I : ToricInput n) (φ : RealSpace n → ℝ) : Prop where
  smooth : ∀ x ≠ 0, ContDiffAt ℝ ∞ φ x
  homogeneous : ∀ (r : ℝ), 0 < r → ∀ x, φ (r • x) = r ^ 2 * φ x
  hessian_pos : ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 →
    ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < inner ℝ
        ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) x) v) v
  facet_star : ∀ v ∈ I.vertices,
    MapsTo (coordinateGradient φ) (polarFacet I v) (interior (rayStar I v))

@[simp] theorem realSquaredNorm_euclidean (x : EuclideanSpace ℝ (Fin n)) :
    realSquaredNorm ((EuclideanSpace.equiv (Fin n) ℝ) x) = ‖x‖ ^ 2 := by
  simp [realSquaredNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]

theorem realSquaredNorm_smul (r : ℝ) (x : RealSpace n) :
    realSquaredNorm (r • x) = r ^ 2 * realSquaredNorm x := by
  simp [realSquaredNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The actual mollified squared gauge admits one strictly positive quadratic
perturbation preserving all of its native facet-star conditions. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∃ δ > 0,
        ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n) =>
          φ ((EuclideanSpace.equiv (Fin n) ℝ) x) - δ * ‖x‖ ^ 2) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), δ * ‖x‖ ^ 2 ≤
          φ ((EuclideanSpace.equiv (Fin n) ℝ) x)) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ∀ v,
          (2 * δ) * ‖v‖ ^ 2 ≤ inner ℝ
            ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) x) v) v) := by
  obtain ⟨ε, hε, hsmall, hstar⟩ := I.exists_mollifiedSupportPrepotential_compatible
  let f := mollifiedSupportPrepotential I ε hε
  have hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x :=
    fun _ hx => mollifiedSupportPrepotential_contDiffAt I ε hε hsmall hx
  obtain ⟨δ, hδ, hδstar⟩ := exists_quadraticPerturbation_gradient_mem
    (K := fun v : {v // v ∈ I.vertices} => polarFacet I v.val)
    (U := fun v : {v // v ∈ I.vertices} => interior (rayStar I v.val))
    (fun v => isCompact_polarFacet I v.val) (fun _ => isOpen_interior)
    (fun v x hx => hfs x (ne_zero_of_mem_polarFacet I v.val hx))
    (fun v => hstar v.val v.property)
  let φ := quadraticPerturbation f δ
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφ1 : ContDiff ℝ 1 φ :=
    (mollifiedSupportPrepotential_contDiff_one I ε hε hsmall).add
      (contDiff_const.mul (contDiff_realSquaredNorm.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)))
  have hφs : ∀ x ≠ 0, ContDiffAt ℝ ∞ φ x := fun x hx =>
    (hfs x hx).add (contDiffAt_const.mul contDiff_realSquaredNorm.contDiffAt)
  have hφconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n) =>
      φ (e x) - δ * ‖x‖ ^ 2) := by
    convert (mollifiedSupportPrepotential_convex I ε hε hsmall).comp_linearMap
      e.toLinearMap using 1 <;> simp [φ, quadraticPerturbation, e, f, Function.comp_def]
  have hbound (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (v) :
      (2 * δ) * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient (φ ∘ e)) x) v) v := by
    apply hessian_lowerBound_of_differentiable_convex_sub_quadratic
      ((hφ1.comp e.contDiff).differentiable (by simp)) hφconv
    exact (contDiffAt_gradient ((hφs (e x) (by simpa [e] using hx)).comp x
      e.contDiff.contDiffAt)).differentiableAt (by simp)
  refine ⟨φ, ⟨hφs, ?_, ?_, ?_⟩, hφ1, ?_, δ, hδ, hφconv, ?_, hbound⟩
  · intro r hr x
    dsimp [φ, quadraticPerturbation, f]
    rw [mollifiedSupportPrepotential_smul I ε hε hr.le, realSquaredNorm_smul]
    ring
  · intro x hx v hv
    exact lt_of_lt_of_le (by positivity : 0 < (2 * δ) * ‖v‖ ^ 2) (hbound x hx v)
  · intro v hv
    exact hδstar ⟨v, hv⟩
  · simp [φ, quadraticPerturbation, f, realSquaredNorm]
  · intro x
    simp only [φ, quadraticPerturbation, realSquaredNorm_euclidean]
    exact le_add_of_nonneg_left (sq_nonneg _)

end FsFltz
