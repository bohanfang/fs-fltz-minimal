import FsFltz.Geometry.PotentialFiberCompleteFlow
import FsFltz.Analysis.TailoringPoissonNative

/-!
# Literal regular holomorphic fibers of the actual potential

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 730–747,
and `lem:originalends`, lines 770–818. Positive actual Hessians transfer
holomorphic regularity to positive native Poisson pairing. The native
regular-level theorem constructs the whole fiber and its tangent kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

section RegularFiber

variable {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (I : ToricInput n)

include hφ hc hU hlower hupper

/-- A regular holomorphic point has strictly positive actual inverse-Hessian
square, with no metric positivity supplied separately. -/
theorem toricInverseMetricSq_potentialHessian_pos (y : LGSpace n) (ha : 0 < a I y) :
    0 < toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1)) I y := by
  have hs := inner_fderiv_gradient_symmetric
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) (WithLp.toLp 2 y.1)
  have hp : ∀ v, 0 ≤ inner ℝ
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1) v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg ‖v‖)).trans (hlower _ v)
  exact (div_pos ha hU).trans_le
    (a_div_le_toricInverseMetricSq _ hs hp hU (hupper _) I y)

omit hφ hc hU hlower hupper in
/-- The actual full regular holomorphic fiber has its literal tangent kernel. -/
theorem potential_W_levelEmbedding_tangent_range (w : ℂ)
    (ha : ∀ y, W I y = w → 0 < a I y)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | W I y = w}) (x : N.Point) :
    (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker := by
  have hreg := fun y hy => complexDifferential_W_surjective_of_a_pos I y (ha y hy)
  have ht := @regularLevel_embedding_tangent_range (2 * n) (lgManifold n) ℂ
    inferInstance inferInstance inferInstance (W I) w (contMDiff_W_lgManifold I) hreg
  rw [Complex.finrank_real_complex] at ht
  exact ht j himage x

/-- The native Poisson pairing on a regular holomorphic point is positive
for the actual chosen positive-Hessian potential. -/
theorem planePairing_potential_W_pos (y : LGSpace n) (ha : 0 < a I y)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) :
    0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) y hnd := by
  obtain ⟨z, hz⟩ := lgCover_surjective n y
  have hp : ∀ (y : (lgManifold n).Point) (hy : y = lgCover z)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) y h =
        toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)) I y := by
    intro y hy h
    subst y
    exact planePairing_W_potentialHessian hφ hc hlower I z h
  rw [hp y hz.symm hnd]
  have ha' : 0 < a I (lgCover z) := by rwa [hz]
  have hpos := toricInverseMetricSq_potentialHessian_pos hφ hc hU hlower hupper I (lgCover z) ha'
  change 0 < toricInverseMetricSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)) I (lgCover z) at hpos
  simpa only [hz] using hpos

/-- Any smooth realization of the literal full regular holomorphic level
inherits the actual restricted symplectic form. -/
theorem isSymplecticOn_potential_W_level (w : ℂ)
    (ha : ∀ y, W I y = w → 0 < a I y)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | W I y = w}) :
    N.IsSymplecticOn
      (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ := by
  apply (N.isSymplecticOn_exteriorDerivative_iff _
    (N.isSmoothForm_pullback_one (lgManifold n) j.map _ (isSmoothForm_lambdaPotentialForm hφ)) univ).mpr
  intro x _
  have hx : W I (j.map x) = w := by
    have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
    rwa [himage] at hx
  let hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map x)
  apply (lgManifold n).nondegenerate_pullback_of_rankTwo_kernel N j _
    (isSmoothForm_lambdaPotentialForm hφ) x hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) (j.map x)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) (j.map x)))
    (planePairing_potential_W_pos hφ hc hU hlower hupper I _ (ha _ hx) hnd).ne'
  rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
  exact potential_W_levelEmbedding_tangent_range I w ha j himage x

/-- Regularity constructs the actual full smooth fiber with its literal
restricted symplectic primitive, also in dimension zero. -/
theorem exists_potential_W_level_symplecticEmbedding (w : ℂ)
    (ha : ∀ y, W I y = w → 0 < a I y) :
    ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | W I y = w} ∧
        N.IsSymplecticOn
          (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ := by
  apply (lgManifold n).exists_planeFiber_symplecticEmbedding (lambdaPotentialForm φ)
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (W I) (contMDiff_W_lgManifold I) w
  intro y hy
  exact (planePairing_potential_W_pos hφ hc hU hlower hupper I y (ha y hy) _).ne'

end RegularFiber

end FsFltz.Geometry
