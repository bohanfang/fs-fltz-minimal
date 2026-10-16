import FsFltz.Geometry.TailoringCompletedGrading
import FsFltz.Geometry.PotentialLogarithmicGrading
import FsFltz.Geometry.TailoringRoundedCompletionMarking

/-!
# Constructed grading representatives on the actual tailored outer completions

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
Uniform Poisson positivity constructs native representatives for every
tailoring slice and every nonnegative base coefficient. The explicit
cylindrical shear then supplies representatives on the actual completed
outer domains, with literal recovery on their entire compact carriers.
This is a pointwise completed-data producer. Joint regularity through the
retained completion presentations and prescribed marked-edge matching are
not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The prescribed native logarithmic tensor is compatible with the
positive-Hessian potential primitive itself. -/
def potentialMaslovRepresentative {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) where
  J := logarithmicAlmostComplexField n
  tensor := logarithmicSquaredVolumeTensor n
  compatible := ⟨isSmoothAlmostComplexField_logarithmicAlmostComplexField n,
    logarithmicAlmostComplexField_sq, logarithmicAlmostComplexField_potential_symplectic hφ,
    logarithmicAlmostComplexField_potential_positive hφ hc hlower⟩
  canonical := logarithmicSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n
  nowhereZero := logarithmicSquaredVolumeTensor_ne_zero

/-- An actual native representative of each nonholomorphic tailoring
primitive, constructed from the potential grading and its Poisson scalar. -/
def tailoringNativeMaslov (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β s : ℝ)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β s) K)) :=
  (potentialMaslovRepresentative hφ hc hlower).nonnegativeRankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (tailoringFamily I β s) (contMDiff_tailoringFamily_lgManifold I β s) hπ K hK

/-- At zero coefficient the native representatives recover exactly the
prescribed potential representative, in both the complex field and tensor. -/
theorem tailoringNativeMaslov_zero (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β s : ℝ)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)) :
    (tailoringNativeMaslov I hφ hc hlower β s hπ 0 le_rfl).J = logarithmicAlmostComplexField n ∧
      (tailoringNativeMaslov I hφ hc hlower β s hπ 0 le_rfl).tensor =
        logarithmicSquaredVolumeTensor n := by
  constructor
  · funext y
    change rankTwoShearComplex _ _ 0 _ = _
    rw [rankTwoShearComplex_zero]
    rfl
  · funext y
    change rankTwoShearTensor _ _ 0 _ = _
    rw [rankTwoShearTensor_zero]
    rfl

end FsFltz.Geometry

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The geometric bounds and the Poisson estimate supply Maslov data on
every actual cylindrical outer completion. The threshold is fixed before
both tailoring parameters and all nonnegative base coefficients. -/
theorem tailoringFamily_exists_uniform_completed_outer_maslov
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ parameterInterval → ∀ K : ℝ, ∀ hK : 0 ≤ K,
      ∃ (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
          (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
        (hcompact : IsCompact {y : LGSpace n | φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0})
        (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
        (hout : ∀ y : (lgManifold n).Point, φ y.1 - D ^ 2 * β ^ 2 / 2 = 0 →
          0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - D ^ 2 * β ^ 2 / 2) y
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)),
      let E := tailoringPotentialOuterDomain I hφ β s K (D ^ 2 * β ^ 2 / 2) hcompact hω hout
      ∀ C : LiouvilleDomain.FlowCollar E,
        ∃ σ : MaslovRepresentative C.cylindricalCompletion.ambient.manifold
          (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
            C.cylindricalCompletion.ambient.primitive),
        ∀ z ∈ C.localizedDomain.domain.carrier,
          σ.J z = (tailoringNativeMaslov I hφ hc hlower β s hπ K hK).J z.val.val ∧
          σ.tensor z = (tailoringNativeMaslov I hφ hc hlower β s hπ K hK).tensor z.val.val := by
  obtain ⟨_d, _hd, _R, _hR, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨BD, _hBD, hdomain⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  refine ⟨max Bπ BD, hBπ.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs K hK
  have hπs := fun y => (hπ β ((le_max_left _ _).trans hβ) s hs y
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)).1
  obtain ⟨hcompact, _, hout⟩ := hdomain β ((le_max_right _ _).trans hβ)
  obtain ⟨hω, hout⟩ := hout s hs K hK
  refine ⟨hπs, hcompact, hω, hout, ?_⟩
  intro E C
  let τ := tailoringNativeMaslov I hφ hc hlower β s hπs K hK
  exact ⟨C.cylindricalMaslovOfNative τ, C.cylindricalMaslovOfNative_eq_on_carrier τ⟩

end FsFltz
