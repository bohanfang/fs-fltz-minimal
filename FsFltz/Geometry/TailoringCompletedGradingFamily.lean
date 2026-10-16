import FsFltz.Geometry.RankTwoMaslovVaryingFamily
import FsFltz.Geometry.TailoringCompletedGradingNative

/-!
# Constructed native grading family for the tailoring path

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
The real and imaginary covectors of the actual affine tailoring family
vary jointly smoothly. Uniform Poisson positivity then constructs an
actual native Maslov family whose slices are precisely the representatives
used by the cylindrical completion construction. Regularity after the
retained completion presentations and prescribed-edge matching are separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

theorem isSmoothFormFamily_tailoringCovector (I : ToricInput n) (β : ℝ)
    (L : ℂ →L[ℝ] ℝ) :
    (lgManifold n).IsSmoothFormFamily (fun s => covectorForm (lgManifold n)
      (fun y => L.comp (complexDifferential (lgManifold n) (tailoringFamily I β s) y))) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let f := tailoringFamily I β 0
  let g := tailoringFamily I β 1 - tailoringFamily I β 0
  have he (s : ℝ) : tailoringFamily I β s = f + s • g := by
    funext y
    simp only [f, g, tailoringFamily, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  simp_rw [he]
  exact isSmoothFormFamily_complexDifferential_affine (lgManifold n)
    (contMDiff_tailoringFamily_lgManifold I β 0)
    ((contMDiff_tailoringFamily_lgManifold I β 1).sub
      (contMDiff_tailoringFamily_lgManifold I β 0)) L

/-- The actual native family along all tailoring parameters, with genuine
smooth real extensions at zero and one supplied by the shear construction. -/
def tailoringNativeMaslovFamily (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovFamily (lgManifold n) (fun s => (lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) :=
  (potentialMaslovRepresentative hφ hc hlower).rankTwoPrimitiveVaryingFamily
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (tailoringFamily I β) (fun s _ => contMDiff_tailoringFamily_lgManifold I β s)
    (isSmoothFormFamily_tailoringCovector I β Complex.reCLM)
    (isSmoothFormFamily_tailoringCovector I β Complex.imCLM)
    (fun _ => K) contDiff_const (fun s hs y =>
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK (hπ s hs y))))

/-- Every native slice is literally the representative consumed by the
actual cylindrical extension, including the endpoint slices. -/
theorem tailoringNativeMaslovFamily_slice (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) (s : ℝ) (hs : s ∈ parameterInterval) :
    (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK).J s =
      (tailoringNativeMaslov I hφ hc hlower β s (hπ s hs) K hK).J ∧
    (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK).tensor s =
      (tailoringNativeMaslov I hφ hc hlower β s (hπ s hs) K hK).tensor := ⟨rfl, rfl⟩

/-- A uniform threshold produces native Maslov families directly from the
Hessian bounds; no Maslov family occurs among the hypotheses. -/
theorem tailoringFamily_exists_uniform_native_maslov_family
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ K : ℝ, 0 ≤ K →
      Nonempty (MaslovFamily (lgManifold n) (fun s => (lgManifold n).exteriorDerivative
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K))) := by
  obtain ⟨_d, _hd, _R, _hR, B, hB, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨B, hB, ?_⟩
  intro β hβ K hK
  exact ⟨tailoringNativeMaslovFamily I hφ hc hlower β
    (fun s hs y => (hπ β hβ s hs y
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y)).1) K hK⟩

end FsFltz
