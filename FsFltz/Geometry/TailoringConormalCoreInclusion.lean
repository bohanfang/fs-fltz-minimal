import FsFltz.Geometry.TailoringConormalFlow
import FsFltz.Geometry.TailoringLyapunovCompletion

/-!
# The conormal section lies in the actual marked full core

Source: `geometric-part-fsf-proof.tex`, `thm:core`, line 1737.
Compact intrinsic invariance and the actual inclusion marking identify
section points with points of every completion's native full core.
The reverse inclusion is not asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

/-- Construct actual full-fiber truncations and prove the first embedded
full-core inclusion for every one of their completions. -/
theorem tailoringEndpoint_exists_uniform_conormal_subset_fullCore
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
        (himage : range j.map = {y | tailoringFamily I β 1 y = 1}),
      ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
        ∃ hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
          0 < N.scalarDerivative (fun y => φ (j.map y).1) x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x),
        let D := tailoringFiberOutwardDomain hφ hEnd1 hEnd.smooth
          hEnd.homogeneous hc hlower hR heq I β 1 j himage P A hpos
        j.map '' D.domain.carrier = {y | tailoringFamily I β 1 y = 1 ∧ φ y.1 ≤ A} ∧
          Nonempty (Completion D) ∧ ∀ C : Completion D,
            Nonempty (InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val)) ∧
            tailoringCoreSection I φEnd β ⊆ j.map '' C.core := by
  obtain ⟨Bi, _, hinv⟩ := tailoringEndpoint_exists_uniform_fullFiber_conormal_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨F, hF, Bm, hBm, hmark⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd.smooth hEnd.homogeneous hR heq
  refine ⟨F, hF, max Bm Bi, hBm.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨N, j, P, himage, hdomains⟩ := hmark β ((le_max_left _ _).trans hβ) 1 (by simp)
  have horbits := (hinv β ((le_max_right _ _).trans hβ) N j himage P.completeFlow).2.2
  refine ⟨N, j, P, himage, ?_⟩
  intro A hA
  obtain ⟨hpos, him, hC, hq⟩ := hdomains A hA
  refine ⟨hpos, him, hC, ?_⟩
  intro C
  refine ⟨hq C, ?_⟩
  intro y hy
  have hyfiber : tailoringFamily I β 1 y = 1 := hy.2
  have hymem : y ∈ range j.map := by rw [himage]; exact hyfiber
  obtain ⟨x, rfl⟩ := hymem
  refine ⟨x, ?_, rfl⟩
  rw [tailoringFiberOutwardDomain_core_eq_relativelyCompact_forwardOrbit hφ hEnd1
    hEnd.smooth hEnd.homogeneous hc hlower hR heq I β 1 j himage P A hpos C]
  exact (horbits x hy).2

end FsFltz
