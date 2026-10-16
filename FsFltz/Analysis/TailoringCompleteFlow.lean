import FsFltz.Analysis.TailoringIntrinsicGrowth
import FsFltz.Geometry.EmbeddedLogarithmicCompleteFlow
import FsFltz.Geometry.FixedAmbient

/-!
# Actual complete full tailored fibers

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1221–1237.
The constructed native intrinsic linear growth controls a proper exhaustion
and produces both-time complete flows on the entire literal level-one fibers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- One threshold gives actual full smooth fibers with literal restricted
complete primitives for every prescribed homotopy parameter. The flow is
constructed from the proved native growth estimate, not supplied as input. -/
theorem tailoringFamily_exists_uniform_completeFullFiber
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {Rend : ℝ} (hRend : 0 < Rend)
    (heq : ∀ u, Rend ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        range j.map = {y | tailoringFamily I β s y = 1} ∧
          Nonempty (CompletePrimitive N
            (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) := by
  obtain ⟨C, hC, R, hR, β₀, hβ₀, hfiber⟩ :=
    tailoringFamily_exists_uniform_fullFiber_intrinsic_growth I hφ hc hU hlower hupper
      hEnd hhom hRend heq
  refine ⟨β₀, hβ₀, fun β hβ s hs => ?_⟩
  obtain ⟨N, j, himage, hsymp, hgrowth⟩ := hfiber β hβ s hs
  let μ := N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)
  have hμ := N.isSmoothForm_pullback_one (lgManifold n) j.map _
    (isSmoothForm_lambdaPotentialForm hφ)
  have hZ := N.isSmoothVectorField_liouvilleVector μ hμ
    (fun x => hsymp.2.2 x (mem_univ _))
  have hclosed : IsClosed (range j.map) := by
    let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    rw [himage]
    exact isClosed_eq (contMDiff_tailoringFamily_lgManifold I β s).continuous continuous_const
  obtain ⟨flow⟩ := exists_completeFlow_of_closedEmbedding_logarithmic_growth N j hclosed
    (N.liouvilleVector μ) hZ hC hR hgrowth
  refine ⟨N, j, himage, ⟨{
    smooth_primitive := hμ
    symplectic := hsymp
    smooth_field := hZ
    contraction := ?_
    completeFlow := flow }⟩⟩
  intro x
  exact N.liouvilleVector_contraction μ x
    (N.liouvilleEquation_exists μ x (hsymp.2.2 x (mem_univ _)))

end FsFltz
