import FsFltz.Geometry.TailoringConormalNative
import FsFltz.Analysis.TailoringFiberProjectionSmooth

/-!
# The smooth cover projected radial field on the entire native endpoint fiber

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1208–1220,
and `eq:intrinsiccone`, lines 1637–1647. No conormal restriction is imposed:
the local smooth ambient extension agrees with the pushed intrinsic field
at every actual endpoint-fiber point.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

theorem tailoringEndpoint_exists_uniform_fullFiber_projectedRadial
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ a : N.Point, ∀ x : TangentCoordinates n, j.map a = lgCover x →
      let V := fun y : TangentCoordinates n =>
        coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1))
          (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) y) (y.1, 0)
      ContDiffAt ℝ ∞ V x ∧
      mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map a
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a) =
          lgCoverTangent x (V x) := by
  obtain ⟨_, _, _, _, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Bs, _, hs⟩ :=
    tailoringFamily_exists_uniform_coverProjectedRadial_smooth I hφ hc hU hlower hupper
  obtain ⟨BR, _, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  refine ⟨max Bπ (max Bs BR), hBπ.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a x hpoint
  dsimp only
  have hf : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  have hx : tailoringFamily I β 1 (lgCover x) = 1 := hpoint ▸ hf
  refine ⟨hs β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) 1 (by simp) x
    (by simp [hx]), ?_⟩
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_left _ _).trans hβ) 1 (by simp) y _).2.2 (by simp [hy])
  have htan := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage a
  have hradius : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    have h := hrad β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
      1 (by simp) (lgCover x) hx
    rw [realEuclideanRadius_eq_norm] at h
    change R + 1 ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ at h
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end
    hφ hEnd.smooth hEnd.homogeneous hR heq hradius
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  have hZ : (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
    (lgManifold n).liouvilleVector_eq _ _ hnd
      (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)
  have hkernel : (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map a).range =
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1)
        (j.map a))).ker ⊓
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1)
        (j.map a))).ker := by
    rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
    exact htan
  have hp := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection N j
    (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) a
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map a))
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (hpi _ hf).ne' hkernel
  rw [hpoint, hZ] at hp
  exact hp.trans (lgCoverTangent_coverFiberProjection hφ x
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
      (contMDiff_tailoringFamily_lgManifold I β 1) (x.1, 0)).symm

end FsFltz
