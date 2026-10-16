import FsFltz.Geometry.TailoringConormalRadial
import FsFltz.Analysis.TailoringFiberCriticalConormal

/-!
# Uniform native conormal evaluation for the same end-extension potential

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1608–1617,
and `eq:intrinsiccone`, lines 1637–1647. All pointwise regularity,
off-cone, and Euler conditions are discharged below from the actual
potential, its prescribed homogeneous end, and the full endpoint fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

/-- The source's transverse evaluation is by the actual native ambient
Liouville field, uniformly on the actual conormal endpoint pieces. -/
theorem tailoringEndpoint_exists_uniform_conormal_ambient_transverse
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ σ ∈ faceFan I,
      ∀ x : TangentCoordinates n, coordinateGradient φEnd x.1 ∈ σ →
      (lgCover x).2 ∈ coneTorus σ → tailoringFamily I β 1 (lgCover x) = 1 →
      ∃ d : ℝ, 0 < d ∧
        complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) = (d : ℂ) := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  have hlog : Real.log (I.vertices.card : ℝ) ≤ L := Real.log_le_log hN (by linarith)
  obtain ⟨Bo, ho⟩ := eventually_atTop.mp (hEnd.eventually_offCone_cutoff_zero L)
  obtain ⟨Bd, hd⟩ := eventually_atTop.mp (tailoringRadialFunction_eventually_radial_positive I hL)
  obtain ⟨BR, hBR, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  refine ⟨max BR (max Bo Bd), hBR.trans_le (le_max_left _ _), ?_⟩
  intro β hβ σ hσ x hp hθ hx
  have hh : β - L ≤ supportHeight I x.1 := by
    have hh := tailoringEndpoint_height_lower I β (lgCover x) hx
    change β - Real.log (I.vertices.card : ℝ) ≤ supportHeight I x.1 at hh
    linarith
  have hoff := ho β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) σ hσ x.1 hp hh
  have hpositive := hd β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) x.1 hh
  have hradius : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    have h := hrad β ((le_max_left _ _).trans hβ) 1 (by simp) (lgCover x) hx
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
  refine ⟨_, hpositive, ?_⟩
  rw [hZ]
  change ((complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)).comp
    (lgCoverTangent x)) (x.1, 0) = _
  rw [← fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1),
    fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff]
  simp

/-- One threshold evaluates the actual native intrinsic field on every
conormal piece of every full endpoint presentation. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_conormal_liouville
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
      ∀ σ ∈ faceFan I, coordinateGradient φEnd x.1 ∈ σ → (lgCover x).2 ∈ coneTorus σ →
      let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
      mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map a
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a) =
      lgCoverTangent x
        (x.1 - (fderiv ℝ (tailoringRadialFunction I β) x.1 x.1 /
          coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)) •
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))), 0) := by
  obtain ⟨_, _, _, _, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨BR, hBR, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  obtain ⟨Bo, ho⟩ := eventually_atTop.mp
    (hEnd.eventually_offCone_cutoff_zero (Real.log (I.vertices.card : ℝ)))
  refine ⟨max Bπ (max BR Bo), hBπ.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a x hpoint σ hσ hp hθ
  dsimp only
  have hf : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  have hx : tailoringFamily I β 1 (lgCover x) = 1 := hpoint ▸ hf
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_left _ _).trans hβ) 1 (by simp) y _).2.2
      (by simp only [hy, norm_one, le_refl])
  have htan := tailoringFamily_levelEmbedding_tangent_range
    I hφ hc hlower β 1 1 hpi j himage a
  have hradius : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    have h := hrad β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ))
      1 (by simp) (lgCover x) hx
    rw [realEuclideanRadius_eq_norm] at h
    change R + 1 ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ at h
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end
    hφ hEnd.smooth hEnd.homogeneous hR heq hradius
  have hoff := ho β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
    σ hσ x.1 hp (tailoringEndpoint_height_lower I β (lgCover x) hx)
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  have hπx : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (lgCover x) hnd ≠ 0 := (hpi (lgCover x) hx).ne'
  exact native_liouvilleVector_tailoring_conormal I β σ x hx hθ hoff hφ
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hEuler
    (2 * n - 2) N j a hpoint hnd hπx htan

end FsFltz
