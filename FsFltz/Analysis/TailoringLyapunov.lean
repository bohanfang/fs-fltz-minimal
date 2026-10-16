import FsFltz.Analysis.TailoringLyapunovGood
import FsFltz.Analysis.TailoringLyapunovBad
import FsFltz.Analysis.TailoringFiberCriticalGood

/-!
# Strict intrinsic Lyapunov positivity on the entire endpoint full fiber

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1472–1496.
The good/bad split applies to the actual cutoff and the primitive-determined
intrinsic Liouville vector on every smooth presentation of the full fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- The actual projected Liouville vector is strictly Lyapunov on the entire
endpoint fiber. The threshold is independent of its point and presentation. -/
theorem tailoringEndpoint_exists_uniform_projectedLiouville_positive
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ (hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)),
      (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
        (lgCover x) hnd ≠ 0 → ∀ q : TangentCoordinates n,
      lgCoverTangent x q = (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) → q ≠ 0 →
      0 < (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x q) := by
  obtain ⟨B, hB, hbad⟩ := tailoringEndpoint_exists_uniform_bad_projectedLiouville_positive
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  refine ⟨B, hB, ?_⟩
  intro β hβ x hx hnd hpi q hq hqne
  by_cases hg : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1
  · exact tailoring_good_projectedLiouville_positive I β x hx hg hφ hc hlower hnd hpi q hq hqne
  · push Not at hg
    obtain ⟨v, hv, hzero, hone⟩ := hg
    exact hbad β hβ x hx ⟨v, hv,
      lt_of_le_of_ne (tailoringCutoff_nonneg I β v x.1) hzero.symm,
      lt_of_le_of_ne (tailoringCutoff_le_one I β v x.1) hone⟩ hnd hpi q hq hqne

/-- Strict positivity for the actual primitive-determined intrinsic field on
every full fiber presentation. No tangent or symplectic contracts are added
to the input: they are derived from the finite toric input and Hessian bounds. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_liouville_positive
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z ≠ 0 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) z
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z) := by
  obtain ⟨_, _, _, _, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Bpos, _, hpos⟩ := tailoringEndpoint_exists_uniform_projectedLiouville_positive
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  refine ⟨max Bπ Bpos, hBπ.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hzero
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_left _ _).trans hβ) 1 (by simp) y _).2.2 (by simp [hy])
  have hz : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map z)
  have hkernel := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1
    hpi j himage z
  let Z := N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z
  let D := mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map z
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map z)
  have hpush := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) z hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map z)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map z)))
    (hpi (j.map z) hz).ne'
    (hkernel.trans ((lgManifold n).complexDifferential_ker_eq_real_inf_imag _ _))
  have hchain := mfderiv_comp_apply z
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map z))
    (j.map.contMDiff.mdifferentiable (by simp) z) Z
  change N.scalarDerivative (fun y => φ (j.map y).1) z Z =
    (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map z) (D Z) at hchain
  rw [hchain]
  have hDne : D Z ≠ 0 := fun he => hzero (j.immersion z (he.trans D.map_zero.symm))
  have hpositive : ∀ (y : LGSpace n) (hy : y = lgCover x)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      tailoringFamily I β 1 y = 1 →
      (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y h ≠ 0 →
      ∀ v : (lgManifold n).Tangent y,
        v = (lgManifold n).rankTwoFiberProjection
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y h
          (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
          (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) →
        v ≠ 0 → 0 < (lgManifold n).scalarDerivative (fun u => φ u.1) y v := by
    intro y hy h hf hp v hv hvne
    subst y
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    apply hpos β ((le_max_right _ _).trans hβ) x hf h hp q hv
    exact fun hq => hvne (by rw [hq, map_zero])
  exact hpositive (j.map z) hx.symm hnd hz (hpi (j.map z) hz).ne' (D Z) hpush hDne

/-- The full-fiber intrinsic zero set is exactly its potential critical set.
Critical-to-zero uses strict positivity; zero-to-critical uses the proved
good-point classification and the complex tangent contraction identity. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_iff_liouville_zero
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      (∀ v : N.Tangent z, N.scalarDerivative (fun y => φ (j.map y).1) z v = 0) ↔
      N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0 := by
  obtain ⟨Bpos, hBpos, hpos⟩ := tailoringEndpoint_exists_uniform_fullFiber_liouville_positive
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  obtain ⟨Bgood, _, hgood⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_good
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  obtain ⟨_, _, _, _, Bπ, _, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨max Bpos (max Bgood Bπ), hBpos.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z
  have hβpos := (le_max_left Bpos (max Bgood Bπ)).trans hβ
  have hβgood := (le_max_left Bgood Bπ).trans ((le_max_right Bpos _).trans hβ)
  have hβπ := (le_max_right Bgood Bπ).trans ((le_max_right Bpos _).trans hβ)
  constructor
  · intro hcritical
    by_contra hzero
    have hp := hpos β hβpos N j himage z hzero
    rw [hcritical] at hp
    exact (lt_irrefl 0) hp
  · intro hzero
    have hg := hgood β hβgood N j himage z (Or.inr hzero)
    have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
        0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
          (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
      intro y hy
      exact (hπ β hβπ 1 (by simp) y _).2.2 (by simp [hy])
    have hz : tailoringFamily I β 1 (j.map z) = 1 := by
      have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
      rwa [himage] at hmem
    obtain ⟨x, hx⟩ := lgCover_surjective n (j.map z)
    exact tailoring_good_intrinsic_zero_is_critical I β x (hx.symm ▸ hz)
      (by simpa only [← hx, lgCover] using hg) hφ (2 * n - 2) N j z hx.symm
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map z))
      (hpi (j.map z) hz).ne'
      (tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage z) hzero

/-- The strict Lyapunov assertion, with the critical set stated intrinsically,
on every actual full endpoint fiber for the same fixed potential. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_strict_lyapunov
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun y => φ (j.map y).1) z v = 0) ↔
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) ∧
      (¬ (∀ v : N.Tangent z, N.scalarDerivative (fun y => φ (j.map y).1) z v = 0) →
        0 < N.scalarDerivative (fun y => φ (j.map y).1) z
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z)) := by
  obtain ⟨B, hB, hpos⟩ := tailoringEndpoint_exists_uniform_fullFiber_liouville_positive
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  obtain ⟨B', _, heq⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_iff_liouville_zero
    I hφ hc hU hlower hupper hstrong ha hEndLower hEnd
  refine ⟨max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z
  have he := heq β ((le_max_right _ _).trans hβ) N j himage z
  exact ⟨he, fun hnot => hpos β ((le_max_left _ _).trans hβ) N j himage z
    (fun hzero => hnot (he.mpr hzero))⟩

end FsFltz
