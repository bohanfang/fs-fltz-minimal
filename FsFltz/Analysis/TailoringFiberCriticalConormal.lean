import FsFltz.Analysis.TailoringCriticalConormalNative
import FsFltz.Analysis.TailoringIntrinsicGrowth
import FsFltz.Analysis.TailoringSupport

/-!
# Critical conormals on the actual full tailored endpoint fiber

Source: `geometric-part-fsf-proof.tex`, `eq:Gchi` and `lem:localcritical`,
lines 1343–1365 and 1428–1454. Uniform Poisson positivity constructs the
actual full smooth symplectic fiber and proves its tangent-image contract.
The critical conormal estimate therefore has no separately assumed
nondegeneracy, Poisson pairing, or tangent-image hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- Every full endpoint presentation has the intrinsic critical estimate,
with all regularity and tangent contracts discharged by actual producers. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_conormal_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ a : N.Point,
      ((∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
      ∃ t : ℂ,
        ‖(fun k => (coordinateGradient φ (j.map a).1 k : ℂ)) -
            t • tailoringRetainedNormal I β (j.map a)‖ ≤
          C * Real.exp (-Real.sqrt β) * ‖coordinateGradient φ (j.map a).1‖ := by
  obtain ⟨C, hC, B, hB, hcritical⟩ :=
    tailoringEndpoint_exists_uniform_embedded_critical_conormal_bound I
  obtain ⟨_, _, _, _, B', hB', hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨C, hC, max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a hcrit
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_right _ _).trans hβ) 1 (by simp) y _).2.2
      (by simp only [hy, norm_one, le_refl])
  have ha : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map a)
  have hfiber : tailoringFamily I β 1 (lgCover x) = 1 := hx.symm ▸ ha
  have htan := tailoringFamily_levelEmbedding_tangent_range
    I hφ hc hlower β 1 1 hpi j himage a
  have h := hcritical β ((le_max_left _ _).trans hβ) x hfiber φ hφ
    (2 * n - 2) N j a hx.symm
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map a))
    (hpi (j.map a) ha).ne' htan hcrit
  simpa only [← hx, lgCover] using h

/-- The actual full smooth symplectic endpoint fiber is produced together
with the intrinsic critical conormal estimate on that same embedding. -/
theorem tailoringEndpoint_exists_uniform_symplecticFullFiber_critical_conormal_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} ∧
      N.IsSymplecticOn
        (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ ∧
      ∀ a : N.Point,
      ((∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
      ∃ t : ℂ,
        ‖(fun k => (coordinateGradient φ (j.map a).1 k : ℂ)) -
            t • tailoringRetainedNormal I β (j.map a)‖ ≤
          C * Real.exp (-Real.sqrt β) * ‖coordinateGradient φ (j.map a).1‖ := by
  obtain ⟨C, hC, B, hB, hcrit⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_critical_conormal_bound I hφ hc hU hlower hupper
  obtain ⟨B', hB', hfull⟩ :=
    tailoringFamily_exists_uniform_symplectic_levelEmbedding I hφ hc hU hlower hupper
  refine ⟨C, hC, max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨N, j, himage, hsympl⟩ :=
    hfull β ((le_max_right _ _).trans hβ) 1 (by simp) 1 (by simp)
  exact ⟨N, j, himage, hsympl,
    hcrit β ((le_max_left _ _).trans hβ) N j himage⟩

/-- End agreement is an equality of actual derivatives on every full
level-one fiber once it lies strictly beyond the extension radius. -/
theorem tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd (I : ToricInput n)
    {φ φEnd : RealSpace n → ℝ} {R : ℝ}
    (hEnd : ∀ u, R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, tailoringFamily I β s y = 1 →
        coordinateGradient φ y.1 = coordinateGradient φEnd y.1 := by
  obtain ⟨B, hB, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  refine ⟨B, hB, fun β hβ s hs y hy => ?_⟩
  have hR : R < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    have hh := hrad β hβ s hs y hy
    rw [realEuclideanRadius_eq_norm] at hh
    change R + 1 ≤ ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ at hh
    linarith
  have heq : φ =ᶠ[𝓝 y.1] φEnd := by
    have hnorm : Continuous (fun u : RealSpace n =>
        ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖) :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.norm
    filter_upwards [hnorm.continuousAt.eventually (eventually_gt_nhds hR)] with u hu
    exact hEnd u hu.le
  ext j
  exact congrArg (fun L : RealSpace n →L[ℝ] ℝ => L (Pi.single j 1)) heq.fderiv_eq

/-- Intrinsic critical points on the full fiber satisfy the retained-line
estimate for the actual homogeneous-end gradient, using proved local
agreement of the extension's differential. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_end_critical_conormal_bound
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ a : N.Point,
      ((∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
      ∃ t : ℂ,
        ‖(fun k => (coordinateGradient φEnd (j.map a).1 k : ℂ)) -
            t • tailoringRetainedNormal I β (j.map a)‖ ≤
          C * Real.exp (-Real.sqrt β) * ‖coordinateGradient φEnd (j.map a).1‖ := by
  obtain ⟨C, hC, B, hB, hcritical⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_critical_conormal_bound I hφ hc hU hlower hupper
  obtain ⟨B', hB', hgrad⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  refine ⟨C, hC, max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a hcrit
  have hfiber : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  have he := hgrad β ((le_max_right _ _).trans hβ) 1 (by simp) (j.map a) hfiber
  simpa only [he] using hcritical β ((le_max_left _ _).trans hβ) N j himage a hcrit

end FsFltz
