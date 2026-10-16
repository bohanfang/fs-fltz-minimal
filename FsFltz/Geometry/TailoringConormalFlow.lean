import FsFltz.Geometry.TailoringConormalInvariance
import FsFltz.Geometry.LogarithmicIntegralCurve
import FsFltz.Geometry.FlowBridge
import FsFltz.Analysis.ClosedFlowInvariance
import FsFltz.Analysis.TailoringCompleteFlow

/-!
# Two-sided invariance for the actual full-fiber Liouville flow

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1625–1658,
and the first inclusion of `thm:core`, line 1737. Local coordinate
invariance is transported to the native fiber, then extended to all real
times using compactness and connectedness. No invariance is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

theorem tailoringEndpoint_exists_uniform_fullFiber_conormal_local_invariance
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ (γ : ℝ → N.Point) (t₀ : ℝ),
      IsMIntegralCurveAt γ
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) t₀ →
      j.map (γ t₀) ∈ tailoringCoreSection I φEnd β →
      ∀ᶠ t in 𝓝 t₀, j.map (γ t) ∈ tailoringCoreSection I φEnd β ∧
        (j.map (γ t)).2 = (j.map (γ t₀)).2 := by
  obtain ⟨Bc, hBc, hcover⟩ := tailoringEndpoint_exists_uniform_cover_conormal_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bp, _, hpush⟩ := tailoringEndpoint_exists_uniform_fullFiber_projectedRadial
    I hφ hc hU hlower hupper hEnd hR heq
  refine ⟨max Bc Bp, hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage γ t₀ hγ hstart
  let V := fun z : TangentCoordinates n =>
    coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1))
      (fderiv ℝ (fun a => tailoringFamily I β 1 (lgCover a)) z) (z.1, 0)
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map (γ t₀))
  obtain ⟨ξ, hξ, hξode, hξcover⟩ := exists_logarithmic_integralCurve_lift N j.map
    _ V (fun a z hz => (hpush β ((le_max_right _ _).trans hβ) N j himage a z hz).2)
    hγ x hx.symm
  have hstart' : lgCover (ξ t₀) ∈ tailoringCoreSection I φEnd β := by
    rw [hξ, hx]
    exact hstart
  have hlocal := hcover β ((le_max_left _ _).trans hβ) ξ t₀ hξode hstart'
  filter_upwards [hlocal, hξcover] with t ht hct
  refine ⟨hct ▸ ht.1, ?_⟩
  rw [← hct, ← hx, ← hξ]
  exact congrArg angleQuotient ht.2

theorem tailoringEndpoint_exists_uniform_fullFiber_conormal_invariance
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ F : CompleteLiouvilleFlow N
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
      IsCompact (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
      IsInvariant F.flow (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
      ∀ a : N.Point, j.map a ∈ tailoringCoreSection I φEnd β →
        (∀ t : ℝ, (j.map (F.flow t a)).2 = (j.map a).2) ∧
        IsCompact (closure (F.flow.forwardOrbit a)) := by
  obtain ⟨Bl, hBl, hlocal⟩ := tailoringEndpoint_exists_uniform_fullFiber_conormal_local_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bk, hcompact⟩ := eventually_atTop.mp
    (hEnd.eventually_coreSection_compact Φ hΦeq hΦ₀)
  refine ⟨max Bl Bk, hBl.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage F
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hsection := hcompact β ((le_max_right _ _).trans hβ)
  have hjclosed : Topology.IsClosedEmbedding j.map := ⟨j.embedding, by
    rw [himage]
    exact isClosed_eq (contMDiff_tailoringFamily_lgManifold I β 1).continuous continuous_const⟩
  have hK := hjclosed.isCompact_preimage hsection
  have hloc := hlocal β ((le_max_left _ _).trans hβ) N j himage
  have hinv : IsInvariant F.flow (j.map ⁻¹' tailoringCoreSection I φEnd β) := by
    apply flow_isInvariant_of_closed_local F.flow hK.isClosed
    intro a ha
    have hh := hloc (fun t => F.flow t a) 0 ((F.isMIntegralCurve a).isMIntegralCurveAt 0)
      (by simpa using ha)
    exact hh.mono fun _ ht => ht.1
  refine ⟨hK, hinv, ?_⟩
  intro a ha
  refine ⟨?_, isCompact_closure_forwardOrbit_of_mem_invariant F.flow hK hinv ha⟩
  intro t
  let A : Set N.Point := {b | j.map b ∈ tailoringCoreSection I φEnd β ∧
    (j.map b).2 = (j.map a).2}
  have hA : IsClosed A := hK.isClosed.inter
    (isClosed_eq (continuous_snd.comp j.map.contMDiff.continuous) continuous_const)
  have hmem : F.flow t a ∈ A := by
    refine mem_closed_of_locally_mem hA
      (F.flow.continuous continuous_id (continuous_const (y := a))) ?_ (t₀ := 0)
      (by simpa [A] using ha) t
    intro s hs
    have hh := hloc (fun t => F.flow t a) s ((F.isMIntegralCurve a).isMIntegralCurveAt s) hs.1
    exact hh.mono fun _ ht => ⟨ht.1, ht.2.trans hs.2⟩
  exact hmem.2

/-- The full endpoint presentation and its both-time intrinsic flow are
constructed from the same potential. Their actual conormal section is invariant. -/
theorem tailoringEndpoint_exists_uniform_complete_invariant_section
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
        range j.map = {y | tailoringFamily I β 1 y = 1} ∧
        IsCompact (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
        IsInvariant P.completeFlow.flow (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
        ∀ a : N.Point, j.map a ∈ tailoringCoreSection I φEnd β →
          (∀ t : ℝ, (j.map (P.completeFlow.flow t a)).2 = (j.map a).2) ∧
          IsCompact (closure (P.completeFlow.flow.forwardOrbit a)) := by
  obtain ⟨Bi, hBi, hinv⟩ := tailoringEndpoint_exists_uniform_fullFiber_conormal_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bf, _, hfiber⟩ := tailoringFamily_exists_uniform_completeFullFiber
    I hφ hc hU hlower hupper hEnd.smooth hEnd.homogeneous hR heq
  refine ⟨max Bi Bf, hBi.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨N, j, himage, ⟨P⟩⟩ := hfiber β ((le_max_right _ _).trans hβ) 1 (by simp)
  exact ⟨N, j, P, himage,
    hinv β ((le_max_left _ _).trans hβ) N j himage P.completeFlow⟩

end FsFltz
