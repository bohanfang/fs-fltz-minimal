import FsFltz.Geometry.TailoringFullCoreReverseInclusion
import FsFltz.Analysis.PotentialPath

/-!
# The literal full endpoint core from finite toric input

Sources: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 626–643;
`lem:radial`, lines 1587–1621; `thm:core`, lines 1728–1750.
The potentials are constructed from the finite input. Every sufficiently
large actual truncation and every completion retain the same entire fiber,
its inclusion marking, and its literal embedded core.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz
open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology ContDiff
variable {n : ℕ}

/-- Constructed potentials give the actual complete endpoint fiber and,
for every large truncation and every completion, its full embedded core
and the prescribed literal radial image. -/
theorem ToricInput.exists_complete_tailoring_fullCore (I : ToricInput n) :
    ∃ (φEnd φ : RealSpace n → ℝ)
      (hStrong : IsStronglyCompatibleEndPotential I φEnd)
      (hEnd1 : ContDiff ℝ 1 φEnd) (hφ : ContDiff ℝ ∞ φ),
      φEnd 0 = 0 ∧
      ∃ (c U : ℝ) (hc : 0 < c) (_hU : 0 < U)
        (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
          inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
        (_hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
          inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤
            U * ‖v‖ ^ 2),
      (∃ a > 0, ∀ᶠ u in 𝓝 (0 : RealSpace n), φ u = a * realSquaredNorm u + 1) ∧
      ∃ (R : ℝ) (hR : 0 < R)
        (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u),
      ∃ ΦEnd Φ : RealSpace n ≃ₜ RealSpace n,
        (∀ u, ΦEnd u = coordinateGradient φEnd u) ∧ ΦEnd 0 = 0 ∧
        ContDiffOn ℝ ∞ ΦEnd ({0}ᶜ : Set (RealSpace n)) ∧
        ContDiffOn ℝ ∞ ΦEnd.symm ({0}ᶜ : Set (RealSpace n)) ∧
        (∀ u, Φ u = coordinateGradient φ u) ∧ ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
        ∃ F > 0, ∃ B > 0, ∀ β ≥ B,
          IsCompact (tailoringCoreSection I φEnd β) ∧
          BijOn (tailoringRadialProjection φEnd) (tailoringCoreSection I φEnd β) (fltzLink I) ∧
          tailoringRadialProjection φEnd '' tailoringCoreSection I φEnd β = fltzLink I ∧
          ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
            (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
            (himage : range j.map = {y | tailoringFamily I β 1 y = 1}),
          (∀ p : N.Point, IsCompact (closure (P.completeFlow.flow.forwardOrbit p)) ↔
            j.map p ∈ tailoringCoreSection I φEnd β) ∧
          ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
          ∃ hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
            0 < N.scalarDerivative (fun y => φ (j.map y).1) x
              (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x),
          let D := tailoringFiberOutwardDomain hφ hEnd1 hStrong.smooth hStrong.homogeneous
            hc hlower hR heq I β 1 j himage P A hpos
          j.map '' D.domain.carrier = {y | tailoringFamily I β 1 y = 1 ∧ φ y.1 ≤ A} ∧
            Nonempty (Completion D) ∧ ∀ C : Completion D,
              Nonempty (InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val)) ∧
              j.map '' C.core = tailoringCoreSection I φEnd β ∧
              tailoringRadialProjection φEnd '' (j.map '' C.core) = fltzLink I := by
  obtain ⟨φEnd, hStrong, hEnd1, hEnd0, d, hd, hconv, hEndLowerE, hbound⟩ :=
    I.exists_stronglyCompatibleEndPotential
  obtain ⟨φ, hφ, hlower, hnear, ⟨R, hR, heq⟩, Φ, hΦeq, hΦinv⟩ :=
    exists_native_smooth_extension_with_legendre hd hEnd1.continuous hEnd0
      hStrong.smooth hconv hEndLowerE
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨U, hU, hUnorm⟩ := exists_hessian_norm_bound_of_homogeneous_end hR
    (hφ.comp e.contDiff) (hEnd1.comp e.contDiff)
    (fun u hu => (hStrong.smooth (e u) (by simpa [e] using hu)).comp u e.contDiff.contDiffAt)
    (by
      intro r hr u
      change φEnd (e (r • u)) = r ^ 2 * φEnd (e u)
      rw [map_smul, hStrong.homogeneous r hr])
    (fun u hu => heq (e u) (by simpa [e] using hu))
  have hupper := hessian_upperBound_of_norm_bound hUnorm
  have hEndLower : ∀ u : RealSpace n, d * ‖u‖ ^ 2 ≤ φEnd u := by
    intro u
    have hn : ‖u‖ ≤ ‖e.symm u‖ := real_pi_norm_le_euclidean_norm u
    have hsq : ‖u‖ ^ 2 ≤ ‖e.symm u‖ ^ 2 := by
      nlinarith [norm_nonneg u, norm_nonneg (e.symm u)]
    exact (mul_le_mul_of_nonneg_left hsq hd.le).trans
      (by simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hEndLowerE (e.symm u))
  have hgrad0 : coordinateGradient φEnd 0 = 0 := by
    have hm : IsLocalMin φEnd 0 := Filter.Eventually.of_forall fun u => by
      rw [hEnd0]
      exact (mul_nonneg hd.le (sq_nonneg _)).trans (hEndLower u)
    ext i
    simp [coordinateGradient, hm.fderiv_eq_zero]
  let ΦEnd := strongConvexCoordinateGradientHomeomorph hEnd1 hd hconv hEndLowerE
  have hΦEndeq : ∀ u, ΦEnd u = coordinateGradient φEnd u :=
    fun u => strongConvexCoordinateGradientHomeomorph_apply hEnd1 hd hconv hEndLowerE u
  have hΦEnd0 : ΦEnd 0 = 0 := by simpa [ΦEnd] using hgrad0
  have hΦEnd : ContDiffOn ℝ ∞ ΦEnd ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_strongConvexCoordinateGradientHomeomorph hEnd1 hd hconv hEndLowerE hStrong.smooth
  have hΦEndinv : ContDiffOn ℝ ∞ ΦEnd.symm ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_symm_strongConvexCoordinateGradientHomeomorph hEnd1 hd hconv hEndLowerE hgrad0
      hStrong.smooth (show 0 < 2 * d by positivity) hbound
  obtain ⟨Bc, hBc, hcore⟩ := tailoringEndpoint_exists_uniform_compactOrbit_iff_coreSection
    I hStrong hEnd1 hEnd0 hd hconv hEndLowerE hbound hd hEndLower hφ hd hU hlower hupper
    ΦEnd hΦEndeq hΦEnd0 hΦEnd hΦEndinv hR heq
  obtain ⟨F, hF, Bm, _, hmark⟩ := tailoringFamily_exists_uniform_fullFiber_markings I
    hφ hd hU hlower hupper hEnd1 hStrong.smooth hStrong.homogeneous hR heq
  obtain ⟨Br, hradial⟩ := eventually_atTop.mp
    (hStrong.eventually_coreSection_projection_bijOn ΦEnd hΦEndeq hΦEnd0)
  obtain ⟨Bk, hcompact⟩ := eventually_atTop.mp
    (hStrong.eventually_coreSection_compact ΦEnd hΦEndeq hΦEnd0)
  refine ⟨φEnd, φ, hStrong, hEnd1, hφ, hEnd0, d, U, hd, hU, hlower, hupper,
    ⟨d / 2, by positivity, hnear⟩, R, hR, heq, ΦEnd, Φ,
    hΦEndeq, hΦEnd0, hΦEnd, hΦEndinv, hΦeq, ?_, hΦinv, F, hF,
    max Bc (max Bm (max Br Bk)), hBc.trans_le (le_max_left _ _), ?_⟩
  · have he : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦeq
    rw [he]
    exact contDiff_coordinateGradient hφ
  · intro β hβ
    have hβc : Bc ≤ β := (le_max_left _ _).trans hβ
    have hβm : Bm ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
    have hβr : Br ≤ β := (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
    have hβk : Bk ≤ β := (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
    have hb := hradial β hβr
    obtain ⟨N, j, P, himage, hmarkβ⟩ := hmark β hβm 1 (by simp)
    have hiff := hcore β hβc N j himage P.completeFlow
    refine ⟨hcompact β hβk, hb, hb.image_eq, N, j, P, himage, hiff, ?_⟩
    intro A hA
    obtain ⟨hpos, hdomain, hcompletion, hmarkC⟩ := hmarkβ A hA
    refine ⟨hpos, hdomain, hcompletion, ?_⟩
    intro C
    have he : j.map '' C.core = tailoringCoreSection I φEnd β := by
      rw [tailoringFiberOutwardDomain_core_eq_relativelyCompact_forwardOrbit hφ hEnd1
        hStrong.smooth hStrong.homogeneous hd hlower hR heq I β 1 j himage P A hpos C]
      apply Set.Subset.antisymm
      · rintro y ⟨p, hp, rfl⟩
        exact (hiff p).mp hp
      · intro y hy
        have hm : y ∈ range j.map := by
          rw [himage]
          exact hy.2
        obtain ⟨p, rfl⟩ := hm
        exact ⟨p, (hiff p).mpr hy, rfl⟩
    exact ⟨hmarkC C, he, by rw [he]; exact hb.image_eq⟩

end FsFltz
