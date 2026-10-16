import FsFltz.Geometry.TailoringConormalFlow
import FsFltz.Analysis.PotentialPath

/-!
# An invariant complete endpoint section from finite toric input

Sources: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 626–643;
`lem:radial`, lines 1587–1621; `lem:invariance`, lines 1625–1659.
The same constructed end potential controls the actual conormal section,
its literal radial image, and the complete intrinsic Liouville flow.
This is an invariant compact section, not the full-core assertion of
`thm:core`, lines 1728–1749.
-/

noncomputable section

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

/-- Finite toric input produces one pair of admissible potentials and one
uniform large-parameter regime in which the actual complete endpoint fiber
has a compact invariant conormal section projecting onto the literal link. -/
theorem ToricInput.exists_complete_invariant_tailoring_section (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ φEnd 0 = 0 ∧
      ContDiff ℝ ∞ φ ∧
      (∃ c U : ℝ, 0 < c ∧ 0 < U ∧
        (∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
          inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) ∧
        (∀ u v : EuclideanSpace ℝ (Fin n),
          inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤
            U * ‖v‖ ^ 2)) ∧
      (∃ a > 0, ∀ᶠ u in 𝓝 (0 : RealSpace n), φ u = a * realSquaredNorm u + 1) ∧
      (∃ R > 0, ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
      ∃ ΦEnd Φ : RealSpace n ≃ₜ RealSpace n,
        (∀ u, ΦEnd u = coordinateGradient φEnd u) ∧ ΦEnd 0 = 0 ∧
        ContDiffOn ℝ ∞ ΦEnd ({0}ᶜ : Set (RealSpace n)) ∧
        ContDiffOn ℝ ∞ ΦEnd.symm ({0}ᶜ : Set (RealSpace n)) ∧
        (∀ u, Φ u = coordinateGradient φ u) ∧ ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
        ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
          IsCompact (tailoringCoreSection I φEnd β) ∧
          BijOn (tailoringRadialProjection φEnd) (tailoringCoreSection I φEnd β) (fltzLink I) ∧
          tailoringRadialProjection φEnd '' tailoringCoreSection I φEnd β = fltzLink I ∧
          ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
            (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
            range j.map = {y | tailoringFamily I β 1 y = 1} ∧
            IsCompact (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
            IsInvariant P.completeFlow.flow (j.map ⁻¹' tailoringCoreSection I φEnd β) ∧
            ∀ a : N.Point, j.map a ∈ tailoringCoreSection I φEnd β →
              (∀ t : ℝ, (j.map (P.completeFlow.flow t a)).2 = (j.map a).2) ∧
              IsCompact (closure (P.completeFlow.flow.forwardOrbit a)) := by
  obtain ⟨φEnd, hstrong, hEnd1, hEnd0, δ, hδ, hconv, hlower, hbound⟩ :=
    I.exists_stronglyCompatibleEndPotential
  obtain ⟨φ, hφ, hφlower, hnear, ⟨R, hR, heq⟩, Φ, hΦeq, hΦinv⟩ :=
    exists_native_smooth_extension_with_legendre hδ hEnd1.continuous hEnd0
      hstrong.smooth hconv hlower
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨U, hU, hUnorm⟩ := exists_hessian_norm_bound_of_homogeneous_end hR
    (hφ.comp e.contDiff) (hEnd1.comp e.contDiff)
    (fun u hu => (hstrong.smooth (e u) (by simpa [e] using hu)).comp u e.contDiff.contDiffAt)
    (by
      intro r hr u
      change φEnd (e (r • u)) = r ^ 2 * φEnd (e u)
      rw [map_smul, hstrong.homogeneous r hr])
    (fun u hu => heq (e u) (by simpa [e] using hu))
  have hupper := hessian_upperBound_of_norm_bound hUnorm
  have hgrad0 : coordinateGradient φEnd 0 = 0 := by
    have hm : IsLocalMin φEnd 0 := Filter.Eventually.of_forall fun u => by
      rw [hEnd0]
      simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using
        (mul_nonneg hδ.le (sq_nonneg _)).trans (hlower (e.symm u))
    ext i
    simp [coordinateGradient, hm.fderiv_eq_zero]
  let ΦEnd := strongConvexCoordinateGradientHomeomorph hEnd1 hδ hconv hlower
  have hΦEndeq : ∀ u, ΦEnd u = coordinateGradient φEnd u :=
    fun u => strongConvexCoordinateGradientHomeomorph_apply hEnd1 hδ hconv hlower u
  have hΦEnd0 : ΦEnd 0 = 0 := by simpa [ΦEnd] using hgrad0
  have hΦEnd : ContDiffOn ℝ ∞ ΦEnd ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_strongConvexCoordinateGradientHomeomorph hEnd1 hδ hconv hlower hstrong.smooth
  have hΦEndinv : ContDiffOn ℝ ∞ ΦEnd.symm ({0}ᶜ : Set (RealSpace n)) :=
    contDiffOn_symm_strongConvexCoordinateGradientHomeomorph hEnd1 hδ hconv hlower hgrad0
      hstrong.smooth (show 0 < 2 * δ by positivity) hbound
  obtain ⟨Bf, hBf, hfiber⟩ := tailoringEndpoint_exists_uniform_complete_invariant_section
    I hφ hδ hU hφlower hupper hstrong ΦEnd hΦEndeq hΦEnd0 hΦEnd hΦEndinv hR heq
  obtain ⟨Br, hradial⟩ := eventually_atTop.mp
    (hstrong.eventually_coreSection_projection_bijOn ΦEnd hΦEndeq hΦEnd0)
  obtain ⟨Bk, hcompact⟩ := eventually_atTop.mp
    (hstrong.eventually_coreSection_compact ΦEnd hΦEndeq hΦEnd0)
  refine ⟨φEnd, φ, hstrong, hEnd1, hEnd0, hφ, ⟨δ, U, hδ, hU, hφlower, hupper⟩,
    ⟨δ / 2, by positivity, hnear⟩, ⟨R, hR, heq⟩, ΦEnd, Φ,
    hΦEndeq, hΦEnd0, hΦEnd, hΦEndinv, hΦeq, ?_, hΦinv,
    max Bf (max Br Bk), hBf.trans_le (le_max_left _ _), ?_⟩
  · have he : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦeq
    rw [he]
    exact contDiff_coordinateGradient hφ
  · intro β hβ
    have hBr : Br ≤ β := (le_max_left Br Bk).trans ((le_max_right _ _).trans hβ)
    have hBk : Bk ≤ β := (le_max_right Br Bk).trans ((le_max_right _ _).trans hβ)
    have hb := hradial β hBr
    exact ⟨hcompact β hBk, hb, hb.image_eq, hfiber β ((le_max_left _ _).trans hβ)⟩

end FsFltz
