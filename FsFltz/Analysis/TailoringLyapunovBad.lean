import FsFltz.Analysis.TailoringLyapunovCoordinates
import FsFltz.Analysis.TailoringBadSeparation

/-!
# Strict intrinsic Lyapunov positivity in the actual bad region

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1478–1489.
Actual bad-region conormal separation gives a quantitative intrinsic-vector
lower bound. The nearby complex-rotated actual tangent then gives positivity
by the Liouville contraction equation and the positive potential Hessian.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- Bad-region separation forces the actual intrinsic vector to control the
actual potential gradient, uniformly over the entire endpoint fiber. -/
theorem tailoringEndpoint_exists_uniform_bad_projectedLiouville_gradient_bound
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
    ∃ K : ℝ, 0 < K ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      (∃ v ∈ tailoringExponents I,
        0 < tailoringCutoff I β v x.1 ∧ tailoringCutoff I β v x.1 < 1) →
      ∀ (hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
        (q : TangentCoordinates n),
      lgCoverTangent x q = (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) →
      ‖coordinateGradient φ x.1‖ ≤ K * ‖q‖ := by
  obtain ⟨A, hA, D, hD, B, hB, hcon⟩ :=
    tailoringEndpoint_exists_uniform_projectedLiouville_conormal_bound I hφ hc hU hlower hupper
  obtain ⟨δ, hδ, B', _, hsep⟩ :=
    tailoringEndpoint_exists_uniform_bad_conormal_separation I hstrong ha hEndLower
  obtain ⟨Bg, _, hgrad⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  have hlim : Tendsto (fun β : ℝ => A * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const (half_pos hδ))
  refine ⟨2 * D / δ, by positivity, max B (max B' (max Bg Be)),
    hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ x hx hbad hnd q hq
  have hBβ := (le_max_left B (max B' (max Bg Be))).trans hβ
  have hB'β := (le_max_left B' (max Bg Be)).trans ((le_max_right B _).trans hβ)
  have hBgβ := (le_max_left Bg Be).trans ((le_max_right B' _).trans ((le_max_right B _).trans hβ))
  have hBeβ := (le_max_right Bg Be).trans ((le_max_right B' _).trans ((le_max_right B _).trans hβ))
  obtain ⟨t, ht⟩ := hcon β hBβ x hx hnd q hq
  have hg := hgrad β hBgβ 1 (by simp) (lgCover x) hx
  have hs := hsep β hB'β (lgCover x) hx hbad t
  rw [← hg] at hs
  change δ * ‖coordinateGradient φ x.1‖ ≤ _ at hs
  have hsmall := mul_le_mul_of_nonneg_right (he β hBeβ).le
    (norm_nonneg (coordinateGradient φ x.1))
  have hh := hs.trans ht
  have hb : ‖coordinateGradient φ x.1‖ * δ ≤ 2 * D * ‖q‖ := by nlinarith
  exact ((le_div_iff₀ hδ).mpr hb).trans_eq (by ring)

/-- At every actual bad endpoint point the primitive-determined projected
Liouville field is strictly Lyapunov whenever it is nonzero. -/
theorem tailoringEndpoint_exists_uniform_bad_projectedLiouville_positive
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
      (∃ v ∈ tailoringExponents I,
        0 < tailoringCutoff I β v x.1 ∧ tailoringCutoff I β v x.1 < 1) →
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
  obtain ⟨K, hK, Bg, hBg, hgrad⟩ :=
    tailoringEndpoint_exists_uniform_bad_projectedLiouville_gradient_bound I hφ hc hU
      hlower hupper hstrong ha hEndLower hEnd
  obtain ⟨C, hC, Br, hBr, hrot⟩ := tailoringEndpoint_exists_uniform_nearby_rotated_tangent I
  let D := (2 * U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ 2 + n * K) * C
  have hlim : Tendsto (fun β : ℝ => D * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const (half_pos hc))
  refine ⟨max Bg (max Br Be), hBg.trans_le (le_max_left _ _), ?_⟩
  intro β hβ x hx hbad hnd hpi q hq hqne
  have hBgβ := (le_max_left Bg (max Br Be)).trans hβ
  have hBrβ := (le_max_left Br Be).trans ((le_max_right Bg _).trans hβ)
  have hBeβ := (le_max_right Br Be).trans ((le_max_right Bg _).trans hβ)
  have hfd := fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1) x
  have hqker : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x q = 0 := by
    rw [hfd, ContinuousLinearMap.comp_apply, hq]
    have hp := (lgManifold n).rankTwoFiberProjection_mem_kernel
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
      hpi ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x))
    apply Complex.ext
    · simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.zero_re] using hp.1
    · simpa only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Complex.zero_im] using hp.2
  obtain ⟨w, hw, hdist⟩ := hrot β hBrβ x hx q hqker
  have hlo := tailoring_projectedLiouville_energy_lower I β x hφ hc hU hlower hupper
    hnd q hq w hw hK.le hdist (hgrad β hBgβ x hx hbad hnd q hq)
  have hnorm : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hqne)
  have herr := he β hBeβ
  have hpos : 0 < (c - D * Real.exp (-Real.sqrt β)) * ‖q‖ ^ 2 :=
    mul_pos (by linarith) hnorm
  apply hpos.trans_le
  convert hlo using 1
  dsimp [D]
  ring

end FsFltz
