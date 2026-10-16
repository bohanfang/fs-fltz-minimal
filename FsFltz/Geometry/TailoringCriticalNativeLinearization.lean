import FsFltz.Geometry.TailoringNativeGradientLinearization

/-!
# Constructed critical tori have the actual positive normal linearization

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1538–1570,
and `lem:stable`, lines 1709–1724. All face weights, multipliers, chart
Hessians and normal positivity hypotheses are produced by the actual
constrained-minimum and reduced branches. No gradient identity, field zero,
normal positivity or branch parametrization is supplied as input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz
open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

/-- The actual reduced branch supplies the native field and its strictly
positive normal linearization at every point of its full face torus. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_face_native_positive_linearization {n : ℕ}
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φEnd (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        (∀ v, 0 < (z β⁻¹).1 v) ∧ 0 < β * (z β⁻¹).2 ∧
        (∃ O : Set (RealSpace n), IsOpen O ∧ faceCriticalRadius x z β ∈ O ∧
          ∀ u ∈ O, ∀ v ∈ tailoringExponents I,
            tailoringCutoff I β v u = if v = 0 ∨ v ∈ s then 1 else 0) ∧
        (∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          range j.map = {y | tailoringFamily I β 1 y = 1} ∧
          N.IsSymplecticOn
            (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ) ∧
        ∀ θ ∈ coneTorus (positiveCone s),
          tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
          tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
          ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
            range j.map = {y | tailoringFamily I β 1 y = 1} →
            ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
              lgCover ξ = (faceCriticalRadius x z β, θ) →
              ∃ C : NativeFaceHessianChart φ s
                  (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
                  (z β⁻¹).1 (β * (z β⁻¹).2) N j a ξ,
                C.coordinateField (chartAt (Model (2 * n - 2)) a a) = 0 ∧
                ((fun y => C.coordinateMetric y (C.coordinateField y)) =ᶠ[
                  𝓝 (chartAt (Model (2 * n - 2)) a a)] fderiv ℝ C.coordinatePotential) ∧
                (∀ v w, C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
                  (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
                  C.coordinateMetric (chartAt (Model (2 * n - 2)) a a) v
                    (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) w)) ∧
                (∀ v : Model (2 * n - 2), v ≠ 0 →
                  (∀ W ∈ faceConormalTangent s
                    (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β)) (z β⁻¹).1,
                    faceHessianMetric (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
                      (fderiv ℝ C.lift (chartAt (Model (2 * n - 2)) a a) v) W = 0) →
                  0 < C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
                    (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) v) := by
  classical
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  obtain ⟨x, z, hx₀, hm₀, hxs, has, hpos, hz₀, hzs, hsol, hzsol, _, hradial, hfiber⟩ :=
    hStrong.exists_actual_positive_faceReduced_branch hEnd1 hd hEndConv hs hsne hsproper
  have hμ : 0 < ∑ v, faceReducedCoefficient φEnd x 0 v :=
    Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hq₀ : ∀ v, 0 < (z 0).1 v := by
    intro v
    rw [hz₀]
    exact div_pos (hpos v) hμ
  have hμ₀ : 0 < (z 0).2 := by simpa only [hz₀] using hμ
  have hxne : x 0 ≠ 0 := ne_zero_of_mem_polarFacet I hsne.choose
    ⟨hx₀.1, hx₀.2 hsne.choose hsne.choose_spec⟩
  have hstrict := hStrong.strict_of_polarFace_minimum hs hsne hsproper hx₀ hm₀
  have hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1 := by
    intro v hv
    split_ifs with hvs
    · exact hx₀.2 v hvs
    · exact hstrict v hv hvs
  have hlevel : ∀ᶠ y in 𝓝 0, faceLevelMap s (x y) = fun v => 1 + y v := by
    filter_upwards [hsol] with y hy
    exact (mem_faceCoordinateSlice_iff s y (x y)).mp hy.1
  have hlevel' : ∀ᶠ y in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v := by
    filter_upwards [hlevel] with y hy v
    simpa only [faceLevelMap_apply] using congrFun hy v
  have hnative := actual_faceReduced_branch_eventually_native_critical hφ hEnd hs.1
    hxs hzs hface hq₀ hlevel' (hzsol.mono fun ε hε => ⟨hε.1, hε.2.2.2⟩) hradial hfiber
  have hblocks := hStrong.eventually_actual_face_hessian_blocks
    (hEnd1.differentiable one_ne_zero) hxs has hzs hxne hq₀ hμ₀ hlevel
    (hsol.mono fun y hy => hy.2.1)
  have hpot := faceCriticalRadius_eventually_potential_germ_eq
    hxs.continuousAt hzs.continuousAt hxne hq₀ hEnd
  have hcut := critical_reduced_branch_eventually_face_plateaus I
    (hxs.differentiableAt (by simp)) hface (hzs.fst.differentiableAt (by simp)) hq₀
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter
        (hzs.fst.differentiableAt (by simp)) hq₀).continuousAt.tendsto.comp
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
  obtain ⟨_, _, _, _, Bπ, _, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Be, _, he⟩ := tailoringFamily_exists_uniform_symplectic_levelEmbedding
    I hφ hc hU hlower hupper
  suffices hall : ∀ᶠ β : ℝ in atTop,
      (∀ v, 0 < (z β⁻¹).1 v) ∧ 0 < β * (z β⁻¹).2 ∧
      (∃ O : Set (RealSpace n), IsOpen O ∧ faceCriticalRadius x z β ∈ O ∧
        ∀ u ∈ O, ∀ v ∈ tailoringExponents I,
          tailoringCutoff I β v u = if v = 0 ∨ v ∈ s then 1 else 0) ∧
      ∀ θ ∈ coneTorus (positiveCone s),
        tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
        tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
            lgCover ξ = (faceCriticalRadius x z β, θ) →
            ∃ C : NativeFaceHessianChart φ s
                (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
                (z β⁻¹).1 (β * (z β⁻¹).2) N j a ξ,
              C.coordinateField (chartAt (Model (2 * n - 2)) a a) = 0 ∧
              ((fun y => C.coordinateMetric y (C.coordinateField y)) =ᶠ[
                𝓝 (chartAt (Model (2 * n - 2)) a a)] fderiv ℝ C.coordinatePotential) ∧
              (∀ v w, C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
                (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) w =
                C.coordinateMetric (chartAt (Model (2 * n - 2)) a a) v
                  (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) w)) ∧
              (∀ v : Model (2 * n - 2), v ≠ 0 →
                (∀ W ∈ faceConormalTangent s
                  (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β)) (z β⁻¹).1,
                  faceHessianMetric (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
                    (fderiv ℝ C.lift (chartAt (Model (2 * n - 2)) a a) v) W = 0) →
                0 < C.coordinateMetric (chartAt (Model (2 * n - 2)) a a)
                  (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a) v) v) by
    obtain ⟨B, hB⟩ := eventually_atTop.mp hall
    refine ⟨x, z, hx₀, hm₀, hxs, hzs, max 1 (max B Be),
      zero_lt_one.trans_le (le_max_left _ _), ?_⟩
    intro β hβ
    have hβB := (le_max_left B Be).trans ((le_max_right 1 _).trans hβ)
    have hβe := (le_max_right B Be).trans ((le_max_right 1 _).trans hβ)
    exact ⟨(hB β hβB).1, (hB β hβB).2.1, (hB β hβB).2.2.1,
      he β hβe 1 (by simp) 1 (by simp), (hB β hβB).2.2.2⟩
  filter_upwards [hnative, hblocks, hpot, hcut, hparam.eventually hlevel',
    tendsto_inv_atTop_zero.eventually hzsol, hradial,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop Bπ]
    with β hn hb hp hcutβ hl hz hr hβ hβπ
  refine ⟨hz.1, mul_pos hβ hz.2.1, hcutβ, ?_⟩
  intro θ hθ
  have hchars : ∀ v : s, (character v.val θ : ℂ) = 1 :=
    fun v => (I.mem_coneTorus_positiveCone_iff hs hsne hsproper θ).mp hθ v.val v.property
  have hnativeθ := hn θ hchars
  refine ⟨hnativeθ.1, hnativeθ.2.1, ?_⟩
  intro N j himage a ξ hpoint hξ
  have hξrad : ξ.1 = faceCriticalRadius x z β := congrArg Prod.fst hξ
  obtain ⟨O, hO, huO, hcutO⟩ := hcutβ
  have hlocal := tailoringFamily_eventually_face_sum_of_plateau I β hs.1
    hnativeθ.1 hO huO hcutO
  have hlocal' : ∀ᶠ y in 𝓝 (j.map a), tailoringFamily I β 1 y =
      ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y := by
    rwa [hpoint, hξ]
  have hmon : ∀ v : s,
      monomial (Real.exp (-β) : ℂ) v.val (lgCover ξ) = ((z β⁻¹).1 v : ℂ) := by
    intro v
    rw [hξ]
    exact monomial_eq_weight_of_shifted_face_level hβ.ne' (hz.1 v)
      (by simpa only [Pi.smul_apply, smul_eq_mul] using hl v) (hchars v)
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β hβπ 1 (by simp) y _).2.2 (by simp only [hy, norm_one, le_refl])
  have hpξ : φ =ᶠ[𝓝 ξ.1] φEnd := hξrad ▸ hp
  have hrξ : coordinateGradient φEnd ξ.1 =
      (β * (z β⁻¹).2) • faceNormalMap s (z β⁻¹).1 := hξrad ▸ hr
  have hchart := tailoring_fullFiber_nonempty_nativeFaceHessianChart I β hφ hc hlower
    hpi s (β * (z β⁻¹).2) (z β⁻¹).1 N j himage a ξ hpoint hlocal' hpξ hmon hrξ
    hb.1 (hξrad ▸ hb.2.1) (hξrad ▸ hb.2.2.1) (hξrad ▸ hb.2.2.2.1)
    hz.1 (mul_pos hβ hz.2.1) hb.2.2.2.2.1
  obtain ⟨C⟩ : Nonempty (NativeFaceHessianChart φ s
      (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
      (z β⁻¹).1 (β * (z β⁻¹).2) N j a ξ) := by
    simpa only [hξrad] using hchart
  have hgood : ∀ᶠ p in 𝓝 (lgCover ξ), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1 := by
    have hnear : ∀ᶠ p : LGSpace n in 𝓝 (lgCover ξ), p.1 ∈ O := by
      apply continuous_fst.continuousAt.eventually
      exact hO.mem_nhds (hξrad.symm ▸ huO)
    filter_upwards [hnear] with p hp v hv
    rw [hcutO p.1 hp v hv]
    split_ifs <;> simp
  exact ⟨C, C.coordinateField_zero I β hφ hc hlower hpi himage hgood,
    C.coordinate_gradient I β hφ hc hlower hpi himage hgood,
    C.coordinate_linearization_selfadjoint I β hφ hc hlower hpi himage hgood,
    C.coordinate_linearization_pos_on_conormal_normal I β hφ hc hlower hpi himage hgood
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hz.1 (mul_pos hβ hz.2.1)⟩

end FsFltz
