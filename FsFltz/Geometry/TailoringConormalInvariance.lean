import FsFltz.Geometry.TailoringConormalBranch
import FsFltz.Geometry.TailoringProjectedRadialNative
import FsFltz.Geometry.RetractFlowInvariance
import FsFltz.Geometry.LocalCovers
import FsFltz.Analysis.ToricConeNeighborhood
import FsFltz.Analysis.TailoringCriticalToriInertiaGlobal

/-!
# Native local invariance of the actual conormal endpoint section

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1585–1617,
`lem:invariance`, lines 1620–1659, and `thm:core`, lines 1728–1749.
The actual projected field is tangent to the constructed radial branch.
Local integral curves are constructed with the existing retraction theorem;
no cone invariance or branch tangency is supplied as an input certificate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

/-- On a conormal piece the Poisson scalar is exactly the radial differential
evaluated on the inverse-Hessian conormal vector. -/
theorem coverPlanePairing_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) =
      fderiv ℝ (tailoringRadialFunction I β) x.1
        ((EuclideanSpace.equiv (Fin n) ℝ)
          (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1)))) := by
  unfold coverPlanePairing coverPoissonBilinear
  rw [coverCovectorVector_im_angular_conormal I β σ x hx hθ hoff,
    coverCovectorVector_im_radial_conormal I β σ x hx hθ hoff]
  simp only [map_zero, inner_zero_left, sub_zero]
  rw [real_inner_comm, inner_coverCovectorVector]
  change (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
    ((EuclideanSpace.equiv (Fin n) ℝ)
      (H.symm (WithLp.toLp 2 (tailoringConormalVector I β x.1))), 0)).re = _
  rw [fderiv_tailoringFamily_one_conormal I β σ x hx hθ hoff]
  simp

/-- The actual projected radial velocity lies in the exact radial tangent
space of any constructed full-span section. -/
theorem coverProjectedRadial_mem_conormal_radial_tangent
    (I : ToricInput n) (β : ℝ) (σ : Set (RealSpace n))
    (x : TangentCoordinates n) (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hp : coordinateGradient φ x.1 ∈ Submodule.span ℝ σ)
    (hπ : coverPlanePairing H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ≠ 0) :
    let v := coverFiberProjection H (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x)
      (x.1, 0)
    fderiv ℝ (coordinateGradient φ) x.1 v.1 ∈ Submodule.span ℝ σ ∧
      fderiv ℝ (tailoringRadialFunction I β) x.1 v.1 = 0 ∧ v.2 = 0 := by
  dsimp only
  rw [coverFiberProjection_radial_conormal I β σ x hx hθ hoff H]
  refine ⟨?_, ?_, rfl⟩
  · rw [map_sub, map_smul, hEuler, coordinateHessian_eq_euclideanHessian hφ]
    change coordinateGradient φ x.1 - _ • (EuclideanSpace.equiv (Fin n) ℝ)
      (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
        (WithLp.toLp 2 x.1) (H.symm _)) ∈ _
    rw [hH, ContinuousLinearEquiv.apply_symm_apply]
    exact (Submodule.span ℝ σ).sub_mem hp ((Submodule.span ℝ σ).smul_mem _
      (tailoringConormalVector_mem_span I β σ x.1 hoff))
  · rw [map_sub, map_smul, ← coverPlanePairing_conormal I β σ x hx hθ hoff H]
    simp only [smul_eq_mul]
    field_simp
    ring

/-- A fixed lifted angle removes the zero angular block: radial tangent
membership is membership in the differential image of the actual lifted branch. -/
theorem mem_radialBranch_fderiv_range
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {g : K → RealSpace n} {q : K} (hg : DifferentiableAt ℝ g q)
    (θ : RealSpace n) (v : TangentCoordinates n)
    (hv : v.1 ∈ range (fderiv ℝ g q)) (hangle : v.2 = 0) :
    v ∈ range (fderiv ℝ (fun a => (g a, θ)) q) := by
  obtain ⟨a, ha⟩ := hv
  refine ⟨a, ?_⟩
  rw [(hg.hasFDerivAt.prodMk (hasFDerivAt_const θ q)).fderiv]
  exact Prod.ext ha (by simpa using hangle.symm)

/-- Both time directions near any point of the literal conormal section,
for the actual smooth logarithmic projected intrinsic field. -/
theorem tailoringEndpoint_exists_uniform_cover_conormal_invariance
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
      let V := fun z : TangentCoordinates n =>
        coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1))
          (fderiv ℝ (fun a => tailoringFamily I β 1 (lgCover a)) z) (z.1, 0)
      ∀ (γ : ℝ → TangentCoordinates n) (t₀ : ℝ),
        IsMIntegralCurveAt (I := 𝓘(ℝ, TangentCoordinates n)) γ V t₀ →
        lgCover (γ t₀) ∈ tailoringCoreSection I φEnd β →
        ∀ᶠ t in 𝓝 t₀, lgCover (γ t) ∈ tailoringCoreSection I φEnd β ∧
          (γ t).2 = (γ t₀).2 := by
  classical
  obtain ⟨Bπ, hBπ, hπ⟩ := tailoringFamily_exists_uniform_coverProjectedRadial_smooth
    I hφ hc hU hlower hupper
  obtain ⟨_, _, _, _, Bp, _, hp⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨BR, _, hrad⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  obtain ⟨Bg, hbg⟩ := eventually_atTop.mp
    (hEnd.eventually_exists_embedded_conormalBranch Φ hΦeq hΦ₀ hΦ hΦinv)
  obtain ⟨Bo, hbo⟩ := eventually_atTop.mp
    (hEnd.eventually_offCone_cutoff_germ (Real.log (I.vertices.card : ℝ)))
  refine ⟨max Bπ (max Bp (max BR (max Bg Bo))), hBπ.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  dsimp only
  let V := fun z : TangentCoordinates n =>
    coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1))
      (fderiv ℝ (fun a => tailoringFamily I β 1 (lgCover a)) z) (z.1, 0)
  intro γ t₀ hγ hx
  let x := γ t₀
  have hxF : tailoringFamily I β 1 (lgCover x) = 1 := hx.2
  obtain ⟨σ, hσ, _, hxσ, hxθ⟩ := hx.1.2
  have hpne : Φ x.1 ≠ 0 := by simpa [hΦeq, lgCover, x] using hx.1.1
  obtain ⟨s, hs, hsne, hsproper, hxs, _, htorus, hcone⟩ :=
    I.exists_face_span_neighborhood hσ (by simpa [hΦeq, lgCover, x] using hxσ) hpne
  have hθs : (lgCover x).2 ∈ coneTorus (positiveCone s) := htorus hxθ
  have hσs : positiveCone s ∈ faceFan I := Or.inr ⟨s, hs, hsne, hsproper, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, Φ x.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply hpne
    funext i
    exact h i
  let ℓ : RealSpace n →L[ℝ] ℝ := (Φ x.1 i)⁻¹ • ContinuousLinearMap.proj i
  have hℓ : ℓ (Φ x.1) = 1 := by simp [ℓ, hi]
  have hβπ : Bπ ≤ β := (le_max_left _ _).trans hβ
  have hβp : Bp ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : BR ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβg : Bg ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hβo : Bo ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  obtain ⟨B, g, f, r, h₀B, hg₀, hfrange, _, _, _, hprops, _⟩ :=
    hbg β hβg s hs hsne hsproper (lgCover x) hxs hθs hxF ℓ hℓ
  change g 0 = x.1 at hg₀
  obtain ⟨θ, hθ⟩ : (lgCover x).2 ∈ range f := by rwa [hfrange]
  let K := conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ
  let j : K → TangentCoordinates n := fun q => (g q, x.2)
  let re : TangentCoordinates n → K := fun z => (r (lgCover z)).1
  have hj₀ : j 0 = x := Prod.ext hg₀ rfl
  have hcover : ContMDiff 𝓘(ℝ, TangentCoordinates n) (lgModel n) ∞
      (fun z : TangentCoordinates n => (z.1, angleQuotient z.2) : TangentCoordinates n → LGSpace n) := by
    have hf : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
        (Prod.fst : TangentCoordinates n → RealSpace n) :=
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
    have hs : ContMDiff 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, RealSpace n) ∞
        (Prod.snd : TangentCoordinates n → RealSpace n) :=
      (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n)).contDiff.contMDiff
    exact hf.prodMk (contMDiff_angleQuotient.comp hs)
  have hr₀ : ContDiffAt ℝ ∞ re (j 0) := by
    have he : (g (0 : K), f θ) = (x.1, angleQuotient x.2) := Prod.ext hg₀ hθ
    have hh := (hprops 0 h₀B θ).2.2.2.2.2.2
    rw [he] at hh
    have hr' : ContMDiffAt (lgModel n) 𝓘(ℝ, K) ∞
        (fun y : LGSpace n => (r y).1) (x.1, angleQuotient x.2) :=
      contMDiffAt_fst.comp (x.1, angleQuotient x.2) hh
    rw [hj₀]
    exact (hr'.comp x (hcover x)).contDiffAt
  have hj : ContDiffAt ℝ ∞ j 0 := by
    have hh := (hprops 0 h₀B θ).1
    have hg := contMDiffAt_fst.comp (0, θ) hh
    have hg' : ContDiffAt ℝ ∞ g 0 :=
      (hg.comp 0 (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    exact hg'.prodMk contDiffAt_const
  have hleft : re ∘ j =ᶠ[𝓝 (0 : K)] id := by
    filter_upwards [B.isOpen.eventually_mem h₀B] with q hq
    have he : lgCover (j q) = (g q, f θ) := Prod.ext rfl hθ.symm
    change (r (lgCover (j q))).1 = q
    rw [he, (hprops q hq θ).2.2.2.2.2.1]
  have hsmooth : ContDiffAt ℝ ∞ V x := hπ β hβπ 1 (by simp) x (by simp [hxF])
  have hV : ContMDiffAt 𝓘(ℝ, TangentCoordinates n)
      (𝓘(ℝ, TangentCoordinates n)).tangent 1
      (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, TangentCoordinates n) (TangentCoordinates n)))
      (j 0) := by
    rw [hj₀]
    rw [contMDiffAt_iff]
    constructor
    · exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, TangentCoordinates n)).symm.continuous.continuousAt.comp
        (continuousAt_id.prodMk hsmooth.continuousAt)
    · simp only [mfld_simps, chartAt_self_eq]
      change ContDiffWithinAt ℝ 1 (fun z : TangentCoordinates n => (z, V z)) Set.univ x
      exact (contDiffAt_id.prodMk (hsmooth.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞))).contDiffWithinAt
  have hnearoff : ∀ᶠ q in 𝓝 (0 : K),
      ∀ v ∈ I.vertices, latticeReal v ∉ positiveCone s → tailoringCutoff I β v (g q) = 0 := by
    have hoff := hbo β hβo (positiveCone s) hσs x.1
      (by simpa [hΦeq] using hxs) (tailoringEndpoint_height_lower I β (lgCover x) hxF)
    have hgcont := (hj.continuousAt.fst)
    have hgcont' : Tendsto g (𝓝 (0 : K)) (𝓝 x.1) := hg₀ ▸ hgcont.tendsto
    exact hgcont'.eventually hoff
  have htangent : ∀ᶠ q in 𝓝 (0 : K), V (j q) ∈
      (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, TangentCoordinates n) j q).range := by
    filter_upwards [B.isOpen.eventually_mem h₀B, hnearoff] with q hq hoff
    have hqp := hprops q hq θ
    have hqF : tailoringFamily I β 1 (lgCover (j q)) = 1 := by
      simpa only [lgCover, j, hθ] using hqp.2.2.1
    have hout : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (g q)‖ := by
      have hh := hrad β hβR 1 (by simp) (lgCover (j q)) hqF
      rw [realEuclideanRadius_eq_norm] at hh
      change R + 1 ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (g q)‖ at hh
      linarith
    have hgerm := potential_germ_eq_on_end heq hout
    have hgrad := coordinateGradient_eq_of_eventuallyEq hgerm
    have hHess := coordinateHessian_eq_of_eventuallyEq hgerm
    have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φEnd := funext hΦeq
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover (j q))
    have hpair := ((hp β hβp 1 (by simp) (lgCover (j q)) hnd).2.2 (by simp [hqF])).ne'
    rw [planePairing_lambdaPotentialForm_eq_cover hφ (j q)
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 (j q).1)) (fun _ => rfl) hnd
        (contMDiff_tailoringFamily_lgManifold I β 1)] at hpair
    have hv := coverProjectedRadial_mem_conormal_radial_tangent I β (positiveCone s) (j q)
      hqF (by simpa [j, lgCover] using hθs) hoff hφ
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 (j q).1)) (fun _ => rfl)
      (coordinateHessian_apply_self_on_homogeneous_end hφ hEnd.smooth hEnd.homogeneous hR heq hout)
      (by simpa only [j, hgrad, ← hΦeq] using hqp.2.2.2.1) hpair
    have hradial : (V (j q)).1 ∈ range (fderiv ℝ g q) := by
      rw [hqp.2.2.2.2.1]
      refine ⟨?_, hv.2.1⟩
      simpa only [hΦfun, ← hHess] using hv.1
    have hgs : DifferentiableAt ℝ g q := by
      have hh := contMDiffAt_fst.comp (q, θ) hqp.1
      exact ((hh.comp q (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt (by simp)
    rw [mfderiv_eq_fderiv]
    exact mem_radialBranch_fderiv_range hgs x.2 (V (j q)) hradial hv.2.2
  have hUcone : ∀ᶠ q in 𝓝 (0 : K), Φ (g q) ∈ Submodule.span ℝ (positiveCone s) →
      Φ (g q) ∈ positiveCone s := by
    have hgcont : Tendsto g (𝓝 (0 : K)) (𝓝 x.1) := hg₀ ▸ hj.continuousAt.fst.tendsto
    exact (Φ.continuous.continuousAt.tendsto.comp hgcont).eventually hcone
  have hUneq : ∀ᶠ q in 𝓝 (0 : K), Φ (g q) ≠ 0 := by
    have hgcont : Tendsto g (𝓝 (0 : K)) (𝓝 x.1) := hg₀ ▸ hj.continuousAt.fst.tendsto
    exact (Φ.continuous.continuousAt.tendsto.comp hgcont).eventually (eventually_ne_nhds hpne)
  let A : Set K := {q | q ∈ B ∧
    (Φ (g q) ∈ Submodule.span ℝ (positiveCone s) → Φ (g q) ∈ positiveCone s) ∧ Φ (g q) ≠ 0}
  have hA : A ∈ 𝓝 (0 : K) :=
    (B.isOpen.eventually_mem h₀B).and (hUcone.and hUneq)
  have hinvariant := integralCurve_eventually_mem_retract_image_of_germ
    (j := j) (r := re) (x := (0 : K))
    (hj.contMDiffAt.of_le (by simp)) (hr₀.contMDiffAt.of_le (by simp))
    hleft hV htangent hγ (by simp only [x, hj₀]) hA
  filter_upwards [hinvariant] with t ht
  obtain ⟨q, hq, hqt⟩ := ht
  have hqp := hprops q hq.1 θ
  have hconeQ := hq.2.1 hqp.2.2.2.1
  have hsnz : positiveCone s ≠ {0} := by
    intro he
    rw [he] at hconeQ
    exact hq.2.2 hconeQ
  rw [← hqt]
  refine ⟨⟨⟨?_, positiveCone s, hσs, hsnz, ?_, ?_⟩, ?_⟩, rfl⟩
  · simpa only [lgCover, j, ← hΦeq] using hq.2.2
  · simpa only [lgCover, j, ← hΦeq] using hconeQ
  · simpa only [lgCover, j] using hθs
  · change tailoringFamily I β 1 (lgCover (j q)) = 1
    simpa only [lgCover, j, hθ] using hqp.2.2.1

end FsFltz
