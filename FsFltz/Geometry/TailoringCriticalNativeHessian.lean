import FsFltz.Geometry.TailoringCriticalTangentHessian
import FsFltz.Analysis.TailoringCriticalToriClassification

/-!
# Uniform native Hessians at the constructed critical face tori

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott` and `eq:hessian`,
lines 1500–1570, and `lem:stable`, lines 1705–1726. The analytic face
equation, weights, multiplier and Hessian blocks are produced from the
actual constrained-minimum branch. The chart Hessian is the second
derivative of the same smooth global potential on the actual full fiber.
No normal trapping or full-core equality is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

/-- A literal face plateau neighborhood supplies the actual endpoint germ,
including the small-monomial cutoff in the specified tailoring function. -/
theorem tailoringFamily_eventually_face_sum_of_plateau {n : ℕ}
    (I : ToricInput n) (β : ℝ) {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    {y : LGSpace n} (hy : tailoringFamily I β 1 y = 1)
    {U : Set (RealSpace n)} (hU : IsOpen U) (hyU : y.1 ∈ U)
    (hcut : ∀ u ∈ U, ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v u = if v = 0 ∨ v ∈ s then 1 else 0) :
    ∀ᶠ w in 𝓝 y, tailoringFamily I β 1 w =
      ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v w := by
  classical
  have hz : tailoringCutoff I β 0 y.1 = 1 := by
    simpa using hcut y.1 hyU 0 (Finset.mem_insert_self _ _)
  have hsum := sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β y hy
  rw [hz, Complex.ofReal_one] at hsum
  have hb := norm_tailoring_weighted_sum_le I β y (tailoringCutoff I β · y.1)
    (fun v _ => ⟨tailoringCutoff_nonneg I β v y.1, tailoringCutoff_le_one I β v y.1⟩)
  change ‖∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y‖ ≤ _ at hb
  rw [hsum, norm_one] at hb
  have hN : 0 < (I.vertices.card : ℝ) := by exact_mod_cast I.vertices_nonempty.card_pos
  have hS : 2 * tailoringSmallConstant I < tailoringMonomialSize I β y := by
    have hc := tailoringSmallConstant_size I
    have hp := mul_pos hN (tailoringSmallConstant_pos I)
    nlinarith
  have hnearU : ∀ᶠ w : LGSpace n in 𝓝 y, w.1 ∈ U :=
    continuous_fst.continuousAt.eventually (hU.mem_nhds hyU)
  have hnearS := (contMDiff_tailoringMonomialSize I β).continuous.continuousAt.eventually
    (eventually_gt_nhds hS)
  filter_upwards [hnearU, hnearS] with w hw hsize
  have hη := (tailoringEta_eq_one_iff I β w).mpr hsize.le
  have hzero : tailoringCutoff I β 0 w.1 = 1 := by
    simpa using hcut w.1 hw 0 (Finset.mem_insert_self _ _)
  rw [tailoringFamily_weighted_sum, hη, hzero]
  simp only [mul_one, one_mul, Complex.ofReal_one, sub_self, mul_zero, zero_add,
    add_sub_cancel]
  calc
    _ = ∑ v ∈ s, (tailoringCutoff I β v w.1 : ℂ) *
        monomial (Real.exp (-β) : ℂ) v w := by
      symm
      apply Finset.sum_subset hsub
      intro v hv hvs
      have hv0 : v ≠ 0 := fun he => I.zero_not_mem_vertices (he ▸ hv)
      rw [hcut w.1 hw v (Finset.mem_insert_of_mem hv)]
      simp [hv0, hvs]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hcut w.1 hw v (Finset.mem_insert_of_mem (hsub hv))]
      simp [hv]

/-- The actual Hessian kernel is linearly isomorphic to the angular face
kernel. This uses the full tangent image and injectivity, not just a bound
on the dimension of an ambient quadratic form. -/
theorem native_hessian_kernel_finrank {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] TangentCoordinates n) (L : E →L[ℝ] E →L[ℝ] ℝ)
    {s : Finset (Lattice n)} {q : s → ℝ}
    (hinj : Injective D)
    (hrange : ∀ V, V ∈ D.range ↔ V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q)
    (hrad : ∀ V, (∀ W, L V W = 0) ↔ (D V).1 = 0 ∧ faceLevelMap s (D V).2 = 0)
    (hA : Surjective (faceLevelMap s)) :
    Module.finrank ℝ L.toLinearMap.ker = n - s.card := by
  have hker (V : E) : V ∈ L.toLinearMap.ker ↔
      (D V).1 = 0 ∧ faceLevelMap s (D V).2 = 0 := by
    rw [LinearMap.mem_ker]
    change L V = 0 ↔ _
    rw [ContinuousLinearMap.ext_iff]
    simpa only [zero_apply] using hrad V
  let A : L.toLinearMap.ker →ₗ[ℝ] (faceLevelMap s).toLinearMap.ker :=
    { toFun := fun V => ⟨(D V.val).2, (hker V.val).mp V.property |>.2⟩
      map_add' := fun V W => Subtype.ext (by simp)
      map_smul' := fun a V => Subtype.ext (by simp) }
  have hbij : Bijective A := by
    constructor
    · intro V W h
      apply Subtype.ext
      apply hinj
      apply Prod.ext
      · exact ((hker V.val).mp V.property).1.trans ((hker W.val).mp W.property).1.symm
      · exact congrArg Subtype.val h
    · intro Y
      have hY : faceLevelMap s Y.val = 0 := Y.property
      have ht : (0, Y.val) ∈ D.range := by
        apply (hrange _).mpr
        constructor
        · simp
        · simp [mem_faceRealTangent, hY]
      obtain ⟨V, hV⟩ := ht
      change D V = (0, Y.val) at hV
      refine ⟨⟨V, (hker V).mpr (by rw [hV]; exact ⟨rfl, hY⟩)⟩, ?_⟩
      apply Subtype.ext
      exact congrArg Prod.snd hV
  exact (LinearEquiv.ofBijective A hbij).finrank_eq.trans (face_kernel_finrank hA)

/-- Actual logarithmic lift, tangent image and second derivative of the
restricted smooth potential at a face-torus point. All Hessian fields refer
to that native restricted function, rather than an assigned model form. -/
structure NativeFaceHessianChart {n d : ℕ} (φ : RealSpace n → ℝ)
    (s : Finset (Lattice n)) (H : RealSpace n →L[ℝ] RealSpace n)
    (q : s → ℝ) (lam : ℝ) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point) (x : TangentCoordinates n) where
  lift : Model d → TangentCoordinates n
  smooth : ContDiffAt ℝ ∞ lift (chartAt (Model d) a a)
  center : lift (chartAt (Model d) a a) = x
  cover : ∀ᶠ y in 𝓝 (chartAt (Model d) a a),
    lgCover (lift y) = j.map ((chartAt (Model d) a).symm y)
  immersion : Injective (fderiv ℝ lift (chartAt (Model d) a a))
  tangent_range : ∀ V, V ∈ (fderiv ℝ lift (chartAt (Model d) a a)).range ↔
    V.1 ∈ faceRealTangent q ∧ V.2 ∈ faceRealTangent q
  stationary : fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1)
    (chartAt (Model d) a a) = 0
  hessian : ∀ V W : Model d,
    fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
      (chartAt (Model d) a a) V W = faceConstrainedPairing s H q lam
        (fderiv ℝ lift (chartAt (Model d) a a) V)
        (fderiv ℝ lift (chartAt (Model d) a a) W)
  radical : ∀ V : Model d,
    (∀ W : Model d,
      fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
        (chartAt (Model d) a a) V W = 0) ↔
      (fderiv ℝ lift (chartAt (Model d) a a) V).1 = 0 ∧
        faceLevelMap s (fderiv ℝ lift (chartAt (Model d) a a) V).2 = 0
  kernel_finrank : Module.finrank ℝ
    (fderiv ℝ (fderiv ℝ (fun y => φ (j.map ((chartAt (Model d) a).symm y)).1))
      (chartAt (Model d) a a)).toLinearMap.ker = n - s.card

/-- Assemble the chart, full bilinear Hessian and native kernel dimension
from the explicit analytic producers. The uniform branch theorem below
discharges all the face-specific hypotheses of this lemma. -/
theorem tailoring_fullFiber_nonempty_nativeFaceHessianChart {n : ℕ}
    (I : ToricInput n) (β : ℝ) {φ ψ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (s : Finset (Lattice n)) (lam : ℝ) (q : s → ℝ)
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (a : N.Point) (x : TangentCoordinates n) (hpoint : j.map a = lgCover x)
    (hlocal : ∀ᶠ y in 𝓝 (j.map a),
      tailoringFamily I β 1 y = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v y)
    (hpot : φ =ᶠ[𝓝 x.1] ψ)
    (hmon : ∀ v : s, monomial (Real.exp (-β) : ℂ) v.val (lgCover x) = (q v : ℂ))
    (hcritical : coordinateGradient ψ x.1 = lam • faceNormalMap s q)
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : (fderiv ℝ (coordinateGradient ψ) x.1).comp B = (faceNormalMap s).comp R)
    (hHsym : ∀ X Y, (∑ j, fderiv ℝ (coordinateGradient ψ) x.1 X j * Y j) =
      ∑ j, fderiv ℝ (coordinateGradient ψ) x.1 Y j * X j)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ j, fderiv ℝ (coordinateGradient ψ) x.1 e j * e j)
    (hq : ∀ v, 0 < q v) (hlam : 0 < lam)
    (hnegative : ∀ h : s → ℝ, h ≠ 0 →
      (∑ v, R h v * h v) - lam * faceWeightSquare q h < 0) :
    Nonempty (NativeFaceHessianChart φ s (fderiv ℝ (coordinateGradient ψ) x.1)
      q lam N j a x) := by
  obtain ⟨g, hg, hga, heq, hinj, _, hfirst, hh⟩ :=
    tailoring_fullFiber_exists_native_hessian_chart I β hφ s lam q N j himage a x
      hpoint hlocal hpot hmon hcritical
  have hkernel := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage a
  have hrange := logarithmic_chart_lift_range_face_tangent I β s q N j a x hpoint
    hkernel hlocal hmon hg hga heq
  have he : (fun y => φ (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1) =ᶠ[
      𝓝 (chartAt (Model (2 * n - 2)) a a)] (fun y => φ (g y).1) := by
    filter_upwards [heq] with y hy
    exact (congrArg (fun z : LGSpace n => φ z.1) hy).symm
  have hsmooth : ContDiffAt ℝ ∞
      (fun y => φ (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1)
      (chartAt (Model (2 * n - 2)) a a) :=
    (hφ.contDiffAt.comp _ hg.fst).congr_of_eventuallyEq he
  have hrad := second_fderiv_face_radical_iff hsmooth
    (fderiv ℝ g (chartAt (Model (2 * n - 2)) a a)) hB hnormal hHsym hH hq hlam
    hnegative hrange hh
  have hA : Surjective (faceLevelMap s) := by
    intro y
    refine ⟨B y, ?_⟩
    exact congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L y) hB
  exact ⟨⟨g, hg, hga, heq, hinj, hrange, hfirst,
    second_fderiv_eq_faceConstrainedPairing hsmooth _ s _ q lam hHsym hh,
    hrad, native_hessian_kernel_finrank _ _ hinj hrange hrad hA⟩⟩

/-- The actual reduced branch has native Hessian charts at every point of
its entire literal face torus, with one threshold independent of angle,
full-fiber presentation and logarithmic lift. All face-specific analytic
conditions are discharged by the constructed branch and inertia theorem. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_face_native_hessian {n : ℕ}
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
        ∀ θ ∈ coneTorus (positiveCone s),
          tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
          tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
          ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
            range j.map = {y | tailoringFamily I β 1 y = 1} →
            ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
              lgCover ξ = (faceCriticalRadius x z β, θ) →
              Nonempty (NativeFaceHessianChart φ s
                (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
                (z β⁻¹).1 (β * (z β⁻¹).2) N j a ξ) := by
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
  have hall : ∀ᶠ β : ℝ in atTop,
      (∀ v, 0 < (z β⁻¹).1 v) ∧ 0 < β * (z β⁻¹).2 ∧
      ∀ θ ∈ coneTorus (positiveCone s),
        tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
        tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
            lgCover ξ = (faceCriticalRadius x z β, θ) →
            Nonempty (NativeFaceHessianChart φ s
              (fderiv ℝ (coordinateGradient φEnd) (faceCriticalRadius x z β))
              (z β⁻¹).1 (β * (z β⁻¹).2) N j a ξ) := by
    filter_upwards [hnative, hblocks, hpot, hcut, hparam.eventually hlevel',
      tendsto_inv_atTop_zero.eventually hzsol, hradial,
      eventually_gt_atTop (0 : ℝ), eventually_ge_atTop Bπ]
      with β hn hb hp hcutβ hl hz hr hβ hβπ
    refine ⟨hz.1, mul_pos hβ hz.2.1, ?_⟩
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
    simpa only [hξrad] using hchart
  obtain ⟨B, hB⟩ := eventually_atTop.mp hall
  exact ⟨x, z, hx₀, hm₀, hxs, hzs, max B 1,
    zero_lt_one.trans_le (le_max_right _ _), fun β hβ => hB β ((le_max_left _ _).trans hβ)⟩

/-- The stationary chart field is actual intrinsic criticality. -/
theorem NativeFaceHessianChart.critical {n d : ℕ} {φ : RealSpace n → ℝ}
    {s : Finset (Lattice n)} {H : RealSpace n →L[ℝ] RealSpace n}
    {q : s → ℝ} {lam : ℝ} {N : SmoothManifold d}
    {j : N.SmoothEmbedding (lgManifold n)} {a : N.Point} {x : TangentCoordinates n}
    (C : NativeFaceHessianChart φ s H q lam N j a x) (hφ : ContDiff ℝ ∞ φ) :
    ∀ V : N.Tangent a, N.scalarDerivative (fun p => φ (j.map p).1) a V = 0 := by
  intro V
  have hs : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (fun p => φ (j.map p).1) :=
    (contMDiff_potentialValue hφ).comp j.map.contMDiff
  rw [← N.fderiv_scalar_in_chart _ hs a a (mem_chart_source _ _) V]
  exact congrArg (fun L : Model d →L[ℝ] ℝ => L (N.chartTangentMap a a V)) C.stationary

/-- One finite threshold supplies actual smooth full fibers and native
Hessian charts simultaneously on all the constructed face tori. -/
theorem IsStronglyCompatibleEndPotential.exists_uniform_fullFiber_native_hessian {n : ℕ}
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
      R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    let F := {s : Finset (Lattice n) //
      IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
    ∃ u : F → ℝ → RealSpace n,
      ∃ q : (s : F) → ℝ → s.val → ℝ, ∃ lam : F → ℝ → ℝ,
        ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
          (∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
            range j.map = {y | tailoringFamily I β 1 y = 1} ∧
            N.IsSymplecticOn
              (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ) ∧
          ∀ s, (∀ v, 0 < q s β v) ∧ 0 < lam s β ∧
            ∀ θ ∈ coneTorus (positiveCone s.val),
              tailoringFamily I β 1 (u s β, θ) = 1 ∧
              tailoringRetainedVertices I β (u s β) = s.val ∧
              ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
                range j.map = {y | tailoringFamily I β 1 y = 1} →
                ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
                  lgCover ξ = (u s β, θ) →
                  Nonempty (NativeFaceHessianChart φ s.val
                    (fderiv ℝ (coordinateGradient φEnd) (u s β)) (q s β) (lam s β) N j a ξ) := by
  classical
  dsimp only
  let F := {s : Finset (Lattice n) //
    IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
  let embed : F → {s // s ∈ I.vertices.powerset} := fun s =>
    ⟨s.val, Finset.mem_powerset.mpr s.property.1.1⟩
  have hinj : Injective embed := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun t : {s // s ∈ I.vertices.powerset} => t.val) h
  let : Finite F := Finite.of_injective embed hinj
  let : Fintype F := Fintype.ofFinite F
  have hface (s : F) := hStrong.exists_actual_face_native_hessian hEnd1 hd hEndConv
    hφ hc hU hlower hupper hEnd s.property.1 s.property.2.1 s.property.2.2
  choose x z _ _ _ _ B _ hall using hface
  let u : F → ℝ → RealSpace n := fun s β => faceCriticalRadius (x s) (z s) β
  let q : (s : F) → ℝ → s.val → ℝ := fun s β => (z s β⁻¹).1
  let lam : F → ℝ → ℝ := fun s β => β * (z s β⁻¹).2
  have hfaces : ∀ᶠ β : ℝ in atTop, ∀ s : F,
      (∀ v, 0 < q s β v) ∧ 0 < lam s β ∧
      ∀ θ ∈ coneTorus (positiveCone s.val),
        tailoringFamily I β 1 (u s β, θ) = 1 ∧
        tailoringRetainedVertices I β (u s β) = s.val ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
            lgCover ξ = (u s β, θ) →
            Nonempty (NativeFaceHessianChart φ s.val
              (fderiv ℝ (coordinateGradient φEnd) (u s β)) (q s β) (lam s β) N j a ξ) :=
    eventually_all.mpr fun s => eventually_atTop.mpr ⟨B s, hall s⟩
  obtain ⟨Bf, hf⟩ := eventually_atTop.mp hfaces
  obtain ⟨Be, _, he⟩ := tailoringFamily_exists_uniform_symplectic_levelEmbedding
    I hφ hc hU hlower hupper
  refine ⟨u, q, lam, max 1 (max Bf Be), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  refine ⟨he β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) 1 (by simp) 1
    (by simp), hf β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ))⟩

/-- Every native critical or Liouville-zero point has the computed native
Hessian, on the same face used by exhaustive critical classification.
The reconstructed and classified radial points are identified through their
actual criticality and literal retained supports in the same full fiber. -/
theorem IsStronglyCompatibleEndPotential.exists_uniform_critical_native_hessian {n : ℕ}
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hEndLower : ∀ u, a₀ * ‖u‖ ^ 2 ≤ φEnd u)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    let F := {s : Finset (Lattice n) //
      IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
    ∃ q : (s : F) → ℝ → s.val → ℝ, ∃ lam : F → ℝ → ℝ,
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ a : N.Point,
          ((∀ V : N.Tangent a, N.scalarDerivative (fun p => φ (j.map p).1) a V = 0) ∨
            N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
          ∃ s : F, tailoringRetainedVertices I β (j.map a).1 = s.val ∧
            (∀ v, 0 < q s β v) ∧ 0 < lam s β ∧
            ∀ ξ : TangentCoordinates n, j.map a = lgCover ξ →
              Nonempty (NativeFaceHessianChart φ s.val
                (fderiv ℝ (coordinateGradient φEnd) (j.map a).1)
                (q s β) (lam s β) N j a ξ) := by
  classical
  dsimp only
  obtain ⟨u, q, lam, Bn, hBn, hn⟩ :=
    hStrong.exists_uniform_fullFiber_native_hessian hEnd1 hd hEndConv
      hφ hc hU hlower hupper hEnd
  obtain ⟨u₀, Bc, _, hclass⟩ := hStrong.exists_fullFiber_critical_face_tori
    hEnd1 hd hEndConv ha₀ hEndLower hφ hc hU hlower hupper hEnd
  refine ⟨q, lam, max Bn Bc, hBn.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a ha
  have hnβ := (hn β ((le_max_left _ _).trans hβ)).2
  have hcβ := hclass β ((le_max_right _ _).trans hβ)
  obtain ⟨s, hs⟩ := ((hcβ.2.2 N j himage a).2.1).mp ha
  have hns := hnβ s
  have hθ := hns.2.2 (j.map a).2 hs.2
  have hbmem : (u s β, (j.map a).2) ∈ range j.map := by
    rw [himage]
    exact hθ.1
  obtain ⟨b, hbpoint⟩ := hbmem
  obtain ⟨ζ, hζ⟩ := lgCover_surjective n (u s β, (j.map a).2)
  obtain ⟨C⟩ := hθ.2.2 N j himage b ζ (hbpoint.trans hζ.symm) hζ
  obtain ⟨t, ht⟩ := (hcβ.2.2 N j himage b).1.mp (C.critical hφ)
  have hsupps : tailoringRetainedVertices I β (j.map b).1 = s.val := by
    rw [hbpoint]
    exact hθ.2.1
  have hsuppt : tailoringRetainedVertices I β (j.map b).1 = t.val := by
    rw [ht.1]
    exact (hcβ.1 t (j.map b).2 ht.2).2
  have hts : t = s := Subtype.ext (hsuppt.symm.trans hsupps)
  subst t
  have hrad : u s β = (j.map a).1 :=
    (congrArg Prod.fst hbpoint).symm.trans (ht.1.trans hs.1.symm)
  refine ⟨s, ?_, hns.1, hns.2.1, ?_⟩
  · rw [hs.1]
    exact (hcβ.1 s (j.map a).2 hs.2).2
  · intro ξ hpoint
    have hξ : lgCover ξ = (u s β, (j.map a).2) :=
      hpoint.symm.trans (Prod.ext hrad.symm rfl)
    have hchart := hθ.2.2 N j himage a ξ hpoint hξ
    simpa only [hrad] using hchart

end FsFltz
