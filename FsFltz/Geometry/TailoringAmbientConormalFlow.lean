import FsFltz.Geometry.TailoringAmbientConormalDifferential
import FsFltz.Geometry.RetractFlowInvariance
import FsFltz.Geometry.LocalCovers
import FsFltz.Analysis.ToricConeNeighborhood
import FsFltz.Analysis.TailoringCriticalToriInertiaGlobal
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Geometry.VectorFieldBridge

/-!
# Actual ambient cone preservation

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1620–1659,
and `prop:band`, lines 1778–1818. The local restricted ODE is constructed
from a full-span Legendre retraction and identified by uniqueness with
the native primitive-determined ambient field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

/-- The small-size region is strictly separated from every actual endpoint
value of norm at least one, including the inner boundary. -/
theorem tailoringMonomialSize_gt_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hy : 1 ≤ ‖tailoringFamily I β 1 y‖) :
    2 * tailoringSmallConstant I < tailoringMonomialSize I β y := by
  by_contra h
  have hS : tailoringMonomialSize I β y ≤ 2 * tailoringSmallConstant I := le_of_not_gt h
  have hzero : tailoringCutoff I β 0 y.1 = 1 := by
    apply tailoringCutoff_eq_one_of_maximal
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    rw [tailoringWeight_zero]
    have hm : ‖monomial (Real.exp (-β) : ℂ) a y‖ < 1 :=
      (norm_monomial_le_tailoringMonomialSize I β ha y).trans_lt
        (hS.trans_lt (two_mul_tailoringSmallConstant_lt_one I))
    rw [norm_tailoring_monomial I β ⟨a, ha⟩ y] at hm
    exact (Real.exp_lt_one_iff.mp hm).le
  have hb := norm_tailoring_weighted_sum_le I β y
    (fun v => 1 + tailoringEta I β y * (tailoringCutoff I β v y.1 - 1))
    (fun v _ => by simpa only [one_mul] using
      tailoringFamily_weight_mem_Icc I β (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) y v)
  rw [tailoringFamily_weighted_sum, hzero] at hy
  simp only [Complex.ofReal_one, sub_self, mul_zero, zero_add, one_mul] at hy
  have hN : (0 : ℝ) ≤ I.vertices.card := Nat.cast_nonneg _
  have hc := tailoringSmallConstant_pos I
  have hs := mul_le_mul_of_nonneg_left hS hN
  have hsmall := tailoringSmallConstant_size I
  nlinarith

/-- At norm one as well, the auxiliary cutoff is literally constant on
an ambient neighborhood, rather than merely flat at the chosen point. -/
theorem tailoringEta_eventually_eq_one_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖) :
    ∀ᶠ z in 𝓝 x, tailoringEta I β (lgCover z) = 1 := by
  have hsize : Continuous (fun z : TangentCoordinates n => tailoringMonomialSize I β (lgCover z)) :=
    (contMDiff_tailoringMonomialSize I β).continuous.comp (contMDiff_lgCover n).continuous
  filter_upwards [hsize.continuousAt (lt_mem_nhds
    (tailoringMonomialSize_gt_of_norm_ge_one I β (lgCover x) hx))] with z hz
  exact (tailoringEta_eq_one_iff I β (lgCover z)).mpr hz.le

/-- The source's height lower bound also holds throughout the actual
norm-one and larger region, not only on its inner fiber. -/
theorem tailoringEndpoint_height_lower_of_norm_ge_one
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hy : 1 ≤ ‖tailoringFamily I β 1 y‖) :
    β - Real.log (I.vertices.card : ℝ) ≤ supportHeight I y.1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hN1 : (1 : ℝ) ≤ I.vertices.card := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hη := tailoringEta_eq_one_of_one_le_norm_endpoint I β y hy
  have hb : 1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) := by
    by_cases hM : 1 ≤ Real.exp (supportHeight I y.1 - β)
    · exact (one_div_le_one_div_of_le zero_lt_one hN1).trans (by simpa using hM)
    have hweight : supportHeight I y.1 - β ≤ 0 :=
      Real.exp_le_one_iff.mp (le_of_not_ge hM)
    have hχ : tailoringCutoff I β 0 y.1 = 1 := by
      apply tailoringCutoff_eq_one_of_maximal
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_rfl
      rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_zero]
      exact (sub_le_sub_right (I.pairing_le_supportHeight y.1 ⟨a, ha⟩) β).trans hweight
    rw [tailoringFamily_weighted_sum, hη, hχ] at hy
    simp only [mul_one, one_mul, Complex.ofReal_one, sub_self, mul_zero,
      zero_add, add_sub_cancel] at hy
    have hbound : (1 : ℝ) ≤ I.vertices.card * Real.exp (supportHeight I y.1 - β) := by
      calc
        1 ≤ ‖∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y‖ := hy
        _ ≤ ∑ v ∈ I.vertices, ‖tailoringRetainedMonomial I β v y‖ := norm_sum_le _ _
        _ ≤ ∑ _v ∈ I.vertices, Real.exp (supportHeight I y.1 - β) :=
          Finset.sum_le_sum fun v hv => norm_tailoringRetainedMonomial_le_max I β v hv y
        _ = _ := by simp
    exact (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hbound)
  have hlog := (Real.log_le_iff_le_exp (one_div_pos.mpr hN)).mpr hb
  rw [Real.log_div (by norm_num) hN.ne', Real.log_one, zero_sub] at hlog
  linarith

/-- An actual smooth inverse Legendre map supplies the full radial tangent
range of a fixed-angle face-span branch. -/
theorem mem_fderiv_inverse_span_branch
    (Φ : RealSpace n ≃ₜ RealSpace n) (L : Submodule ℝ (RealSpace n))
    (q : L) (θ : RealSpace n)
    (hΦ : DifferentiableAt ℝ Φ (Φ.symm (q : RealSpace n)))
    (hinv : DifferentiableAt ℝ Φ.symm (q : RealSpace n))
    (v : TangentCoordinates n) (hangle : v.2 = 0)
    (hspan : fderiv ℝ Φ (Φ.symm (q : RealSpace n)) v.1 ∈ L) :
    v ∈ range (fderiv ℝ (fun a : L => (Φ.symm (a : RealSpace n), θ)) q) := by
  let w : L := ⟨fderiv ℝ Φ (Φ.symm (q : RealSpace n)) v.1, hspan⟩
  have hinv' : HasFDerivAt Φ.symm (fderiv ℝ Φ.symm (q : RealSpace n))
      (Φ (Φ.symm (q : RealSpace n))) := by simpa using hinv.hasFDerivAt
  have hcomp : (Φ.symm : RealSpace n → RealSpace n) ∘ Φ = id :=
    funext Φ.symm_apply_apply
  have hd := hinv'.comp (Φ.symm (q : RealSpace n)) hΦ.hasFDerivAt
  rw [hcomp] at hd
  have he := congrArg (fun T : RealSpace n →L[ℝ] RealSpace n => T v.1)
    (hd.unique (hasFDerivAt_id (Φ.symm (q : RealSpace n))))
  refine ⟨w, ?_⟩
  change (fderiv ℝ (fun a => ((Φ.symm ∘ L.subtypeL) a, θ)) q) w = v
  erw [((hinv.hasFDerivAt.comp q L.subtypeL.hasFDerivAt).prodMk
    (hasFDerivAt_const θ q)).fderiv]
  exact Prod.ext he (by simpa using hangle.symm)

/-- Native ambient integral curves locally preserve the actual conic set,
including every cone face and the norm-one inner boundary. Hessian, Euler,
cutoff, and denominator conditions are discharged by the stated potentials. -/
theorem tailoringEndpoint_exists_uniform_ambient_conePiece_local_invariance
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (γ : ℝ → (lgManifold n).Point) (t₀ : ℝ),
        IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t₀ →
        ∀ σ ∈ faceFan I,
        coordinateGradient φEnd (γ t₀).1 ≠ 0 →
        coordinateGradient φEnd (γ t₀).1 ∈ σ → (γ t₀).2 ∈ coneTorus σ →
        1 ≤ ‖tailoringFamily I β 1 (γ t₀)‖ →
        ∀ᶠ t in 𝓝 t₀, γ t ∈ tailoringLegendreConic I φEnd ∧ (γ t).2 = (γ t₀).2 ∧ coordinateGradient φEnd (γ t).1 ∈ σ := by
  classical
  obtain ⟨_, _, _, _, Bp, hBp, hpair⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨BR, hBR, hsmall⟩ := tailoringFamily_exists_compact_norm_lt_one I (R + 1)
  obtain ⟨Bo, hoff⟩ := eventually_atTop.mp
    (hEnd.eventually_offCone_cutoff_germ (Real.log (I.vertices.card : ℝ)))
  refine ⟨max Bp (max BR Bo), hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ K hK γ t₀ hγ σ hσ hpneNative hpσNative hθNative hnorm
  have hβp : Bp ≤ β := (le_max_left _ _).trans hβ
  have hβR : BR ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβo : Bo ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨x, hx⟩ := lgCover_surjective n (γ t₀)
  have hxnorm : 1 ≤ ‖tailoringFamily I β 1 (lgCover x)‖ := hx.symm ▸ hnorm
  have hpne : coordinateGradient φEnd (lgCover x).1 ≠ 0 := hx.symm ▸ hpneNative
  have hpσ : coordinateGradient φEnd (lgCover x).1 ∈ σ := hx.symm ▸ hpσNative
  have hθσ : (lgCover x).2 ∈ coneTorus σ := hx.symm ▸ hθNative
  have hpne' : Φ x.1 ≠ 0 := by simpa only [hΦeq, lgCover] using hpne
  obtain ⟨s, hs, hsne, hsproper, hps, hsub, htorus, hcone⟩ :=
    I.exists_face_span_neighborhood hσ (by simpa only [hΦeq, lgCover] using hpσ) hpne'
  have hface : positiveCone s ∈ faceFan I := Or.inr ⟨s, hs, hsne, hsproper, rfl⟩
  have hθs : (lgCover x).2 ∈ coneTorus (positiveCone s) := htorus hθσ
  have hxrad : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    have hh : R + 1 < Real.sqrt (realSquaredNorm x.1) := by
      by_contra hn
      exact (not_lt_of_ge hxnorm) (hsmall β hβR 1 (lgCover x) (le_of_not_gt hn))
    rw [realEuclideanRadius_eq_norm] at hh
    linarith
  have hxne : x.1 ≠ 0 := by
    intro h
    simp only [h, map_zero, norm_zero] at hxrad
    linarith
  let L := Submodule.span ℝ (positiveCone s)
  let q₀ : L := ⟨Φ x.1, Submodule.subset_span hps⟩
  obtain ⟨P₀, hP₀⟩ := L.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr L.subtype_injective)
  let P : RealSpace n →L[ℝ] L := P₀.toContinuousLinearMap
  have hP (q : L) : P (q : RealSpace n) = q :=
    congrArg (fun T : L →ₗ[ℝ] L => T q) hP₀
  let g : L → TangentCoordinates n := fun q => (Φ.symm (q : RealSpace n), x.2)
  let j : L → (lgManifold n).Point := lgCover ∘ g
  let r : (lgManifold n).Point → L := fun y => P (Φ y.1)
  have hg₀ : g q₀ = x := Prod.ext (Φ.symm_apply_apply x.1) rfl
  have hj₀ : j q₀ = γ t₀ := by
    dsimp only [j, Function.comp_apply]
    rw [hg₀, hx]
  have hqne : (q₀ : RealSpace n) ≠ 0 := hpne'
  have hΦx : ContDiffAt ℝ ∞ Φ x.1 :=
    hΦ.contDiffAt (isOpen_compl_singleton.mem_nhds hxne)
  have hinvx : ContDiffAt ℝ ∞ Φ.symm (q₀ : RealSpace n) :=
    hΦinv.contDiffAt (isOpen_compl_singleton.mem_nhds hqne)
  have hg : ContDiffAt ℝ ∞ g q₀ :=
    (hinvx.comp q₀ L.subtypeL.contDiff.contDiffAt).prodMk contDiffAt_const
  have hj : ContMDiffAt 𝓘(ℝ, L) 𝓘(ℝ, Model (2 * n)) ∞ j q₀ :=
    (contMDiff_lgCover n _).comp q₀ hg.contMDiffAt
  have hr : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, L) ∞ r (j q₀) := by
    have hh : ContDiffAt ℝ ∞ (r ∘ lgCover) x :=
      P.contDiff.contDiffAt.comp x (hΦx.comp x contDiffAt_fst)
    have hnative := (contMDiffAt_iff_comp_of_isLocalDiffeomorphAt
      (isLocalDiffeomorph_lgCover n x) r).mpr hh.contMDiffAt
    simpa only [j, Function.comp_apply, hg₀] using hnative
  have hleft : r ∘ j =ᶠ[𝓝 q₀] id := Eventually.of_forall fun q => by
    change P (Φ (Φ.symm (q : RealSpace n))) = q
    rw [Φ.apply_symm_apply, hP]
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K
  let Z := (lgManifold n).liouvilleVector α
  have hnd₀ := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower
  have hden (y : (lgManifold n).Point)
      (hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) :
      1 + K * (lgManifold n).planePairing (lambdaPotentialForm φ)
        (tailoringFamily I β 1) y hnd ≠ 0 := by
    have hh := (hpair β hβp 1 (by simp) y hnd).1
    positivity
  have hZ := (lgManifold n).isSmoothVectorField_liouvilleVector α
    ((lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
      (contMDiff_tailoringFamily_lgManifold I β 1) K) (fun y =>
      ((lgManifold n).nondegenerate_exteriorDerivative_rankTwoPrimitive_iff
        (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1)
          K y (hnd₀ y)).mpr (hden y (hnd₀ y)))
  have hgt : Tendsto g (𝓝 q₀) (𝓝 x) := by
    simpa only [hg₀] using hg.continuousAt.tendsto
  have hnearη : ∀ᶠ q in 𝓝 q₀, tailoringEta I β (lgCover (g q)) = 1 :=
    hgt.eventually
      (tailoringEta_eventually_eq_one_of_norm_ge_one I β x hxnorm)
  have hnearoff : ∀ᶠ q in 𝓝 q₀,
      ∀ v ∈ I.vertices, latticeReal v ∉ positiveCone s →
        tailoringCutoff I β v (g q).1 = 0 := by
    have h := hoff β hβo (positiveCone s) hface x.1
      (by simpa only [hΦeq] using hps)
      (tailoringEndpoint_height_lower_of_norm_ge_one I β (lgCover x) hxnorm)
    have hgcont : Tendsto (fun q => (g q).1) (𝓝 q₀) (𝓝 x.1) := by
      simpa only [hg₀] using hg.continuousAt.fst.tendsto
    exact hgcont.eventually h
  have hnearrad : ∀ᶠ q in 𝓝 q₀,
      R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (g q).1‖ := by
    have hc : Continuous (fun z : TangentCoordinates n =>
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖) :=
      ((EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp continuous_fst).norm
    have hh := hg.continuousAt.tendsto.eventually
      (hc.continuousAt (lt_mem_nhds (show R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (g q₀).1‖ by
        simpa only [hg₀] using hxrad)))
    exact hh
  have hnearΦ : ∀ᶠ q in 𝓝 q₀,
      ContDiffAt ℝ ∞ Φ (g q).1 ∧ ContDiffAt ℝ ∞ Φ.symm (q : RealSpace n) := by
    have hq := L.subtypeL.continuous.tendsto q₀ |>.eventually (eventually_ne_nhds hqne)
    filter_upwards [hq] with q hq
    have hgu : (g q).1 ≠ 0 := by
      intro h
      have he : (q : RealSpace n) = 0 := by
        calc
          _ = Φ (g q).1 := (Φ.apply_symm_apply _).symm
          _ = 0 := by rw [h, hΦ₀]
      exact hq he
    exact ⟨hΦ.contDiffAt (isOpen_compl_singleton.mem_nhds hgu),
      hΦinv.contDiffAt (isOpen_compl_singleton.mem_nhds hq)⟩
  have htangent : ∀ᶠ q in 𝓝 q₀, Z (j q) ∈
      (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, Model (2 * n)) j q).range := by
    filter_upwards [hnearη, hnearoff, hnearrad, hnearΦ] with q hη ho hradius hsm
    let z := g q
    let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)
    let π := coverPlanePairing H
      (fderiv ℝ (fun a => tailoringFamily I β 1 (lgCover a)) z)
    have hgerm := potential_germ_eq_on_end heq hradius
    have hgrad := coordinateGradient_eq_of_eventuallyEq hgerm
    have hHess := coordinateHessian_eq_of_eventuallyEq hgerm
    have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φEnd := funext hΦeq
    have hpL : coordinateGradient φ z.1 ∈ L := by
      rw [hgrad, ← hΦeq]
      change Φ (Φ.symm (q : RealSpace n)) ∈ L
      simpa only [Φ.apply_symm_apply] using q.property
    have hd : 1 + K * π ≠ 0 := by
      have hh := hden (lgCover z) (hnd₀ (lgCover z))
      rw [planePairing_lambdaPotentialForm_eq_cover hφ z H (fun _ => rfl)
        (hnd₀ (lgCover z)) (contMDiff_tailoringFamily_lgManifold I β 1)] at hh
      exact hh
    have hEuler := coordinateHessian_apply_self_on_homogeneous_end
      hφ hEnd.smooth hEnd.homogeneous hR heq hradius
    let κ := K / (1 + K * π) *
      ((tailoringFamily I β 1 (lgCover z)).re / 2 -
        fderiv ℝ (tailoringRadialFunction I β) z.1 z.1)
    let v : TangentCoordinates n := (z.1 + κ •
      ((EuclideanSpace.equiv (Fin n) ℝ)
        (H.symm (WithLp.toLp 2 (tailoringConormalVector I β z.1)))), 0)
    have hZv : Z (j q) = lgCoverTangent z v :=
      native_liouvilleVector_rankTwo_tailoring_conormal_of_eta_eq_one
        I β (positiveCone s) z hη (by simpa only [j, g, lgCover] using hθs) ho
        hφ H (fun _ => rfl) hEuler K hd
    have hvspan : fderiv ℝ Φ z.1 v.1 ∈ L := by
      rw [hΦfun, ← hHess]
      change fderiv ℝ (coordinateGradient φ) z.1 (z.1 + κ • _) ∈ L
      rw [map_add, map_smul, hEuler, coordinateHessian_eq_euclideanHessian hφ]
      change coordinateGradient φ z.1 + κ • (EuclideanSpace.equiv (Fin n) ℝ)
        (H (H.symm (WithLp.toLp 2 (tailoringConormalVector I β z.1)))) ∈ L
      rw [H.apply_symm_apply]
      exact L.add_mem hpL (L.smul_mem _ (tailoringConormalVector_mem_span I β (positiveCone s) z.1 ho))
    have hvrange := mem_fderiv_inverse_span_branch Φ L q x.2
      (hsm.1.differentiableAt (by simp)) (hsm.2.differentiableAt (by simp)) v rfl hvspan
    obtain ⟨w, hw⟩ := hvrange
    refine ⟨w, ?_⟩
    have hgq : ContDiffAt ℝ ∞ g q :=
      (hsm.2.comp q L.subtypeL.contDiff.contDiffAt).prodMk contDiffAt_const
    have hdj := mfderiv_comp q
      ((contMDiff_lgCover n).mdifferentiableAt (by simp))
      (hgq.contMDiffAt.mdifferentiableAt (by simp))
    change (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, Model (2 * n)) (lgCover ∘ g) q) w = Z (j q)
    erw [hdj, mfderiv_eq_fderiv]
    change lgCoverTangent (g q) (fderiv ℝ g q w) = Z (j q)
    rw [hw, hZv]
  let A : Set L := {q | (q : RealSpace n) ≠ 0 ∧
    ((q : RealSpace n) ∈ L → (q : RealSpace n) ∈ positiveCone s)}
  have hA : A ∈ 𝓝 q₀ := by
    exact (L.subtypeL.continuous.tendsto q₀).eventually ((eventually_ne_nhds hpne').and hcone)
  have hinv := integralCurve_eventually_mem_retract_image_of_germ
    (hj.of_le (by norm_num)) (hr.of_le (by norm_num)) hleft
    ((hZ.contMDiff_section.of_le (by norm_num)) (j q₀)) htangent hγ hj₀.symm hA
  filter_upwards [hinv] with t ht
  obtain ⟨q, hq, hqt⟩ := ht
  rw [← hqt]
  refine ⟨⟨?_, positiveCone s, hface, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change coordinateGradient φEnd (Φ.symm (q : RealSpace n)) ≠ 0
    rw [← hΦeq, Φ.apply_symm_apply]
    exact hq.1
  · intro he
    have hqs := hq.2 q.property
    rw [he] at hqs
    exact hq.1 hqs
  · change coordinateGradient φEnd (Φ.symm (q : RealSpace n)) ∈ positiveCone s
    rw [← hΦeq, Φ.apply_symm_apply]
    exact hq.2 q.property
  · simpa only [j, Function.comp_apply, g, lgCover] using hθs
  · change angleQuotient x.2 = (γ t₀).2
    exact congrArg Prod.snd hx
  · change coordinateGradient φEnd (Φ.symm (q : RealSpace n)) ∈ σ
    rw [← hΦeq, Φ.apply_symm_apply]
    exact hsub (hq.2 q.property)

/-- Local two-sided retention of the union of actual face pieces. -/
theorem tailoringEndpoint_exists_uniform_ambient_conormal_local_invariance
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (γ : ℝ → (lgManifold n).Point) (t₀ : ℝ),
        IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t₀ →
        γ t₀ ∈ tailoringLegendreConic I φEnd →
        1 ≤ ‖tailoringFamily I β 1 (γ t₀)‖ →
        ∀ᶠ t in 𝓝 t₀, γ t ∈ tailoringLegendreConic I φEnd ∧ (γ t).2 = (γ t₀).2 := by
  obtain ⟨B, hB, hpiece⟩ := tailoringEndpoint_exists_uniform_ambient_conePiece_local_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  refine ⟨B, hB, ?_⟩
  intro β hβ K hK γ t₀ hγ hstart hnorm
  obtain ⟨hpne, σ, hσ, _, hpσ, hθσ⟩ := hstart
  exact (hpiece β hβ K hK γ t₀ hγ σ hσ hpne hpσ hθσ hnorm).mono
    (fun _ h => ⟨h.1, h.2.1⟩)

/-- Every specified cone piece is preserved on any connected time band
where the actual endpoint norm stays at least one. No cone retention or
Hessian/Euler identity is assumed. -/
theorem tailoringEndpoint_exists_uniform_ambient_conePiece_invariance_on
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (S : Set ℝ), IsPreconnected S → ∀ γ : ℝ → (lgManifold n).Point,
        (∀ t ∈ S, IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        (∀ t ∈ S, 1 ≤ ‖tailoringFamily I β 1 (γ t)‖) →
        ∀ t₀ ∈ S, ∀ σ ∈ faceFan I,
          coordinateGradient φEnd (γ t₀).1 ∈ σ → (γ t₀).2 ∈ coneTorus σ →
          ∀ t ∈ S, γ t ∈ tailoringLegendreConic I φEnd ∧
            coordinateGradient φEnd (γ t).1 ∈ σ ∧ (γ t).2 = (γ t₀).2 := by
  obtain ⟨Bl, hBl, hlocal⟩ := tailoringEndpoint_exists_uniform_ambient_conePiece_local_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨B₀, _, hsmall⟩ := tailoringFamily_exists_compact_norm_lt_one I 0
  refine ⟨max Bl B₀, hBl.trans_le (le_max_left _ _), ?_⟩
  intro β hβ K hK S hS γ hγ hnorm t₀ ht₀ σ hσ hp₀ hθ₀
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hγc : Continuous (fun t : S => γ t.val) :=
    (show ContinuousOn γ S from fun t ht => (hγ t ht).continuousAt.continuousWithinAt).domRestrict
  have hne (t : ℝ) (ht : t ∈ S) : coordinateGradient φEnd (γ t).1 ≠ 0 := by
    rw [← hΦeq, ← hΦ₀]
    intro hz
    have hu : (γ t).1 = 0 := Φ.injective hz
    have hh := hsmall β ((le_max_right _ _).trans hβ) 1 (γ t) (by simp [hu, realSquaredNorm])
    exact not_lt_of_ge (hnorm t ht) hh
  let A : Set S := {t | Φ (γ t.val).1 ∈ σ ∧ (γ t.val).2 = (γ t₀).2}
  have hAc : IsClosed A :=
    ((I.isClosed_of_mem_faceFan hσ).preimage (Φ.continuous.comp (continuous_fst.comp hγc))).inter
      (isClosed_eq (continuous_snd.comp hγc) continuous_const)
  have hAo : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hp : coordinateGradient φEnd (γ t.val).1 ∈ σ := (hΦeq _).symm ▸ ht.1
    have hθ : (γ t.val).2 ∈ coneTorus σ := ht.2.symm ▸ hθ₀
    have hh := hlocal β ((le_max_left _ _).trans hβ) K hK γ t.val
      (hγ t.val t.property) σ hσ (hne t.val t.property) hp hθ (hnorm t.val t.property)
    have hrestr := continuous_subtype_val.continuousAt.tendsto.eventually hh
    filter_upwards [hrestr] with u hu
    exact ⟨(hΦeq _).symm ▸ hu.2.2, hu.2.1.trans ht.2⟩
  have hAall : A = univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ
    ⟨⟨t₀, ht₀⟩, ⟨(hΦeq _).symm ▸ hp₀, rfl⟩⟩
  intro t ht
  have hh : (⟨t, ht⟩ : S) ∈ A := by rw [hAall]; trivial
  have hp : coordinateGradient φEnd (γ t).1 ∈ σ := hΦeq _ ▸ hh.1
  have hσne : σ ≠ {0} := by
    intro he
    rw [he] at hp₀
    exact hne t₀ ht₀ hp₀
  exact ⟨⟨hne t ht, σ, hσ, hσne, hp, hh.2.symm ▸ hθ₀⟩, hp, hh.2⟩

/-- The actual Legendre conic union and fixed angle are retained through
any connected interval on the norm-one and larger side of the inner fiber. -/
theorem tailoringEndpoint_exists_uniform_ambient_conormal_invariance_on
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (S : Set ℝ), IsPreconnected S → ∀ γ : ℝ → (lgManifold n).Point,
        (∀ t ∈ S, IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        (∀ t ∈ S, 1 ≤ ‖tailoringFamily I β 1 (γ t)‖) →
        ∀ t₀ ∈ S, γ t₀ ∈ tailoringLegendreConic I φEnd →
          ∀ t ∈ S, γ t ∈ tailoringLegendreConic I φEnd ∧ (γ t).2 = (γ t₀).2 := by
  obtain ⟨B, hB, hpiece⟩ := tailoringEndpoint_exists_uniform_ambient_conePiece_invariance_on
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  refine ⟨B, hB, ?_⟩
  intro β hβ K hK S hS γ hγ hnorm t₀ ht₀ hstart
  obtain ⟨_, σ, hσ, _, hpσ, hθσ⟩ := hstart
  intro t ht
  have hh := hpiece β hβ K hK S hS γ hγ hnorm t₀ ht₀ σ hσ hpσ hθσ t ht
  exact ⟨hh.1, hh.2.2⟩

end FsFltz
