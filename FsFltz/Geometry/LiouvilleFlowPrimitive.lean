import FsFltz.Geometry.ExteriorDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Primitive scaling along a smooth local Liouville flow

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158; the Cartan
argument in `lem:shrinking`, lines 624–628; and the required collar bridge
in `sec:lean`, lines 805–821. These are differential-geometric foundations;
they establish no part of the existence target `thm:target`, lines 352–415.

The proof uses the actual differential of a jointly smooth spacetime map.
Pull back the primitive to its open spacetime domain. Its time coefficient
vanishes because the Liouville contraction equation gives α(Z)=dα(Z,Z)=0.
On the constant pair (∂t,v), exterior differentiation is the time derivative
of the spatial coefficient minus the spatial derivative of that zero time
coefficient. Naturality and ι_Z dα=α therefore give the spatial-coefficient
equation q'=q. Differentiating exp(-t)q(t) and applying the mean-value theorem
gives q(t)=exp(t-t₀)q(t₀) on a connected time interval. The argument needs
neither a completion nor its end primitive, and assumes no pullback ODE.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
namespace SmoothManifold

/-- Alternation makes the primitive vanish on its Liouville vector. -/
theorem evalOne_eq_zero_of_liouvilleEquation {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (x : M.Point) (Z : M.Tangent x)
    (hZ : M.LiouvilleEquation alpha x Z) : evalOne alpha x Z = 0 := by
  rw [← hZ Z]
  exact (M.exteriorDerivative alpha x).map_eq_zero_of_eq ![Z, Z]
    (i := 0) (j := 1) rfl (by decide)

/-- Near a point of an open smooth parametrization, the actual pullback
is its coordinate pullback in any chart containing the image point. -/
theorem pullback_from_normedSpace_eventually_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ} (M : SmoothManifold d)
    (f : E → M.Point) {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Model d) ∞ f U)
    (eta : M.Form k) {x : E} (hx : x ∈ U) :
    (fun z => (eta (f z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model d) f z)) =ᶠ[𝓝 x]
    (fun z => (M.formInChart (f x) eta (chartAt (Model d) (f x) (f z))).compContinuousLinearMap
      (fderiv ℝ (chartAt (Model d) (f x) ∘ f) z)) := by
  let b := chartAt (Model d) (f x)
  have hb : f x ∈ b.source := mem_chart_source _ _
  have hnb : ∀ᶠ z in 𝓝 x, f z ∈ b.source :=
    (((hf x hx).contMDiffAt (hU.mem_nhds hx)).continuousAt).preimage_mem_nhds
      (b.open_source.mem_nhds hb)
  filter_upwards [hU.mem_nhds hx, hnb] with z hz hzb
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp z ((mdifferentiable_chart (I := 𝓘(ℝ, Model d))
      (f x)).mdifferentiableAt hzb) (((hf z hz).contMDiffAt
        (hU.mem_nhds hz)).mdifferentiableAt (by simp))]
  rw [← M.formInChart_comp_chartTangentMap eta (f x) (f z) hzb]
  apply ContinuousAlternatingMap.ext
  intro vs
  rfl

/-- Exterior-derivative naturality is local on the open domain of a smooth
parametrization. A local flow need not be smooth outside its time domain. -/
theorem exteriorDerivative_pullback_from_normedSpace_on {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ} (M : SmoothManifold d)
    (f : E → M.Point) {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Model d) ∞ f U)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) {x : E} (hx : x ∈ U) :
    extDeriv (fun z => (eta (f z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model d) f z)) x =
    (M.exteriorDerivative eta (f x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model d) f x) := by
  let b := chartAt (Model d) (f x)
  have hb : f x ∈ b.source := mem_chart_source _ _
  have hB : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hb)
  have hF := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hCoeff : DifferentiableAt ℝ (M.formInChart (f x) eta) ((b ∘ f) x) :=
    ((heta (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hb))).differentiableAt
      (by simp)
  erw [(M.pullback_from_normedSpace_eventually_eq f hU hf eta hx).extDeriv_eq,
    extDeriv_pullback hCoeff (hB.comp x hF).contDiffAt (by simp)]
  erw [← mfderiv_eq_fderiv,
    mfderiv_comp x (hB.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
  apply ContinuousAlternatingMap.ext
  intro vs
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a smooth primitive by a map smooth on an open set gives
genuinely smooth one-form coefficients there. -/
theorem contDiffAt_pullback_one_from_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ} (M : SmoothManifold d)
    (f : E → M.Point) {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Model d) ∞ f U)
    (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha) {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (F := E [⋀^Fin 1]→L[ℝ] ℝ) (fun z => (alpha (f z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model d) f z)) x := by
  let b := chartAt (Model d) (f x)
  have hb : f x ∈ b.source := mem_chart_source _ _
  have hB : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hb)
  let g := b ∘ f
  have hg : ContDiffAt ℝ ∞ g x :=
    (hB.comp x ((hf x hx).contMDiffAt (hU.mem_nhds hx))).contDiffAt
  have hCoeff : ContDiffAt ℝ ∞ (M.formInChart (f x) alpha) (g x) :=
    (halpha (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hb))
  let eM := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hc := (eM.symm.contDiff.contDiffAt.comp x (hCoeff.comp x hg)).clm_comp
    (hg.fderiv_right (by simp))
  have hs := eE.contDiff.contDiffAt.comp x hc
  have hs' : ContDiffAt ℝ ∞ (fun z =>
      (M.formInChart (f x) alpha (g z)).compContinuousLinearMap (fderiv ℝ g z)) x := by
    convert hs using 1
    ext z vs
    change (M.formInChart (f x) alpha (g z)) (fun i => (fderiv ℝ g z) (vs i)) =
      (M.formInChart (f x) alpha (g z)) (fun _ => (fderiv ℝ g z) (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
  exact hs'.congr_of_eventuallyEq
    (M.pullback_from_normedSpace_eventually_eq f hU hf alpha hx)

end SmoothManifold

namespace LiouvilleFlowPrimitive

/-- The actual exterior derivative of a one-form on a normed space has
the usual two directional derivatives, without any smoothness assumption. -/
theorem extDeriv_one_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eta : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x u v : E) :
    extDeriv eta x ![u, v] =
      (fderiv ℝ eta x u) (fun _ => v) - (fderiv ℝ eta x v) (fun _ => u) := by
  have h0 : (0 : Fin 2).removeNth ![u, v] = fun _ => v := by
    funext i
    fin_cases i
    rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = fun _ => u := by
    funext i
    fin_cases i
    rfl
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp only [h0, h1, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth family solving the genuine Liouville equation satisfies the
primitive pullback ODE. This derives the ODE by exterior differentiation;
no equation for the pulled-back primitive is included in the hypotheses. -/
theorem hasDerivAt_spatial_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha)
    (Z : (x : M.Point) → M.Tangent x) (F : ℝ × E → M.Point)
    {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F U)
    (hode : ∀ p ∈ U, mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0) = Z (F p))
    (hZ : ∀ p ∈ U, M.LiouvilleEquation alpha (F p) (Z (F p)))
    {t : ℝ} {y : E} (hp : (t, y) ∈ U) (v : E) :
    HasDerivAt (fun s => SmoothManifold.evalOne alpha (F (s, y))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (s, y) (0, v)))
      (SmoothManifold.evalOne alpha (F (t, y))
        (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y) (0, v))) t := by
  let beta : ℝ × E → (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    (alpha (F p)).compContinuousLinearMap (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p)
  have hbeta : DifferentiableAt ℝ beta (t, y) :=
    (M.contDiffAt_pullback_one_from_normedSpace F hU hF alpha halpha hp).differentiableAt
      (by simp)
  have hzero : (fun p => beta p (fun _ => (1, 0))) =ᶠ[𝓝 (t, y)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with p hpu
    change SmoothManifold.evalOne alpha (F p)
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0)) = 0
    rw [hode p hpu]
    exact M.evalOne_eq_zero_of_liouvilleEquation alpha (F p) (Z (F p)) (hZ p hpu)
  have hzeroDeriv : (fderiv ℝ beta (t, y) (0, v)) (fun _ => (1, 0)) = 0 := by
    change (fderiv ℝ beta (t, y)).flipAlternating (fun _ => (1, 0)) (0, v) = 0
    rw [← fderiv_continuousAlternatingMap_apply_const hbeta (fun _ => (1, 0)),
      hzero.fderiv_eq]
    simp
  have hnat := congrArg (fun eta => eta ![(1, 0), (0, v)])
    (M.exteriorDerivative_pullback_from_normedSpace_on F hU hF alpha halpha hp)
  have hpair : (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y)) ∘ ![(1, 0), (0, v)] =
      ![(mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y)) (1, 0),
        (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y)) (0, v)] := by
    funext i
    fin_cases i <;> rfl
  change extDeriv beta (t, y) ![(1, 0), (0, v)] =
    (M.exteriorDerivative alpha (F (t, y)))
      ((mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y)) ∘ ![(1, 0), (0, v)]) at hnat
  rw [hpair] at hnat
  change extDeriv beta (t, y) ![(1, 0), (0, v)] =
    SmoothManifold.evalTwo (M.exteriorDerivative alpha) (F (t, y))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y) (1, 0))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y) (0, v)) at hnat
  rw [extDeriv_one_apply, hzeroDeriv, sub_zero, hode (t, y) hp,
    hZ (t, y) hp] at hnat
  have hd := (hbeta.hasFDerivAt.continuousAlternatingMap_apply_const
    (fun _ => (0, v))).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hd.congr_deriv hnat

/-- Integration of the derived primitive ODE gives exponential scaling
on any connected open time interval, including negative times. -/
theorem spatial_pullback_eq_exp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (M : SmoothManifold d) (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha)
    (Z : (x : M.Point) → M.Tangent x) (F : ℝ × E → M.Point)
    {J : Set ℝ} {V : Set E} (hJ : IsOpen J) (hJconn : IsPreconnected J) (hV : IsOpen V)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F (J ×ˢ V))
    (hode : ∀ p ∈ J ×ˢ V,
      mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0) = Z (F p))
    (hZ : ∀ p ∈ J ×ˢ V, M.LiouvilleEquation alpha (F p) (Z (F p)))
    {t t₀ : ℝ} {y : E} (ht : t ∈ J) (ht₀ : t₀ ∈ J) (hy : y ∈ V) (v : E) :
    SmoothManifold.evalOne alpha (F (t, y))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t, y) (0, v)) =
    Real.exp (t - t₀) * SmoothManifold.evalOne alpha (F (t₀, y))
      (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (t₀, y) (0, v)) := by
  let q : ℝ → ℝ := fun s => SmoothManifold.evalOne alpha (F (s, y))
    (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F (s, y) (0, v))
  have hq : ∀ s ∈ J, HasDerivAt q (q s) s := fun s hs =>
    hasDerivAt_spatial_pullback M alpha halpha Z F (hJ.prod hV) hF hode hZ ⟨hs, hy⟩ v
  have hw : ∀ s ∈ J, HasDerivAt (fun r => Real.exp (-r) * q r) 0 s := by
    intro s hs
    exact (((hasDerivAt_id s).neg.exp).mul (hq s hs)).congr_deriv (by ring)
  have hconst := hJ.is_const_of_deriv_eq_zero hJconn
    (fun s hs => (hw s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hw s hs).deriv) ht ht₀
  have h := congrArg (fun r => Real.exp t * r) hconst
  simp only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
  simpa only [sub_eq_add_neg, q] using h

set_option backward.isDefEq.respectTransparency false in
/-- The native orbit equation implies the time-direction differential
equation used above. It is an equation for the supplied field, not a
condition on the pulled-back primitive. -/
theorem time_derivative_of_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (M : SmoothManifold d) (Z : (x : M.Point) → M.Tangent x)
    (F : ℝ × E → M.Point) {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞ F U)
    (hode : ∀ p ∈ U, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => F (s, p.2)) p.1 ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F p))))
    {p : ℝ × E} (hp : p ∈ U) :
    mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) F p (1, 0) = Z (F p) := by
  have hinc := hasMFDerivAt_iff_hasFDerivAt.mpr
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  have hc := (((hF p hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p.1 hinc
  have he := congrArg (fun L : ℝ →L[ℝ] M.Tangent (F p) => L (1 : ℝ))
    (hc.mfderiv.symm.trans (hode p hp).mfderiv)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul] at he
  erw [ContinuousLinearMap.inl_apply] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem spatial_mfderiv_comp_inverseChart {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (F : ℝ × N.Point → M.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F)
    (a : N.Point) (t : ℝ) {y : Model e} (hy : y ∈ (chartAt (Model e) a).target)
    (hH : MDifferentiableAt 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d)
      (fun p : ℝ × Model e => F (p.1, (chartAt (Model e) a).symm p.2)) (t, y))
    (v : Model e) :
    mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d)
      (fun p : ℝ × Model e => F (p.1, (chartAt (Model e) a).symm p.2)) (t, y) (0, v) =
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun x => F (t, x))
      ((chartAt (Model e) a).symm y) (N.inverseChartTangentMap a y v) := by
  have hinc := hasMFDerivAt_iff_hasFDerivAt.mpr
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)
  have hslice : MDifferentiable 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun x => F (t, x)) :=
    (hF.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)
  have hleft := mfderiv_comp y hH hinc.mdifferentiableAt
  rw [hinc.mfderiv] at hleft
  have hright := mfderiv_comp y (hslice _)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model e)) a).mdifferentiableAt_symm hy)
  have he := congrArg (fun L : Model e →L[ℝ] M.Tangent (F (t, (chartAt (Model e) a).symm y)) => L v)
    (hleft.symm.trans hright)
  simp only [ContinuousLinearMap.comp_apply] at he
  erw [ContinuousLinearMap.inr_apply] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- Exponential scaling is an equality of the actual manifold pullbacks
for a jointly smooth family of native integral curves. Contraction is
required only along the supplied flow tube; the field need not be Liouville
outside that image. The proof uses this same parametrization and its actual
ODE, with no primitive-scaling certificate or new choice of flow. -/
theorem pullback_slice_eq_exp_smul_of_local_contraction {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (alpha : M.Form 1)
    (halpha : M.IsSmoothForm alpha) (Z : (x : M.Point) → M.Tangent x)
    (F : ℝ × N.Point → M.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F)
    {J : Set ℝ} {V : Set N.Point} (hJ : IsOpen J) (hJconn : IsPreconnected J)
    (hV : IsOpen V)
    (hZ : ∀ p ∈ J ×ˢ V, M.LiouvilleEquation alpha (F p) (Z (F p)))
    (hode : ∀ x ∈ V, ∀ t ∈ J, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => F (s, x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F (t, x)))))
    {t t₀ : ℝ} {x : N.Point} (ht : t ∈ J) (ht₀ : t₀ ∈ J) (hx : x ∈ V) :
    N.pullback M (fun x => F (t, x)) alpha x =
      Real.exp (t - t₀) • N.pullback M (fun x => F (t₀, x)) alpha x := by
  let c := chartAt (Model e) x
  let W := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.isOpen_inter_preimage_symm hV
  have hxs : x ∈ c.source := mem_chart_source _ _
  have hxt : c x ∈ W := ⟨c.map_source hxs, by simpa only [mem_preimage, c.left_inv hxs] using hx⟩
  let H : ℝ × Model e → M.Point := fun p => F (p.1, c.symm p.2)
  have hcs : ContMDiffOn 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model e) ∞
      (fun p => c.symm p.2) (J ×ˢ W) := by
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model e)) (x := x)).comp
      (contMDiffOn_iff_contDiffOn.mpr contDiffOn_snd) (fun p hp => hp.2.1)
  have hH : ContMDiffOn 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) ∞ H (J ×ˢ W) := by
    apply hF.comp_contMDiffOn
    apply ContMDiffOn.prodMk _ hcs
    exact contMDiffOn_iff_contDiffOn.mpr contDiffOn_fst
  have hHode : ∀ p ∈ J ×ˢ W,
      mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H p (1, 0) = Z (H p) := by
    intro p hp
    exact time_derivative_of_orbit M Z H (hJ.prod hW) hH
      (fun p hp => hode (c.symm p.2) hp.2.2 p.1 hp.1) hp
  have hspatial : ∀ s ∈ J, ∀ v : N.Tangent x,
      mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (s, c x)
        (0, N.chartTangentMap x x v) =
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun x => F (s, x)) x v := by
    intro s hs v
    have hd := spatial_mfderiv_comp_inverseChart M N F hF x s hxt.1
      (((hH (s, c x) ⟨hs, hxt⟩).contMDiffAt
        ((hJ.prod hW).mem_nhds ⟨hs, hxt⟩)).mdifferentiableAt (by simp))
      (N.chartTangentMap x x v)
    have hinv := congrArg (fun L : N.Tangent x →L[ℝ] N.Tangent x => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model e)) x).symm_comp_deriv hxs)
    change N.inverseChartTangentMap x (c x) (N.chartTangentMap x x v) = v at hinv
    change mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (s, c x)
      (0, N.chartTangentMap x x v) =
      mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) (fun x => F (s, x)) (c.symm (c x))
        (N.inverseChartTangentMap x (c x) (N.chartTangentMap x x v)) at hd
    rw [c.left_inv hxs] at hd
    erw [hinv] at hd
    exact hd
  apply ContinuousAlternatingMap.ext
  intro vs
  have hscale := spatial_pullback_eq_exp_mul M alpha halpha Z H hJ hJconn hW hH
    hHode (fun p hp => hZ (p.1, c.symm p.2) ⟨hp.1, hp.2.2⟩)
    ht ht₀ hxt (N.chartTangentMap x x (vs 0))
  change SmoothManifold.evalOne alpha (F (t, c.symm (c x)))
      (mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (t, c x)
        (0, N.chartTangentMap x x (vs 0))) =
    Real.exp (t - t₀) * SmoothManifold.evalOne alpha (F (t₀, c.symm (c x)))
      (mfderiv 𝓘(ℝ, ℝ × Model e) 𝓘(ℝ, Model d) H (t₀, c x)
        (0, N.chartTangentMap x x (vs 0))) at hscale
  rw [c.left_inv hxs, hspatial t ht, hspatial t₀ ht₀] at hscale
  convert hscale using 1 <;> apply congrArg _ <;> funext i <;> rw [Fin.eq_zero i]

/-- The globally Liouville version specializes the local contraction law. -/
theorem pullback_slice_eq_exp_smul {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (alpha : M.Form 1)
    (halpha : M.IsSmoothForm alpha) (Z : (x : M.Point) → M.Tangent x)
    (hZ : ∀ x, M.LiouvilleEquation alpha x (Z x)) (F : ℝ × N.Point → M.Point)
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) 𝓘(ℝ, Model d) ∞ F)
    {J : Set ℝ} {V : Set N.Point} (hJ : IsOpen J) (hJconn : IsPreconnected J)
    (hV : IsOpen V)
    (hode : ∀ x ∈ V, ∀ t ∈ J, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => F (s, x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F (t, x)))))
    {t t₀ : ℝ} {x : N.Point} (ht : t ∈ J) (ht₀ : t₀ ∈ J) (hx : x ∈ V) :
    N.pullback M (fun x => F (t, x)) alpha x =
      Real.exp (t - t₀) • N.pullback M (fun x => F (t₀, x)) alpha x :=
  pullback_slice_eq_exp_smul_of_local_contraction M N alpha halpha Z F hF
    hJ hJconn hV (fun p _ => hZ (F p)) hode ht ht₀ hx

end LiouvilleFlowPrimitive
end FsFltz.Geometry
