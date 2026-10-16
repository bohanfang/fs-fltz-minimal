import FsFltz.Geometry.IntrinsicCollarCompact
import FsFltz.Geometry.LiouvilleFlowPrimitive

/-!
# Primitive scaling on the inward intrinsic collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160,
`lem:shrinking`, lines 624–628, and the required collar bridge in
`sec:lean`, lines 805–814. The inward sign is `ι_f dα = -α`.
The coordinate proof uses actual derivatives of the collar trajectories,
derives the spatial primitive ODE, and includes the time tangent.
Only the native, nonnegative side satisfies the contraction equation;
no Liouville extension to the other side is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

private theorem contDiffAt_one_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : F → F [⋀^Fin 1]→L[ℝ] ℝ) (C : E → F) (p : E)
    (ha : ContDiffAt ℝ ∞ alpha (C p)) (hC : ContDiffAt ℝ ∞ C p) :
    ContDiffAt ℝ ∞ (fun q => (alpha (C q)).compContinuousLinearMap (fderiv ℝ C q)) p := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp p (ha.comp p hC)).clm_comp
    (hC.fderiv_right (by simp))
  have hs := eE.contDiff.contDiffAt.comp p h
  convert hs using 1
  ext q vs
  change alpha (C q) (fun i => fderiv ℝ C q (vs i)) =
    alpha (C q) (fun _ => fderiv ℝ C q (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- The inward contraction equation forces the primitive's time coefficient
to vanish. This is alternation, rather than an extra collar hypothesis. -/
theorem one_eq_zero_of_inward_contraction {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : F → F [⋀^Fin 1]→L[ℝ] ℝ) (x f : F)
    (h : ∀ v, extDeriv alpha x ![f, v] = -alpha x (fun _ => v)) :
    alpha x (fun _ => f) = 0 := by
  have hz := (extDeriv alpha x).map_eq_zero_of_eq ![f, f]
    (i := 0) (j := 1) rfl (by decide)
  rw [h f] at hz
  exact neg_eq_zero.mp hz

/-- On the positive-time interior of an inward collar the actual spatial
primitive coefficient solves `q' = -q`. The proof derives this from exterior
derivative naturality and the actual trajectory ODE. -/
theorem hasDerivAt_inward_spatial_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : F → F [⋀^Fin 1]→L[ℝ] ℝ) (f : F → F) (C : ℝ × E → F)
    {U : Set F} {P : Set (ℝ × E)} (hU : IsOpen U) (hP : IsOpen P)
    (ha : ContDiffOn ℝ ∞ alpha U) (hC : ContDiffOn ℝ ∞ C P)
    (hmaps : MapsTo C P U)
    (hode : ∀ p ∈ P, HasDerivAt (fun s => C (s, p.2)) (f (C p)) p.1)
    (hcontr : ∀ p ∈ P, ∀ v, extDeriv alpha (C p) ![f (C p), v] =
      -alpha (C p) (fun _ => v))
    {t : ℝ} {y : E} (hp : (t, y) ∈ P) (v : E) :
    HasDerivAt (fun s => alpha (C (s, y)) (fun _ => fderiv ℝ C (s, y) (0, v)))
      (-alpha (C (t, y)) (fun _ => fderiv ℝ C (t, y) (0, v))) t := by
  let beta : ℝ × E → (ℝ × E) [⋀^Fin 1]→L[ℝ] ℝ := fun p =>
    (alpha (C p)).compContinuousLinearMap (fderiv ℝ C p)
  have hc (p) (hp : p ∈ P) : ContDiffAt ℝ ∞ C p := (hC p hp).contDiffAt (hP.mem_nhds hp)
  have hat (p) (hp : p ∈ P) : ContDiffAt ℝ ∞ alpha (C p) :=
    (ha _ (hmaps hp)).contDiffAt (hU.mem_nhds (hmaps hp))
  have htime (p) (hp : p ∈ P) : fderiv ℝ C p (1, 0) = f (C p) := by
    have hd := (hc p hp).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    exact hd.unique (hode p hp)
  have hbeta : DifferentiableAt ℝ beta (t, y) :=
    (contDiffAt_one_pullback alpha C (t, y) (hat _ hp) (hc _ hp)).differentiableAt (by simp)
  have hzero : (fun p => beta p (fun _ => (1, 0))) =ᶠ[𝓝 (t, y)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hP.mem_nhds hp] with p hpp
    change alpha (C p) (fun _ => fderiv ℝ C p (1, 0)) = 0
    rw [htime p hpp]
    exact one_eq_zero_of_inward_contraction alpha (C p) (f (C p)) (hcontr p hpp)
  have hzeroDeriv : (fderiv ℝ beta (t, y) (0, v)) (fun _ => (1, 0)) = 0 := by
    change (fderiv ℝ beta (t, y)).flipAlternating (fun _ => (1, 0)) (0, v) = 0
    rw [← fderiv_continuousAlternatingMap_apply_const hbeta (fun _ => (1, 0)), hzero.fderiv_eq]
    simp
  have hnat := congrArg (fun eta => eta ![(1, 0), (0, v)])
    (extDeriv_pullback ((hat _ hp).differentiableAt (by simp)) (hc _ hp) (by simp))
  change extDeriv beta (t, y) ![(1, 0), (0, v)] =
    extDeriv alpha (C (t, y)) ((fderiv ℝ C (t, y)) ∘ ![(1, 0), (0, v)]) at hnat
  have hpair : (fderiv ℝ C (t, y)) ∘ ![(1, 0), (0, v)] =
      ![fderiv ℝ C (t, y) (1, 0), fderiv ℝ C (t, y) (0, v)] := by
    funext i
    fin_cases i <;> rfl
  rw [hpair, htime _ hp, hcontr _ hp, LiouvilleFlowPrimitive.extDeriv_one_apply,
    hzeroDeriv, sub_zero] at hnat
  have hd := (hbeta.hasFDerivAt.continuousAlternatingMap_apply_const (fun _ => (0, v))).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hd.congr_deriv hnat

/-- The spatial primitive law on the entire inward strip, including its
boundary seam. The contraction equation is required only on that strip;
the auxiliary smooth parametrization may lie outside the native half-space
at negative times. -/
theorem inward_spatial_pullback_eq_exp_mul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : F → F [⋀^Fin 1]→L[ℝ] ℝ) (f : F → F) (C : ℝ × E → F)
    {U : Set F} {V : Set E} {δ : ℝ} (hU : IsOpen U) (hV : IsOpen V) (hδ : 0 < δ)
    (ha : ContDiffOn ℝ ∞ alpha U)
    (hC : ContDiffOn ℝ ∞ C (Ioo (-δ) δ ×ˢ V))
    (hmaps : MapsTo C (Ico 0 δ ×ˢ V) U)
    (hode : ∀ p ∈ Ico 0 δ ×ˢ V,
      HasDerivAt (fun s => C (s, p.2)) (f (C p)) p.1)
    (hcontr : ∀ p ∈ Ico 0 δ ×ˢ V, ∀ v,
      extDeriv alpha (C p) ![f (C p), v] = -alpha (C p) (fun _ => v))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (v : E) :
    alpha (C (t, y)) (fun _ => fderiv ℝ C (t, y) (0, v)) =
      Real.exp (-t) * alpha (C (0, y)) (fun _ => fderiv ℝ C (0, y) (0, v)) := by
  let q : ℝ → ℝ := fun s => alpha (C (s, y)) (fun _ => fderiv ℝ C (s, y) (0, v))
  have hsub : Ioo 0 δ ×ˢ V ⊆ Ico 0 δ ×ˢ V := prod_mono Ioo_subset_Ico_self Subset.rfl
  have hCpos : ContDiffOn ℝ ∞ C (Ioo 0 δ ×ˢ V) := hC.mono
    (prod_mono (Ioo_subset_Ioo_left (neg_nonpos.mpr hδ.le)) Subset.rfl)
  have hq : ∀ s ∈ Ioo 0 δ, HasDerivAt q (-q s) s := fun s hs =>
    hasDerivAt_inward_spatial_pullback alpha f C hU (isOpen_Ioo.prod hV) ha hCpos
      (hmaps.mono hsub Subset.rfl) (fun p hp => hode p (hsub hp))
      (fun p hp => hcontr p (hsub hp)) ⟨hs, hy⟩ v
  have hw : ∀ s ∈ Ioo 0 δ, HasDerivAt (fun r => Real.exp r * q r) 0 s := by
    intro s hs
    exact ((Real.hasDerivAt_exp s).mul (hq s hs)).congr_deriv (by ring)
  have hzero : ContinuousAt q 0 := by
    have hp : (0, y) ∈ Ioo (-δ) δ ×ˢ V := ⟨⟨neg_neg_of_pos hδ, hδ⟩, hy⟩
    have hc := (hC _ hp).contDiffAt ((isOpen_Ioo.prod hV).mem_nhds hp)
    have hm : C (0, y) ∈ U := hmaps (show (0, y) ∈ Ico 0 δ ×ˢ V from ⟨⟨le_rfl, hδ⟩, hy⟩)
    have ha₀ := (ha _ hm).contDiffAt (hU.mem_nhds hm)
    have hb := (contDiffAt_one_pullback alpha C (0, y) ha₀ hc).differentiableAt (by simp)
    have hinc : ContinuousAt (fun s : ℝ => (s, y)) 0 := continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun s : ℝ => (s, y))
      (hb.hasFDerivAt.continuousAlternatingMap_apply_const (fun _ => (0, v))).continuousAt hinc
  by_cases hzt : t = 0
  · simp [hzt]
  have htpos : t ∈ Ioo 0 δ := ⟨lt_of_le_of_ne ht.1 (Ne.symm hzt), ht.2⟩
  have hcst : ∀ s ∈ Ioo 0 δ, Real.exp s * q s = Real.exp t * q t :=
    fun s hs => isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 δ).isPreconnected
      (fun s hs => (hw s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hw s hs).deriv) hs htpos
  have hseam : Real.exp 0 * q 0 = Real.exp t * q t :=
    ((Real.continuous_exp.continuousAt).mul hzero).continuousWithinAt.eq_const_of_mem_closure
      (by rw [closure_Ioo (ne_of_lt hδ)]; exact ⟨le_rfl, hδ.le⟩) hcst
  have he := congrArg (fun r => Real.exp (-t) * r) hseam
  simp only [Real.exp_zero, one_mul, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul] at he
  exact he.symm

/-- Full tangent identity for an inward collar, including arbitrary time
components. This is the complete one-form pullback law, rather than only
the fixed-time slice law. -/
theorem inward_pullback_eq_exp_mul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (alpha : F → F [⋀^Fin 1]→L[ℝ] ℝ) (f : F → F) (C : ℝ × E → F)
    {U : Set F} {V : Set E} {δ : ℝ} (hU : IsOpen U) (hV : IsOpen V) (hδ : 0 < δ)
    (ha : ContDiffOn ℝ ∞ alpha U)
    (hC : ContDiffOn ℝ ∞ C (Ioo (-δ) δ ×ˢ V))
    (hmaps : MapsTo C (Ico 0 δ ×ˢ V) U)
    (hode : ∀ p ∈ Ico 0 δ ×ˢ V,
      HasDerivAt (fun s => C (s, p.2)) (f (C p)) p.1)
    (hcontr : ∀ p ∈ Ico 0 δ ×ˢ V, ∀ v,
      extDeriv alpha (C p) ![f (C p), v] = -alpha (C p) (fun _ => v))
    {t : ℝ} {y : E} (ht : t ∈ Ico 0 δ) (hy : y ∈ V) (r : ℝ) (v : E) :
    alpha (C (t, y)) (fun _ => fderiv ℝ C (t, y) (r, v)) =
      Real.exp (-t) * alpha (C (0, y)) (fun _ => fderiv ℝ C (0, y) (0, v)) := by
  have htime : fderiv ℝ C (t, y) (1, 0) = f (C (t, y)) := by
    have hp : (t, y) ∈ Ioo (-δ) δ ×ˢ V := ⟨⟨by linarith [ht.1], ht.2⟩, hy⟩
    have hd := ((hC _ hp).contDiffAt ((isOpen_Ioo.prod hV).mem_nhds hp)).differentiableAt
      (by simp) |>.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact hd.unique (hode (t, y) ⟨ht, hy⟩)
  have hsp := inward_spatial_pullback_eq_exp_mul alpha f C hU hV hδ ha hC hmaps hode hcontr ht hy v
  have hdecomp : (r, v) = r • (1, (0 : E)) + (0, v) := by simp
  rw [hdecomp, map_add, map_smul, htime]
  have heval : alpha (C (t, y)) (fun _ => r • f (C (t, y)) + fderiv ℝ C (t, y) (0, v)) =
      r * alpha (C (t, y)) (fun _ => f (C (t, y))) +
        alpha (C (t, y)) (fun _ => fderiv ℝ C (t, y) (0, v)) := by
    change ((ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).symm (alpha (C (t, y))))
        (r • f (C (t, y)) + fderiv ℝ C (t, y) (0, v)) = _
    simp only [map_add, map_smul, smul_eq_mul]
    rfl
  rw [heval, one_eq_zero_of_inward_contraction alpha _ _ (hcontr (t, y) ⟨ht, hy⟩),
    mul_zero, zero_add]
  exact hsp

end FsFltz.Geometry.IntrinsicCollar
