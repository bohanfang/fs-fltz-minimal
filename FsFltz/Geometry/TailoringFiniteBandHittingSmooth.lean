import FsFltz.Geometry.TailoringFiniteBandHitting
import Mathlib.Analysis.Calculus.ImplicitContDiff
import FsFltz.Geometry.LocalInverse

/-!
# Smooth time at a constructed transverse finite hit

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775.
This is the analytic implicit-function producer for the literal scalar
equation of an orbit. Parameters may include the extended coefficient and
initial-point coordinates. It assumes no smooth hitting function.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Topology ContDiff
open scoped Manifold

namespace FsFltz.Geometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A nonzero scalar time derivative is precisely an invertible partial
differential, so a transverse scalar equation constructs its smooth local
time, with the actual hitting equation on a neighborhood. -/
theorem exists_smooth_local_hitting_time
    {H : E × ℝ → ℝ} {p : E} {t q b : ℝ}
    (hH : ContDiffAt ℝ ∞ H (p, t)) (hhit : H (p, t) = b)
    (hder : HasDerivAt (fun s => H (p, s)) q t) (hq : q ≠ 0) :
    ∃ τ : E → ℝ, τ p = t ∧ ContDiffAt ℝ ∞ τ p ∧
      ∀ᶠ x in 𝓝 p, H (x, τ x) = b := by
  have hd := hH.differentiableAt (by simp)
  have hpartial : (fderiv ℝ H (p, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      (1 : ℝ →L[ℝ] ℝ).smulRight q := by
    have hs : HasFDerivAt (fun s : ℝ => (p, s))
        (ContinuousLinearMap.inr ℝ E ℝ) t :=
      (hasFDerivAt_const p t).prodMk (hasFDerivAt_id t)
    exact ((hd.hasFDerivAt.comp t hs).unique hder.hasFDerivAt)
  have hinv : ((fderiv ℝ H (p, t)).comp
      (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [hpartial]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (1 : ℝ →L[ℝ] ℝ).smulRight q⁻¹)
    · ext
      simp [smul_eq_mul, hq]
    · ext
      simp [smul_eq_mul, hq]
  let τ := hH.implicitFunction (by simp) hinv
  refine ⟨τ, hH.implicitFunction_apply_self (by simp) hinv,
    hH.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  simpa only [hhit] using hH.eventually_apply_implicitFunction (by simp) hinv

/-- The lower speed producer supplies a finite hit; the actual nonzero
derivative at that hit then constructs smooth dependence on all parameters.
The time is strictly smaller than an extended interval endpoint so that
transversality at the hit follows from the stated bound. -/
theorem exists_finite_hit_with_smooth_local_time
    {H : E × ℝ → ℝ} {p : E} {b ε : ℝ}
    (hH : ContDiff ℝ ∞ H) (hε : 0 < ε) (hzero : H (p, 0) < b)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) ((b - H (p, 0) + 2) / ε),
      H (p, t) ≤ b → ε ≤ deriv (fun s => H (p, s)) t) :
    ∃ (t : ℝ) (τ : E → ℝ),
      t ∈ Ioc (0 : ℝ) ((b - H (p, 0) + 1) / ε) ∧ H (p, t) = b ∧
      τ p = t ∧ ContDiffAt ℝ ∞ τ p ∧
      ∀ᶠ x in 𝓝 p, H (x, τ x) = b := by
  have hg : Differentiable ℝ (fun t => H (p, t)) :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hwide : (b - H (p, 0) + 1) / ε < (b - H (p, 0) + 2) / ε := by
    apply (div_lt_div_iff_of_pos_right hε).mpr
    linarith
  obtain ⟨t, ht, he⟩ := exists_pos_time_scalar_eq_of_lower_speed hg hε hzero
    (fun t ht => hspeed t ⟨ht.1, ht.2.trans hwide⟩)
  have htwide : t ∈ Ioo (0 : ℝ) ((b - H (p, 0) + 2) / ε) :=
    ⟨ht.1, ht.2.trans_lt hwide⟩
  have hpos := hε.trans_le (hspeed t htwide he.le)
  obtain ⟨τ, hτ, hτsmooth, hτhit⟩ := exists_smooth_local_hitting_time
    hH.contDiffAt he (hg t).hasDerivAt hpos.ne'
  exact ⟨t, τ, ht, he, hτ, hτsmooth, hτhit⟩

omit [CompleteSpace E] in
/-- A genuinely smooth equation produces one actual open neighborhood on
which the hitting time is jointly `C∞`, rather than only `C∞` at one point.
The local inverse preserves every initial parameter coordinate literally. -/
theorem exists_smooth_hitting_time_neighborhood [FiniteDimensional ℝ E]
    {H : E × ℝ → ℝ} {p : E} {t q b : ℝ}
    (hH : ContDiff ℝ ∞ H) (hhit : H (p, t) = b)
    (hder : HasDerivAt (fun s => H (p, s)) q t) (hq : q ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∃ τ : E → ℝ,
      ContDiffOn ℝ ∞ τ U ∧ τ p = t ∧ ∀ x ∈ U, H (x, τ x) = b := by
  let S : E × ℝ → E × ℝ := fun z => (z.1, H z)
  have hS : ContDiff ℝ ∞ S := contDiff_fst.prodMk hH
  let A := fderiv ℝ H (p, t)
  have hpartial : A.comp (ContinuousLinearMap.inr ℝ E ℝ) =
      (1 : ℝ →L[ℝ] ℝ).smulRight q := by
    exact (((hH.differentiable (by simp) (p, t)).hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))).unique hder.hasFDerivAt)
  have htime (r : ℝ) : A (0, r) = r * q := by
    exact congrArg (fun L : ℝ →L[ℝ] ℝ => L r) hpartial
  have hsplit (x : E) (r : ℝ) : A (x, r) = A (x, 0) + r * q := by
    rw [show (x, r) = (x, 0) + (0, r) by simp, map_add, htime]
  have hdf : fderiv ℝ S (p, t) = (ContinuousLinearMap.fst ℝ E ℝ).prod A := by
    exact ((hasFDerivAt_fst.prodMk
      (hH.differentiable (by simp) (p, t)).hasFDerivAt).fderiv)
  have hbij : Bijective (fderiv ℝ S (p, t)) := by
    rw [hdf]
    constructor
    · rintro ⟨x, r⟩ ⟨y, s⟩ he
      have hxy : x = y := congrArg Prod.fst he
      subst y
      have hrs := congrArg Prod.snd he
      change A (x, r) = A (x, s) at hrs
      rw [hsplit x r, hsplit x s] at hrs
      exact Prod.ext rfl (mul_right_cancel₀ hq (add_left_cancel hrs))
    · rintro ⟨x, r⟩
      refine ⟨(x, (r - A (x, 0)) / q), Prod.ext rfl ?_⟩
      change A (x, (r - A (x, 0)) / q) = r
      rw [hsplit, div_mul_cancel₀ _ hq]
      ring
  have hlocal := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    isOpen_univ hS.contMDiff.contMDiffOn (mem_univ (p, t))
    (by
      rw [mfderiv_eq_fderiv]
      exact ⟨fun _ _ he => hbij.1 he, fun y => hbij.2 y⟩)
  let l := hlocal.localInverse
  let U : Set E := (fun x => (x, b)) ⁻¹' l.source
  have hU : IsOpen U := l.open_source.preimage (continuous_id.prodMk continuous_const)
  have hpU : p ∈ U := by
    simpa only [U, l, mem_preimage, S, hhit] using hlocal.localInverse_mem_source
  let τ : E → ℝ := fun x => (l (x, b)).2
  have hτ : ContDiffOn ℝ ∞ τ U := by
    have hl : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ l l.source :=
      hlocal.localInverse_contMDiffOn
    have hm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E × ℝ) ∞
        (fun x => l (x, b)) U :=
      hl.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
        (fun _ hx => hx)
    exact (contMDiffOn_iff_contDiffOn.mp hm).snd
  have hleft : l (p, b) = (p, t) := by
    simpa only [S, hhit, l] using
      hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  refine ⟨U, hU, hpU, τ, hτ, congrArg Prod.snd hleft, ?_⟩
  intro x hx
  have he := hlocal.localInverse_right_inv hx
  have hfst : (l (x, b)).1 = x := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  change H (l (x, b)) = b at hsnd
  rw [← Prod.eta (l (x, b)), hfst] at hsnd
  exact hsnd

/-- The finite speed estimate constructs a hit and an actual smooth time
on one open neighborhood of the whole initial-parameter tuple. -/
theorem exists_finite_hit_with_smooth_time_neighborhood [FiniteDimensional ℝ E]
    {H : E × ℝ → ℝ} {p : E} {b ε : ℝ}
    (hH : ContDiff ℝ ∞ H) (hε : 0 < ε) (hzero : H (p, 0) < b)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) ((b - H (p, 0) + 2) / ε),
      H (p, t) ≤ b → ε ≤ deriv (fun s => H (p, s)) t) :
    ∃ (t : ℝ) (U : Set E),
      t ∈ Ioc (0 : ℝ) ((b - H (p, 0) + 1) / ε) ∧ H (p, t) = b ∧
      IsOpen U ∧ p ∈ U ∧ ∃ τ : E → ℝ,
        ContDiffOn ℝ ∞ τ U ∧ τ p = t ∧ ∀ x ∈ U, H (x, τ x) = b := by
  obtain ⟨t, _, ht, he, _, _, _⟩ :=
    exists_finite_hit_with_smooth_local_time hH hε hzero hspeed
  have hwide : (b - H (p, 0) + 1) / ε < (b - H (p, 0) + 2) / ε := by
    apply (div_lt_div_iff_of_pos_right hε).mpr
    linarith
  have hg : Differentiable ℝ (fun s => H (p, s)) :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hpos := hε.trans_le (hspeed t ⟨ht.1, ht.2.trans_lt hwide⟩ he.le)
  obtain ⟨U, hU, hpU, τ, hτ, hτp, hτhit⟩ :=
    exists_smooth_hitting_time_neighborhood hH he (hg t).hasDerivAt hpos.ne'
  exact ⟨t, U, ht, he, hU, hpU, τ, hτ, hτp, hτhit⟩

end FsFltz.Geometry
