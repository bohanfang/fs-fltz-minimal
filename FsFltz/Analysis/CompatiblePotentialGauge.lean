import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Tactic.Linarith

/-!
# Smooth radial gauges for the compatible potential

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 587–593 and
617–620. The convex body is the literal sublevel of a smooth convex function.
Its Minkowski gauge is Mathlib's `gauge`. Radial transversality is proved
from convexity and the strict inequality at zero, rather than assumed.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convexity controls the radial derivative at every point. -/
theorem sub_zero_le_fderiv_self_of_convex {q : E → ℝ}
    (hq : ConvexOn ℝ univ q) {x : E} (hd : DifferentiableAt ℝ q x) :
    q x - q 0 ≤ fderiv ℝ q x x := by
  let L : ℝ →ₗ[ℝ] E := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight x
  have hc : ConvexOn ℝ univ (fun t : ℝ => q (t • x)) := by
    simpa [L, Function.comp_def] using hq.comp_linearMap L
  have ht : HasDerivAt (fun t : ℝ => q (t • x)) (fderiv ℝ q x x) 1 := by
    have hd' : HasFDerivAt q (fderiv ℝ q x) ((1 : ℝ) • x) := by
      simpa using hd.hasFDerivAt
    convert hd'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x) using 1 <;>
      simp [Function.comp_def]
  simpa [slope] using hc.slope_le_of_hasDerivAt (mem_univ 0) (mem_univ 1)
    zero_lt_one ht

/-- The radial derivative is strictly positive on the unit level. -/
theorem fderiv_self_pos_of_convex_level {q : E → ℝ}
    (hq : ConvexOn ℝ univ q) (h₀ : q 0 < 1) {x : E}
    (hd : DifferentiableAt ℝ q x) (hx : q x = 1) :
    0 < fderiv ℝ q x x := by
  have h := sub_zero_le_fderiv_self_of_convex hq hd
  rw [hx] at h
  linarith

omit [NormedSpace ℝ E] in
/-- The unit sublevel is a neighborhood of zero. -/
theorem convexSublevel_mem_nhds_zero {q : E → ℝ}
    (hq : Continuous q) (h₀ : q 0 < 1) : {x | q x ≤ 1} ∈ 𝓝 (0 : E) := by
  have h : ∀ᶠ x in 𝓝 (0 : E), q x < 1 :=
    hq.continuousAt.eventually (gt_mem_nhds h₀)
  exact Filter.mem_of_superset h (fun z hx => (show q z < 1 from hx).le)

/-- Normalizing a nonzero vector by the actual Minkowski gauge puts it on
the defining unit level, including for a non-symmetric convex body. -/
theorem apply_inv_gauge_smul_eq_one {q : E → ℝ}
    (hq : Continuous q) (hc : ConvexOn ℝ univ q) (h₀ : q 0 < 1)
    (hb : Bornology.IsBounded {x | q x ≤ 1}) {x : E} (hx : x ≠ 0) :
    q ((gauge {z | q z ≤ 1} x)⁻¹ • x) = 1 := by
  have hs : Convex ℝ {z | q z ≤ 1} := by simpa using hc.convex_le 1
  have hn := convexSublevel_mem_nhds_zero hq h₀
  have hp : 0 < gauge {z | q z ≤ 1} x :=
    (gauge_pos (absorbent_nhds_zero hn) ((NormedSpace.isVonNBounded_iff ℝ).mpr hb)).mpr hx
  apply frontier_le_subset_eq hq continuous_const
  apply (gauge_eq_one_iff_mem_frontier hs hn).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le)]
  exact inv_mul_cancel₀ hp.ne'

/-- The gauge is convex; this uses its actual subadditivity and homogeneity. -/
theorem convexOn_gauge_of_convex {s : Set E} (hs : Convex ℝ s)
    (h₀ : s ∈ 𝓝 (0 : E)) : ConvexOn ℝ univ (gauge s) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  simpa only [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul]
    using gauge_add_le hs (absorbent_nhds_zero h₀) (a • x) (b • y)

/-- A smooth convex defining function with a bounded unit sublevel gives a
smooth Minkowski gauge away from zero. The implicit equation is solved for
the reciprocal radius; positivity of its derivative is a consequence of
convexity, not an additional regularity hypothesis. -/
theorem contDiffAt_gauge_convexSublevel [CompleteSpace E] {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ConvexOn ℝ univ q) (h₀ : q 0 < 1)
    (hb : Bornology.IsBounded {x | q x ≤ 1}) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (gauge {z | q z ≤ 1}) x := by
  let s : Set E := {z | q z ≤ 1}
  let j : E → ℝ := gauge s
  have hs : Convex ℝ s := by simpa [s] using hc.convex_le 1
  have hn : s ∈ 𝓝 (0 : E) := convexSublevel_mem_nhds_zero hq.continuous h₀
  have hj : Continuous j := continuous_gauge hs hn
  have hp : 0 < j x :=
    (gauge_pos (absorbent_nhds_zero hn) ((NormedSpace.isVonNBounded_iff ℝ).mpr hb)).mpr hx
  let t : ℝ := (j x)⁻¹
  let y : E := t • x
  have ht : 0 < t := inv_pos.mpr hp
  have hy : q y = 1 := apply_inv_gauge_smul_eq_one hq.continuous hc h₀ hb hx
  have hdy : 0 < fderiv ℝ q y y :=
    fderiv_self_pos_of_convex_level hc h₀ (hq.differentiable (by simp) y) hy
  have hdpos : 0 < fderiv ℝ q y x := by
    have he : fderiv ℝ q y y = t * fderiv ℝ q y x := by simp [y]
    rw [he] at hdy
    exact (mul_pos_iff_of_pos_left ht).mp hdy
  let F : E × ℝ → ℝ := fun z => q (z.2 • z.1)
  let D : E × ℝ →L[ℝ] ℝ := (fderiv ℝ q y).comp
    (t • ContinuousLinearMap.fst ℝ E ℝ +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight x)
  have hD : HasFDerivAt F D (x, t) := by
    convert (hq.differentiable (by simp) y).hasFDerivAt.comp (x, t)
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (x, t))).smul
        (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, t)))) using 1
    simp [F, Function.comp_def]
  have hF : ContDiffAt ℝ ∞ F (x, t) := by
    exact hq.contDiffAt.comp (x, t) (contDiffAt_snd.smul contDiffAt_fst)
  have hi : (fderiv ℝ F (x, t) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    let e : ℝ ≃L[ℝ] ℝ :=
      (LinearEquiv.smulOfNeZero ℝ ℝ (fderiv ℝ q y x) hdpos.ne').toContinuousLinearEquiv
    refine ⟨e, ?_⟩
    rw [hD.fderiv]
    ext
    simp [e, D, mul_comm]
  let ψ : E → ℝ := hF.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ x := hF.contDiffAt_implicitFunction (by simp) hi
  have htcont : ContinuousAt (fun z => (j z)⁻¹) x := hj.continuousAt.inv₀ hp.ne'
  have hpair : Tendsto (fun z => (z, (j z)⁻¹)) (𝓝 x) (𝓝 (x, t)) :=
    continuousAt_id.prodMk htcont
  have heq : (fun z => (j z)⁻¹) =ᶠ[𝓝 x] ψ := by
    have hlocal := hpair.eventually
      (hF.eventually_apply_eq_iff_implicitFunction (by simp) hi)
    filter_upwards [hlocal, isOpen_compl_singleton.mem_nhds hx] with z hz hz₀
    apply (hz.mp ?_).symm
    change q ((j z)⁻¹ • z) = q y
    rw [hy]
    exact apply_inv_gauge_smul_eq_one hq.continuous hc h₀ hb hz₀
  have htSmooth : ContDiffAt ℝ ∞ (fun z => (j z)⁻¹) x :=
    hψ.congr_of_eventuallyEq heq
  simpa [Pi.inv_def, j, s] using htSmooth.inv (inv_ne_zero hp.ne')

/-- The exact differential of the radial gauge is a positive scalar multiple
of the defining differential at the normalized point. -/
theorem fderiv_gauge_convexSublevel [CompleteSpace E] {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ConvexOn ℝ univ q) (h₀ : q 0 < 1)
    (hb : Bornology.IsBounded {x | q x ≤ 1}) {x : E} (hx : x ≠ 0) :
    let j := gauge {z | q z ≤ 1}
    let y := (j x)⁻¹ • x
    fderiv ℝ j x = (fderiv ℝ q y y)⁻¹ • fderiv ℝ q y := by
  dsimp only
  let j := gauge {z | q z ≤ 1}
  let y := (j x)⁻¹ • x
  have hn := convexSublevel_mem_nhds_zero hq.continuous h₀
  have hp : 0 < j x :=
    (gauge_pos (absorbent_nhds_zero hn) ((NormedSpace.isVonNBounded_iff ℝ).mpr hb)).mpr hx
  have hj : DifferentiableAt ℝ j x :=
    (contDiffAt_gauge_convexSublevel hq hc h₀ hb hx).differentiableAt (by simp)
  have hinv : HasFDerivAt (fun z => (j z)⁻¹)
      (-(j x ^ 2)⁻¹ • fderiv ℝ j x) x := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hp.ne').comp_hasFDerivAt x hj.hasFDerivAt
  have hnorm := hinv.fun_smul (hasFDerivAt_id x)
  have hcomp := (hq.differentiable (by simp) y).hasFDerivAt.comp x
    (f := fun z => (j z)⁻¹ • id z) hnorm
  have heq : (fun z => q ((j z)⁻¹ • z)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
    exact apply_inv_gauge_smul_eq_one hq.continuous hc h₀ hb hz
  have hzero := hcomp.fderiv.symm.trans (heq.fderiv_eq (𝕜 := ℝ))
  have hy : q y = 1 := apply_inv_gauge_smul_eq_one hq.continuous hc h₀ hb hx
  have hdy : 0 < fderiv ℝ q y y :=
    fderiv_self_pos_of_convex_level hc h₀ (hq.differentiable (by simp) y) hy
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hzero
  change fderiv ℝ j x v = (fderiv ℝ q y y)⁻¹ * fderiv ℝ q y v
  have hyy : fderiv ℝ q y y = (j x)⁻¹ * fderiv ℝ q y x := by simp [y]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    smul_eq_mul, id_eq, fderiv_const_apply, zero_apply] at hv
  rw [← div_eq_inv_mul, eq_div_iff hdy.ne', hyy]
  field_simp [hp.ne'] at hv ⊢
  nlinarith

/-- Squaring the nonnegative convex gauge gives a convex function. -/
theorem convexOn_gauge_sq {s : Set E} (hs : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    ConvexOn ℝ univ (fun x => gauge s x ^ 2) := by
  exact (convexOn_gauge_of_convex hs h₀).pow (fun _ _ => gauge_nonneg _) 2

/-- The smooth squared gauge has degree two under positive dilations. -/
theorem gauge_sq_smul {s : Set E} {a : ℝ} (ha : 0 ≤ a) (x : E) :
    gauge s (a • x) ^ 2 = a ^ 2 * gauge s x ^ 2 := by
  rw [gauge_smul_of_nonneg ha, smul_eq_mul, mul_pow]

/-- Squaring the gauge also preserves the direction of the defining
differential by a strictly positive factor. -/
theorem fderiv_gauge_sq_positive_multiple [CompleteSpace E] {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ConvexOn ℝ univ q) (h₀ : q 0 < 1)
    (hb : Bornology.IsBounded {x | q x ≤ 1}) {x : E} (hx : x ≠ 0) :
    let j := gauge {z | q z ≤ 1}
    let y := (j x)⁻¹ • x
    ∃ c : ℝ, 0 < c ∧ fderiv ℝ (fun z => j z ^ 2) x = c • fderiv ℝ q y := by
  dsimp only
  let j := gauge {z | q z ≤ 1}
  let y := (j x)⁻¹ • x
  have hn := convexSublevel_mem_nhds_zero hq.continuous h₀
  have hp : 0 < j x :=
    (gauge_pos (absorbent_nhds_zero hn) ((NormedSpace.isVonNBounded_iff ℝ).mpr hb)).mpr hx
  have hy : q y = 1 := apply_inv_gauge_smul_eq_one hq.continuous hc h₀ hb hx
  have hdy : 0 < fderiv ℝ q y y :=
    fderiv_self_pos_of_convex_level hc h₀ (hq.differentiable (by simp) y) hy
  refine ⟨2 * j x * (fderiv ℝ q y y)⁻¹, by positivity, ?_⟩
  have hj := (contDiffAt_gauge_convexSublevel hq hc h₀ hb hx).differentiableAt (by simp)
  have hd := (hasDerivAt_pow 2 (j x)).comp_hasFDerivAt x hj.hasFDerivAt
  have hd' : fderiv ℝ (fun z => j z ^ 2) x = (2 * j x) • fderiv ℝ j x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using hd.fderiv
  change fderiv ℝ (fun z => j z ^ 2) x = _
  rw [hd', fderiv_gauge_convexSublevel hq hc h₀ hb hx, smul_smul]

end FsFltz
