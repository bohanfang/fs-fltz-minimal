import FsFltz.Analytic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv

/-!
# Actual smooth convex rounding profiles

This implements the profile existence used in `prop:allinitial` of
`geometric-part-fsf-proof.tex`, lines 898–908, and all conditions of
`def:rounding` in `geoemtric-part-fsf.tex`, lines 295–325. The construction
integrates the standard smooth transition instead of convolving absolute
value; it produces the same required bounds and exact tails.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace FsFltz
namespace SmoothRounding

/-- A smooth increasing cutoff, flat outside `[0, eps]`. -/
def cutoff (eps t : ℝ) : ℝ := Real.smoothTransition (t / eps)

lemma cutoff_contDiff (eps : ℝ) : ContDiff ℝ ∞ (cutoff eps) := by
  exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const eps)

lemma cutoff_continuous (eps : ℝ) : Continuous (cutoff eps) :=
  (cutoff_contDiff eps).continuous

lemma cutoff_intervalIntegrable (eps a b : ℝ) :
    IntervalIntegrable (cutoff eps) volume a b :=
  (cutoff_continuous eps).intervalIntegrable a b

lemma cutoff_nonneg (eps t : ℝ) : 0 ≤ cutoff eps t :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (eps t : ℝ) : cutoff eps t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma cutoff_zero {eps t : ℝ} (heps : 0 < eps) (ht : t ≤ 0) :
    cutoff eps t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht heps.le)

lemma cutoff_one {eps t : ℝ} (heps : 0 < eps) (ht : eps ≤ t) :
    cutoff eps t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ heps).2 (by simpa using ht))

lemma cutoff_monotone {eps : ℝ} (heps : 0 < eps) : Monotone (cutoff eps) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hxy heps.le)

/-- Primitive of the cutoff. It vanishes on the negative half-line. -/
def primitive (eps t : ℝ) : ℝ := ∫ s in 0..t, cutoff eps s

lemma primitive_hasDerivAt (eps t : ℝ) :
    HasDerivAt (primitive eps) (cutoff eps t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (cutoff_intervalIntegrable eps 0 t)
    (cutoff_continuous eps).stronglyMeasurable.stronglyMeasurableAtFilter
    (cutoff_continuous eps).continuousAt

lemma primitive_contDiff (eps : ℝ) : ContDiff ℝ ∞ (primitive eps) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (primitive_hasDerivAt eps t).differentiableAt, ?_⟩
  have hd : deriv (primitive eps) = cutoff eps := by
    funext t
    exact (primitive_hasDerivAt eps t).deriv
  rw [hd]
  exact cutoff_contDiff eps

lemma primitive_convex {eps : ℝ} (heps : 0 < eps) :
    ConvexOn ℝ univ (primitive eps) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun t => (primitive_hasDerivAt eps t).differentiableAt)
  intro x y hxy
  rw [(primitive_hasDerivAt eps x).deriv, (primitive_hasDerivAt eps y).deriv]
  exact cutoff_monotone heps hxy

lemma primitive_zero {eps t : ℝ} (heps : 0 < eps) (ht : t ≤ 0) :
    primitive eps t = 0 := by
  unfold primitive
  calc
    (∫ s in 0..t, cutoff eps s) = ∫ _ in 0..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact cutoff_zero heps hs.2
    _ = 0 := by simp

lemma primitive_nonneg {eps t : ℝ} (ht : 0 ≤ t) : 0 ≤ primitive eps t :=
  intervalIntegral.integral_nonneg ht (fun s _ => cutoff_nonneg eps s)

lemma primitive_le {eps t : ℝ} (ht : 0 ≤ t) : primitive eps t ≤ t := by
  have h := intervalIntegral.integral_mono ht (cutoff_intervalIntegrable eps 0 t)
    (continuous_const.intervalIntegrable 0 t) (fun s => cutoff_le_one eps s)
  simpa [primitive] using h

lemma primitive_tail {eps t : ℝ} (heps : 0 < eps) (ht : eps ≤ t) :
    primitive eps t = primitive eps eps + (t - eps) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (cutoff_intervalIntegrable eps 0 eps) (cutoff_intervalIntegrable eps eps t)
  have htail : (∫ s in eps..t, cutoff eps s) = t - eps := by
    calc
      (∫ s in eps..t, cutoff eps s) = ∫ _ in eps..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact cutoff_one heps hs.1
      _ = t - eps := by simp
  change primitive eps eps + (∫ s in eps..t, cutoff eps s) = primitive eps t at hadd
  rw [htail] at hadd
  exact hadd.symm

lemma primitive_gap {eps t : ℝ} (ht : t ≤ eps) :
    primitive eps eps - primitive eps t ≤ eps - t := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (cutoff_intervalIntegrable eps 0 t) (cutoff_intervalIntegrable eps t eps)
  have hle := intervalIntegral.integral_mono ht (cutoff_intervalIntegrable eps t eps)
    (continuous_const.intervalIntegrable t eps) (fun s => cutoff_le_one eps s)
  change primitive eps t + (∫ s in t..eps, cutoff eps s) = primitive eps eps at hadd
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
  linarith

/-- A smooth convex absolute-value approximation with exact tails. -/
def smoothAbs (eps t : ℝ) : ℝ :=
  primitive eps t + primitive eps (-t) + (eps - primitive eps eps)

lemma smoothAbs_even (eps t : ℝ) : smoothAbs eps (-t) = smoothAbs eps t := by
  simp only [smoothAbs, neg_neg]
  ring

lemma smoothAbs_contDiff (eps : ℝ) : ContDiff ℝ ∞ (smoothAbs eps) := by
  exact ((primitive_contDiff eps).add
    ((primitive_contDiff eps).comp contDiff_id.neg)).add contDiff_const

lemma smoothAbs_convex {eps : ℝ} (heps : 0 < eps) :
    ConvexOn ℝ univ (smoothAbs eps) := by
  have hn : ConvexOn ℝ univ (fun t : ℝ => primitive eps (-t)) := by
    simpa only [Function.comp_def, LinearMap.neg_apply, LinearMap.id_apply, preimage_univ]
      using (primitive_convex heps).comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  exact ((primitive_convex heps).add hn).add
    (convexOn_const (eps - primitive eps eps) convex_univ)

lemma smoothAbs_tail_nonneg {eps t : ℝ} (heps : 0 < eps) (ht : eps ≤ t) :
    smoothAbs eps t = t := by
  rw [smoothAbs, primitive_tail heps ht,
    primitive_zero (t := -t) heps (by linarith)]
  ring

lemma smoothAbs_lower_nonneg {eps t : ℝ} (heps : 0 < eps) (ht : 0 ≤ t) :
    t ≤ smoothAbs eps t := by
  rcases le_total t eps with h | h
  · rw [smoothAbs, primitive_zero heps (neg_nonpos.mpr ht)]
    have := primitive_gap h
    linarith
  · rw [smoothAbs_tail_nonneg heps h]

lemma smoothAbs_upper_nonneg {eps t : ℝ} (heps : 0 < eps) (ht : 0 ≤ t) :
    smoothAbs eps t ≤ t + eps := by
  rw [smoothAbs, primitive_zero heps (neg_nonpos.mpr ht)]
  have := primitive_le (eps := eps) ht
  have := primitive_nonneg (eps := eps) heps.le
  linarith

lemma smoothAbs_lower {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    |t| ≤ smoothAbs eps t := by
  rcases le_or_gt 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using smoothAbs_lower_nonneg heps ht
  · have h := smoothAbs_lower_nonneg heps (neg_nonneg.mpr ht.le)
    rw [smoothAbs_even] at h
    simpa only [abs_of_nonpos ht.le] using h

lemma smoothAbs_upper {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    smoothAbs eps t ≤ |t| + eps := by
  rcases le_or_gt 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using smoothAbs_upper_nonneg heps ht
  · have h := smoothAbs_upper_nonneg heps (neg_nonneg.mpr ht.le)
    rw [smoothAbs_even] at h
    simpa only [abs_of_nonpos ht.le] using h

lemma smoothAbs_exact {eps t : ℝ} (heps : 0 < eps) (ht : eps ≤ |t|) :
    smoothAbs eps t = |t| := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact smoothAbs_tail_nonneg heps ht
  · rw [abs_of_nonpos h.le] at ht ⊢
    rw [← smoothAbs_even eps t]
    exact smoothAbs_tail_nonneg heps ht

lemma smoothAbs_hasDerivAt (eps t : ℝ) :
    HasDerivAt (smoothAbs eps) (cutoff eps t - cutoff eps (-t)) t := by
  change HasDerivAt
    (fun x => primitive eps x + primitive eps (-x) + (eps - primitive eps eps)) _ t
  simpa only [Function.comp_def, Pi.add_apply, mul_neg_one, sub_eq_add_neg] using
    ((primitive_hasDerivAt eps t).add
    ((primitive_hasDerivAt eps (-t)).comp t (hasDerivAt_id t).neg)).add_const
      (eps - primitive eps eps)

lemma smoothAbs_deriv_bounds (eps t : ℝ) :
    -1 ≤ cutoff eps t - cutoff eps (-t) ∧ cutoff eps t - cutoff eps (-t) ≤ 1 := by
  have := cutoff_nonneg eps t
  have := cutoff_nonneg eps (-t)
  have := cutoff_le_one eps t
  have := cutoff_le_one eps (-t)
  constructor <;> linarith

/-- The resulting two-variable smooth maximum. -/
def smoothMax (eps : ℝ) (xy : ℝ × ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * (xy.1 + xy.2 + smoothAbs eps (xy.1 - xy.2))

lemma smoothMax_contDiff (eps : ℝ) : ContDiff ℝ ∞ (smoothMax eps) := by
  exact contDiff_const.mul ((contDiff_fst.add contDiff_snd).add
    ((smoothAbs_contDiff eps).comp (contDiff_fst.sub contDiff_snd)))

lemma smoothMax_convex {eps : ℝ} (heps : 0 < eps) :
    ConvexOn ℝ univ (smoothMax eps) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb _hab
  have h := (smoothAbs_convex heps).2 (mem_univ (p.1 - p.2))
    (mem_univ (q.1 - q.2)) ha hb _hab
  simp only [smul_eq_mul] at h
  change (2 : ℝ)⁻¹ * ((a • p + b • q).1 + (a • p + b • q).2 +
    smoothAbs eps ((a • p + b • q).1 - (a • p + b • q).2)) ≤
    a * ((2 : ℝ)⁻¹ * (p.1 + p.2 + smoothAbs eps (p.1 - p.2))) +
    b * ((2 : ℝ)⁻¹ * (q.1 + q.2 + smoothAbs eps (q.1 - q.2)))
  change (2 : ℝ)⁻¹ * ((a * p.1 + b * q.1) + (a * p.2 + b * q.2) +
    smoothAbs eps (a * p.1 + b * q.1 - (a * p.2 + b * q.2))) ≤
    a * ((2 : ℝ)⁻¹ * (p.1 + p.2 + smoothAbs eps (p.1 - p.2))) +
    b * ((2 : ℝ)⁻¹ * (q.1 + q.2 + smoothAbs eps (q.1 - q.2)))
  rw [show a * p.1 + b * q.1 - (a * p.2 + b * q.2) =
    a * (p.1 - p.2) + b * (q.1 - q.2) by ring]
  norm_num at ⊢
  linarith

lemma max_formula (x y : ℝ) : max x y = (2 : ℝ)⁻¹ * (x + y + |x - y|) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

lemma smoothMax_lower {eps : ℝ} (heps : 0 < eps) (xy : ℝ × ℝ) :
    max xy.1 xy.2 ≤ smoothMax eps xy := by
  have := smoothAbs_lower heps (xy.1 - xy.2)
  rw [max_formula, smoothMax]
  norm_num at ⊢
  linarith

lemma smoothMax_upper {eps : ℝ} (heps : 0 < eps) (xy : ℝ × ℝ) :
    smoothMax eps xy ≤ max xy.1 xy.2 + eps := by
  have := smoothAbs_upper heps (xy.1 - xy.2)
  rw [max_formula, smoothMax]
  norm_num at ⊢
  linarith

lemma smoothMax_exact {eps : ℝ} (heps : 0 < eps) (xy : ℝ × ℝ)
    (hxy : eps ≤ |xy.1 - xy.2|) : smoothMax eps xy = max xy.1 xy.2 := by
  rw [smoothMax, smoothAbs_exact heps hxy, max_formula]

lemma smoothMax_hasFDerivAt (eps : ℝ) (xy : ℝ × ℝ) :
    HasFDerivAt (smoothMax eps)
      ((2 : ℝ)⁻¹ • ((ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) +
        (cutoff eps (xy.1 - xy.2) - cutoff eps (-(xy.1 - xy.2))) •
          (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))) xy := by
  change HasFDerivAt (fun p : ℝ × ℝ =>
    (2 : ℝ)⁻¹ * (p.1 + p.2 + smoothAbs eps (p.1 - p.2))) _ xy
  simpa only [Function.comp_def, Pi.add_apply, Pi.sub_apply] using
    ((hasFDerivAt_fst.add hasFDerivAt_snd).add
      ((smoothAbs_hasDerivAt eps (xy.1 - xy.2)).comp_hasFDerivAt xy
        (hasFDerivAt_fst.sub hasFDerivAt_snd))).const_mul (2 : ℝ)⁻¹

lemma smoothMax_partialFirst (eps : ℝ) (xy : ℝ × ℝ) :
    fderiv ℝ (smoothMax eps) xy (1, 0) =
      (2 : ℝ)⁻¹ * (1 + (cutoff eps (xy.1 - xy.2) - cutoff eps (-(xy.1 - xy.2)))) := by
  rw [(smoothMax_hasFDerivAt eps xy).fderiv]
  simp
  ring

lemma smoothMax_partialSecond (eps : ℝ) (xy : ℝ × ℝ) :
    fderiv ℝ (smoothMax eps) xy (0, 1) =
      (2 : ℝ)⁻¹ * (1 - (cutoff eps (xy.1 - xy.2) - cutoff eps (-(xy.1 - xy.2)))) := by
  rw [(smoothMax_hasFDerivAt eps xy).fderiv]
  simp
  ring

end SmoothRounding

/-- An actual native rounding profile exists at every positive width.
Source: `prop:allinitial`, proof lines 898–908; the integrated-cutoff
construction above supplies the stated profile without further hypotheses. -/
def roundingProfile (eps : ℝ) (heps : 0 < eps) : RoundingProfile eps where
  toFun := SmoothRounding.smoothMax eps
  smooth := SmoothRounding.smoothMax_contDiff eps
  convex := SmoothRounding.smoothMax_convex heps
  partialFirst_nonneg := by
    intro xy
    rw [SmoothRounding.smoothMax_partialFirst]
    have := (SmoothRounding.smoothAbs_deriv_bounds eps (xy.1 - xy.2)).1
    exact mul_nonneg (by norm_num) (by linarith)
  partialSecond_nonneg := by
    intro xy
    rw [SmoothRounding.smoothMax_partialSecond]
    have := (SmoothRounding.smoothAbs_deriv_bounds eps (xy.1 - xy.2)).2
    exact mul_nonneg (by norm_num) (by linarith)
  partial_sum := by
    intro xy
    rw [SmoothRounding.smoothMax_partialFirst, SmoothRounding.smoothMax_partialSecond]
    ring
  lower := SmoothRounding.smoothMax_lower heps
  upper := SmoothRounding.smoothMax_upper heps
  exact_away := SmoothRounding.smoothMax_exact heps

theorem roundingProfile_nonempty {eps : ℝ} (heps : 0 < eps) :
    Nonempty (RoundingProfile eps) :=
  ⟨roundingProfile eps heps⟩

end FsFltz
