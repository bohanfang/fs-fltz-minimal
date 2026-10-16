import FsFltz.Analysis.PotentialMetricEstimates
import FsFltz.Analysis.CoefficientPathMargin

/-!
# Quantitative margins and logarithmic fiber ends in the varying potential metric

Source: `geometric-part-fsf-proof.tex`, `lem:margin`, lines 746–768,
`lem:originalends`, lines 770–795, and matching truncations, lines 1011–1049.
The inverse metric here is the inverse of the actual Hessian. Coefficient and
potential parameters vary independently; the endpoint potential is retained.
The scalar bounds are producers for the native Liouville identities, rather
than assumptions about an ambient field, a fiber marking, or a pair family.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate ContDiff

variable {n : ℕ}

/-- The source's literal homogeneous radial square `uᵀ H u`. -/
def metricRadialSq
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : RealSpace n) : ℝ :=
  inner ℝ (H (WithLp.toLp 2 u)) (WithLp.toLp 2 u)

/-- The displayed source scalar `Q_f` in the actual potential metric. -/
def potentialMetricMargin
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n) : ℝ :=
  metricRadialSq H y.1 * toricInverseMetricSq H I y - Complex.normSq (b0 I y) +
    (conj (W I y) * b0 I y).re / 2

/-- The literal intrinsic exhaustion derivative on the homogeneous end. -/
def potentialMetricFiberDefect
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n) : ℝ :=
  metricRadialSq H y.1 - Complex.normSq (b0 I y) / toricInverseMetricSq H I y

/-- The scalar quantitative step of `lem:margin` applies to any radius
and derivative length satisfying the proved metric bounds. -/
theorem ambient_margin_quantitative_of_bounds {r g h C M c D : ℝ} {b f : ℂ}
    (hr : 0 ≤ r) (hg : 0 ≤ g) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hc : 0 < c) (hD : 0 < D) (hh : 1 / 2 ≤ h)
    (hheight : h ≤ D * r) (hgrad : c * M ≤ g)
    (hradius : 2 * C ≤ c * r) (hb : ‖b‖ ≤ r * g)
    (hdef : ‖b - (h : ℂ) * f‖ ≤ C * M) :
    c ^ 2 / (4 * D) * r * M ^ 2 ≤
      r ^ 2 * g ^ 2 - Complex.normSq b + (conj f * b).re / 2 := by
  have hq : 0 ≤ c ^ 2 / (4 * D) := div_nonneg (sq_nonneg _) (by positivity)
  have hrg : 0 ≤ r * g := mul_nonneg hr hg
  have hcg : r * (c * M) ≤ r * g := mul_le_mul_of_nonneg_left hgrad hr
  have hdefsmall : C * M ≤ r * g / 2 := by
    have hcM := mul_le_mul_of_nonneg_right hradius hM
    nlinarith only [hcM, hcg]
  have hnumer : (r * g) ^ 2 / 2 ≤ r * g * (r * g - C * M) := by
    have hm := mul_le_mul_of_nonneg_left hdefsmall hrg
    nlinarith only [hm]
  have hcgSq : (r * (c * M)) ^ 2 ≤ (r * g) ^ 2 := by
    have hleft : 0 ≤ r * (c * M) := mul_nonneg hr (mul_nonneg hc.le hM)
    nlinarith only [hleft, hcg]
  have hden : 0 < 2 * h := by linarith
  have hbound : c ^ 2 / (4 * D) * r * M ^ 2 ≤
      r * g * (r * g - C * M) / (2 * h) := by
    apply (le_div_iff₀ hden).mpr
    calc
      c ^ 2 / (4 * D) * r * M ^ 2 * (2 * h) ≤
          c ^ 2 / (4 * D) * r * M ^ 2 * (2 * (D * r)) :=
        mul_le_mul_of_nonneg_left (by linarith [hheight])
          (mul_nonneg (mul_nonneg hq hr) (sq_nonneg _))
      _ = (r * (c * M)) ^ 2 / 2 := by field_simp; ring
      _ ≤ (r * g) ^ 2 / 2 := div_le_div_of_nonneg_right hcgSq (by norm_num)
      _ ≤ r * g * (r * g - C * M) := hnumer
  exact hbound.trans (quadratic_ambient_margin hh hC hM hb hdef)

/-- The common lower and upper Hessian bounds compare the source radius
to the fixed Euclidean radius. -/
theorem metricRadialSq_radius_bounds
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v)
    (hupper : ∀ v, inner ℝ (H v) v ≤ C * ‖v‖ ^ 2) (u : RealSpace n) :
    Real.sqrt c * Real.sqrt (realSquaredNorm u) ≤ Real.sqrt (metricRadialSq H u) ∧
      Real.sqrt (metricRadialSq H u) ≤ Real.sqrt C * Real.sqrt (realSquaredNorm u) := by
  have hn : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ ^ 2 = realSquaredNorm u := by
    simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hl := hlower (WithLp.toLp 2 u)
  have hu := hupper (WithLp.toLp 2 u)
  rw [hn] at hl hu
  exact ⟨by simpa only [Real.sqrt_mul hc.le, metricRadialSq] using Real.sqrt_le_sqrt hl,
    by simpa only [Real.sqrt_mul hC.le, metricRadialSq] using Real.sqrt_le_sqrt hu⟩

/-- Independent coefficient and metric choices admit one positive common
ambient margin. Every metric is required to satisfy the same Hessian bounds;
these bounds will be supplied by the actual chosen potential path. -/
theorem ToricInput.coefficientPath_metric_quantitative_ambient_margin
    (I : ToricInput n) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ q : ℝ, 0 < q ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
      ∀ H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x z, inner ℝ (H x) z = inner ℝ x (H z)) →
        (∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) →
        (∀ v, inner ℝ (H v) v ≤ C * ‖v‖ ^ 2) →
        0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
          q * Real.sqrt (metricRadialSq H y.1) *
            maxMonomialMagnitude (I.alongCoefficientPath t) y ^ 2 ≤
              potentialMetricMargin H (I.alongCoefficientPath t) y := by
  obtain ⟨d, hd, L, hL, hgrad⟩ := I.coefficientPath_inverseMetric_dominant_lowerBound hC
  obtain ⟨B, hB, hdef⟩ := I.coefficientPath_b0_sub_supportHeight_mul_W_bound
  obtain ⟨m, hm, D, hD, hheight⟩ := I.exists_supportHeight_linear_bounds
  let k := Real.sqrt c
  have hk : 0 < k := Real.sqrt_pos.mpr hc
  let T := max L (max (1 / (2 * m)) (2 * B / (d * k))) + 1
  have hT : 0 < T := hL.trans_le ((le_max_left _ _).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  refine ⟨d ^ 2 / (4 * (D / k)), div_pos (sq_pos_of_pos hd) (by positivity), T, hT, ?_⟩
  intro t ht y hy H hsymm hlower hupper
  let J := I.alongCoefficientPath t
  let r := Real.sqrt (metricRadialSq H y.1)
  let ρ := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (toricInverseMetricSq H J y)
  have hpos : ∀ v, 0 ≤ inner ℝ (H v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower v)
  have hrad := (metricRadialSq_radius_bounds H hc hC hlower hupper y.1).1
  have hmax : max L (max (1 / (2 * m)) (2 * B / (d * k))) ≤ ρ :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans hy
  have hLrad : L ≤ ρ := (le_max_left _ _).trans hmax
  have hmrad : 1 / (2 * m) ≤ ρ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hBrad : 2 * B / (d * k) ≤ ρ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmax)
  have hgrad' : d * maxMonomialMagnitude J y ≤ g :=
    hgrad t ht y hLrad H hsymm hpos hupper
  have ha : 0 < toricInverseMetricSq H J y := Real.sqrt_pos.mp
    ((mul_pos hd (J.maxMonomialMagnitude_pos y)).trans_le hgrad')
  have hh : 1 / 2 ≤ supportHeight J y.1 := by
    rw [supportHeight_alongCoefficientPath]
    have hh' := (div_le_iff₀ (show 0 < 2 * m by positivity)).mp hmrad
    nlinarith [(hheight y.1).1]
  have hheight' : supportHeight J y.1 ≤ D / k * r := by
    rw [supportHeight_alongCoefficientPath]
    have hρ : ρ ≤ r / k := (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hrad)
    exact (hheight y.1).2.trans (by
      simpa only [div_mul_eq_mul_div, mul_div_assoc, ρ] using
        mul_le_mul_of_nonneg_left hρ hD.le)
  have hradius : 2 * B ≤ d * r := by
    have h := (div_le_iff₀ (mul_pos hd hk)).mp hBrad
    have h' := mul_le_mul_of_nonneg_left hrad hd.le
    nlinarith only [h, h']
  have hmetric : 0 ≤ metricRadialSq H y.1 := hpos (WithLp.toLp 2 y.1)
  have hinverse : 0 ≤ toricInverseMetricSq H J y := ha.le
  have hbound := ambient_margin_quantitative_of_bounds
    (Real.sqrt_nonneg (metricRadialSq H y.1)) (Real.sqrt_nonneg (toricInverseMetricSq H J y))
    (J.maxMonomialMagnitude_pos y).le hB.le hd (div_pos hD hk) hh hheight' hgrad' hradius
    (norm_b0_le_metric_radius_mul_sqrt_toricInverseMetricSq H hsymm hpos J y)
    (hdef t ht y)
  refine ⟨ha, ?_⟩
  simpa only [Real.sq_sqrt hmetric, Real.sq_sqrt hinverse, potentialMetricMargin] using hbound

/-- The actual Hessian equivalence of the prescribed affine path from the
quadratic potential to a fixed chosen endpoint. Its inverse is constructed
from the endpoint lower bound, rather than supplied as separate data. -/
def potentialPathHessianEquiv {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  potentialHessianEquiv (lt_min zero_lt_one hc)
    (hessian_potentialPath_lowerBound
      ((contDiff_id.norm_sq ℝ).div_const 2) hφ
      (fun x v => by simp [hessian_half_norm_sq]) hlower hs) x

@[simp]
theorem potentialPathHessianEquiv_apply
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x v : EuclideanSpace ℝ (Fin n)) :
    potentialPathHessianEquiv hφ hc hlower s hs x v =
      (fderiv ℝ (gradient (potentialPath (fun z => ‖z‖ ^ 2 / 2) φ s)) x) v := rfl

/-- Symmetry and both common Hessian bounds for the actual path metric,
with the fixed chosen endpoint retained. -/
theorem potentialPathHessianEquiv_bounds
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin n)) :
    (∀ u v, inner ℝ (potentialPathHessianEquiv hφ hc hlower s hs x u) v =
      inner ℝ u (potentialPathHessianEquiv hφ hc hlower s hs x v)) ∧
    (∀ v, min 1 c * ‖v‖ ^ 2 ≤
      inner ℝ (potentialPathHessianEquiv hφ hc hlower s hs x v) v) ∧
    (∀ v, inner ℝ (potentialPathHessianEquiv hφ hc hlower s hs x v) v ≤
      max 1 C * ‖v‖ ^ 2) := by
  have hq : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 / 2) :=
    (contDiff_id.norm_sq ℝ).div_const 2
  refine ⟨inner_fderiv_gradient_symmetric (potentialPath_contDiff_space hq hφ s) x,
    hessian_potentialPath_lowerBound hq hφ (fun x v => by simp [hessian_half_norm_sq]) hlower hs x,
    hessian_potentialPath_upperBound hq hφ (fun x v => by simp [hessian_half_norm_sq]) hupper hs x⟩

/-- The quantitative ambient margin for the actual chosen potential path.
The coefficient parameter `t` and the potential parameter `s` are independent.
No replacement endpoint is selected inside this theorem. -/
theorem ToricInput.coefficientPath_potentialPath_quantitative_ambient_margin
    (I : ToricInput n) {φ : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hupper : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2) :
    ∃ q : ℝ, 0 < q ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
        L ≤ Real.sqrt (realSquaredNorm y.1) →
        let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 y.1)
        0 < toricInverseMetricSq H (I.alongCoefficientPath t) y ∧
          q * Real.sqrt (metricRadialSq H y.1) *
            maxMonomialMagnitude (I.alongCoefficientPath t) y ^ 2 ≤
              potentialMetricMargin H (I.alongCoefficientPath t) y := by
  obtain ⟨q, hq, L, hL, hmargin⟩ := I.coefficientPath_metric_quantitative_ambient_margin
    (lt_min zero_lt_one hc) (zero_lt_one.trans_le (le_max_left (1 : ℝ) C))
  refine ⟨q, hq, L, hL, ?_⟩
  intro t ht s hs y hy
  obtain ⟨hsymm, hl, hu⟩ := potentialPathHessianEquiv_bounds hφ hc hlower hupper s hs
    (WithLp.toLp 2 y.1)
  exact hmargin t ht y hy _ hsymm hl hu

end FsFltz
