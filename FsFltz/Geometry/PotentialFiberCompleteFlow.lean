import FsFltz.Geometry.PotentialFiberLiouville
import FsFltz.Analysis.OriginalFiberCompleteFlow
import FsFltz.Analysis.CoefficientPathRegularity

/-!
# Complete intrinsic flows of holomorphic potential fibers

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 770–818.
Weighted Cauchy–Schwarz bounds the actual intrinsic exhaustion derivative
on the homogeneous end. Closedness of the literal full fiber, quadratic
growth of the end potential, and compactness of the remainder give a
proper shifted exhaustion with a global derivative bound. The native ODE
theorem then constructs the intrinsic flow in both time directions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

/-- Weighted Cauchy–Schwarz bounds the literal metric fiber defect throughout
every regular holomorphic level, independently of the coefficient magnitudes. -/
theorem potentialMetricFiberDefect_bounds
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v))
    (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) (I : ToricInput n) (y : LGSpace n)
    (ha : 0 < toricInverseMetricSq H I y) :
    0 ≤ potentialMetricFiberDefect H I y ∧
      potentialMetricFiberDefect H I y ≤ metricRadialSq H y.1 := by
  have hb := norm_b0_le_metric_radius_mul_sqrt_toricInverseMetricSq H hsymm hpos I y
  change ‖b0 I y‖ ≤ Real.sqrt (metricRadialSq H y.1) *
    Real.sqrt (toricInverseMetricSq H I y) at hb
  have hr : 0 ≤ metricRadialSq H y.1 := hpos _
  have hprod := mul_nonneg (Real.sqrt_nonneg (metricRadialSq H y.1))
    (Real.sqrt_nonneg (toricInverseMetricSq H I y))
  have hsq : Complex.normSq (b0 I y) ≤ metricRadialSq H y.1 * toricInverseMetricSq H I y := by
    rw [Complex.normSq_eq_norm_sq]
    have heq : (Real.sqrt (metricRadialSq H y.1) * Real.sqrt (toricInverseMetricSq H I y)) ^ 2 =
        metricRadialSq H y.1 * toricInverseMetricSq H I y := by
      rw [mul_pow, Real.sq_sqrt hr, Real.sq_sqrt ha.le]
    nlinarith [norm_nonneg (b0 I y)]
  have hquot : 0 ≤ Complex.normSq (b0 I y) / toricInverseMetricSq H I y :=
    div_nonneg (Complex.normSq_nonneg _) ha.le
  exact ⟨sub_nonneg.mpr ((div_le_iff₀ ha).mpr hsq), sub_le_self _ hquot⟩

section End

variable {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)

include hEnd1 hEnds hhom hc hlower hL hend

/-- On the actual common homogeneous end the native Hessian radial square
is twice the actual potential value. -/
theorem metricRadialSq_potential_eq_two_mul (u : RealSpace n)
    (hu : L < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖) :
    metricRadialSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 u)) u = 2 * φ u := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  exact inner_hessian_self_eq_two_mul_on_homogeneous_end
    (hEnd1.comp e.contDiff)
    (fun x hx => (hEnds (e x) (by simpa [e] using hx)).comp x e.contDiff.contDiffAt)
    (fun r hr x => by simpa only [Function.comp_apply, map_smul] using hhom r hr (e x))
    hL (fun x hx => by simpa [e] using hend (e x) hx) hu

/-- Positive Hessian and homogeneity supply a quantitative quadratic lower
bound for the actual potential on its end. -/
theorem potential_quadratic_lower_on_end (u : RealSpace n)
    (hu : L < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖) :
    c * realSquaredNorm u ≤ 2 * φ u := by
  have h := hlower (WithLp.toLp 2 u) (WithLp.toLp 2 u)
  have he := metricRadialSq_potential_eq_two_mul hEnd1 hEnds hhom hc hlower hL hend u hu
  change c * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
    metricRadialSq (potentialHessianEquiv hc hlower (WithLp.toLp 2 u)) u at h
  rw [he] at h
  simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using h

include hφ

/-- Every actual potential sublevel is compact in the quotient ambient.
The end lower bound contains it in a compact quadratic cylinder. -/
theorem isCompact_potential_sublevel (A : ℝ) :
    IsCompact {y : LGSpace n | φ y.1 ≤ A} := by
  have hB : 0 ≤ max (L ^ 2 / 2) (A / c) :=
    (div_nonneg (sq_nonneg _) (by norm_num)).trans (le_max_left _ _)
  apply IsCompact.of_isClosed_subset (isCompact_phi0_sublevel (n := n) _ hB)
    (isClosed_le (hφ.continuous.comp continuous_fst) continuous_const)
  intro y hy
  change φ y.1 ≤ A at hy
  change phi0 y ≤ max (L ^ 2 / 2) (A / c)
  by_cases hout : L < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖
  · have hl := potential_quadratic_lower_on_end hEnd1 hEnds hhom hc hlower hL hend y.1 hout
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hc).mpr
    dsimp [phi0]
    nlinarith
  · apply le_trans _ (le_max_left _ _)
    have hr : ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ ≤ L := le_of_not_gt hout
    have hsq : realSquaredNorm y.1 ≤ L ^ 2 := by
      simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using (sq_le_sq₀ (norm_nonneg _) hL.le).mpr hr
    dsimp [phi0]
    linarith

/-- A single nonnegative shift makes the potential nonnegative everywhere.
It is obtained from the compact ball and the proved nonnegative end. -/
theorem exists_nonnegative_potential_shift :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u, 0 ≤ φ u + D := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) L).exists_bound_of_continuousOn (hφ.comp e.contDiff).continuous.continuousOn
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro u
  by_cases hout : L < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖
  · have hl := potential_quadratic_lower_on_end hEnd1 hEnds hhom hc hlower hL hend u hout
    have hnonneg := mul_nonneg hc.le (realSquaredNorm_nonneg u)
    linarith [le_max_right D 0]
  · have hbound := hD (e.symm u) (by
      simpa [e, Metric.mem_closedBall, dist_zero_right] using le_of_not_gt hout)
    have hlow : -D ≤ φ u := by
      simp only [Function.comp_apply, e.apply_symm_apply] at hbound
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound)).1
    linarith [le_max_left D 0]

end End

end FsFltz.Geometry
