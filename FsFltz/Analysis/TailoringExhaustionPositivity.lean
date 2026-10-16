import FsFltz.Analysis.TailoringExhaustionNative
import FsFltz.Analysis.TailoringNormalizedMargin

/-!
# Outwardness on each fixed finite tailoring band

Source: `geometric-part-fsf-proof.tex`, `subsec:finite`, lines 1182–1197.
The native numerator error and normalized holomorphic margin are absorbed
on a finite band. The threshold is independent of every later `K ≥ 0`.
This module does not assert ambient convexity at all radii for fixed `β`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ComplexConjugate ContDiff Manifold Topology

variable {n : ℕ}

/-- The source decay needed for finite-band absorption. -/
theorem tendsto_beta_mul_exp_neg_sqrt :
    Tendsto (fun β : ℝ => β * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  simp only [Function.comp_apply, Real.sq_sqrt hβ]

/-- The actual native numerator is positive, and the actual updated
Liouville field is outward on any fixed finite homogeneous radial band.
All analytic constants and the threshold precede the arbitrary later `K`.
The homogeneous end and both Hessian bounds concern the supplied potential. -/
theorem tailoringFamily_exists_uniform_finite_band_outwardness
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    {d D : ℝ} (hd : 0 < d) (_hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ x : TangentCoordinates n,
      let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
      d * β ≤ Real.sqrt (metricRadialSq H x.1) →
      Real.sqrt (metricRadialSq H x.1) ≤ D * β →
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
      0 < potentialExhaustionNumerator φ (tailoringFamily I β s) (lgCover x) hnd ∧
      ∀ K : ℝ, 0 ≤ K →
        0 < (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
          ((lgManifold n).liouvilleVector
            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
              (tailoringFamily I β s) K) (lgCover x)) := by
  obtain ⟨C, hC, herror⟩ :=
    tailoringFamily_exists_uniform_native_exhaustionNumerator_error I hφ hc hlower
  obtain ⟨q, hq, L, hL, hmargin⟩ := tailoringNormalizedInput_uniform_metric_margin I hc hU
  obtain ⟨_a, _ha, _R, _hR, Bπ, _hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  have hlim : Tendsto (fun β : ℝ => C * D * β * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using
      (tendsto_const_nhds.mul tendsto_beta_mul_exp_neg_sqrt :
        Tendsto (fun β : ℝ => (C * D) * (β * Real.exp (-Real.sqrt β))) atTop (𝓝 ((C * D) * 0)))
  obtain ⟨Be, heps⟩ := eventually_atTop.mp (hlim.eventually_lt_const
    (show (0 : ℝ) < q / 2 by positivity))
  let A := max 1 (max L (REnd + 1))
  let B := Real.sqrt U * A / d
  let β₀ := max 1 (max Bπ (max Be B))
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  refine ⟨β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ s hs x
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  dsimp only
  intro hlo hhi hnd
  have hβ₁ : 1 ≤ β := (le_max_left 1 _).trans hβ
  have hβπ : Bπ ≤ β := (le_max_left Bπ _).trans ((le_max_right 1 _).trans hβ)
  have hβe : Be ≤ β := (le_max_left Be B).trans
    ((le_max_right Bπ _).trans ((le_max_right 1 _).trans hβ))
  have hβB : B ≤ β := (le_max_right Be B).trans
    ((le_max_right Bπ _).trans ((le_max_right 1 _).trans hβ))
  let ρ := ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖
  let r := Real.sqrt (metricRadialSq H x.1)
  let M := Real.exp (supportHeight I x.1 - β)
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hn : ρ ^ 2 = realSquaredNorm x.1 := by
    simp [ρ, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hupper' : metricRadialSq H x.1 ≤ U * ρ ^ 2 := hupper _ _
  have hradUpper : r ≤ Real.sqrt U * ρ := by
    have h := Real.sqrt_le_sqrt hupper'
    simpa only [Real.sqrt_mul hU.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hρ] using h
  have hAρ : A ≤ ρ := by
    have h := (div_le_iff₀ hd).mp hβB
    have hbound : Real.sqrt U * A ≤ Real.sqrt U * ρ := by
      have hstep : Real.sqrt U * A ≤ d * β := by simpa only [mul_comm] using h
      exact hstep.trans (hlo.trans hradUpper)
    exact le_of_mul_le_mul_left hbound hsU
  have hρ₁ : 1 ≤ ρ := (le_max_left _ _).trans hAρ
  have hρL : L ≤ ρ := (le_max_left _ _).trans ((le_max_right _ _).trans hAρ)
  have hρEnd : REnd < ρ := by
    have h : REnd + 1 ≤ ρ := (le_max_right _ _).trans ((le_max_right _ _).trans hAρ)
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end hφ hEnd hhom hREnd heq hρEnd
  have hmetric : 0 < metricRadialSq H x.1 :=
    (mul_pos hc (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ₁))).trans_le (hlower _ _)
  have hr : 0 < r := Real.sqrt_pos.mpr hmetric
  have hM : 0 < M := Real.exp_pos _
  have hsymm : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
    inner_fderiv_gradient_symmetric (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
  have hmargin' := (hmargin β (lgCover x) (by
    simpa only [lgCover, ← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg hρ] using hρL)
    H hsymm (hlower _) (hupper _)).2
  have herr := herror β s hs x hρ₁ hEuler hnd
  dsimp only at herr
  have hsmall : C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 * M ^ 2 ≤
      q / 2 * r * M ^ 2 := by
    calc
      _ = (C * Real.exp (-Real.sqrt β) * r) * r * M ^ 2 := by
        have hrs : r ^ 2 = metricRadialSq H x.1 := Real.sq_sqrt hmetric.le
        linear_combination -C * Real.exp (-Real.sqrt β) * M ^ 2 * hrs
      _ ≤ (C * D * β * Real.exp (-Real.sqrt β)) * r * M ^ 2 := by
        have he : C * Real.exp (-Real.sqrt β) * r ≤ C * D * β * Real.exp (-Real.sqrt β) := by
          calc
            _ ≤ C * Real.exp (-Real.sqrt β) * (D * β) := by gcongr
            _ = _ := by ring
        gcongr
      _ ≤ q / 2 * r * M ^ 2 := by gcongr; exact (heps β hβe).le
  have hB : q / 2 * r * M ^ 2 ≤
      potentialExhaustionNumerator φ (tailoringFamily I β s) (lgCover x) hnd := by
    rw [Real.norm_eq_abs] at herr
    have hb := (abs_le.mp herr).1
    change q * r * M ^ 2 ≤ _ at hmargin'
    linarith only [hb, hmargin', hsmall]
  have hBpos : 0 < potentialExhaustionNumerator φ (tailoringFamily I β s) (lgCover x) hnd :=
    (show 0 < q / 2 * r * M ^ 2 by positivity).trans_le hB
  refine ⟨hBpos, fun K hK => ?_⟩
  have hπnonneg := (hπ β hβπ s hs (lgCover x) hnd).1
  have hden : 0 < 1 + K * (lgManifold n).planePairing
      (lambdaPotentialForm φ) (tailoringFamily I β s) (lgCover x) hnd := by positivity
  rw [scalarDerivative_liouvilleVector_potential_eq_numerator hφ x H (fun _ => rfl) hEuler
    (contMDiff_tailoringFamily_lgManifold I β s) hnd hden.ne']
  exact div_pos (add_pos_of_pos_of_nonneg hmetric (mul_nonneg hK hBpos.le)) hden

end FsFltz
