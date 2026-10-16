import FsFltz.Analysis.TailoringIntrinsicExhaustionEstimates
import FsFltz.Analysis.TailoringAlmostTangent

/-!
# Native exhaustion on the entire bounded-value tailored end

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`,
`eq:almosttangent` and `eq:fiberends`, lines 1198–1220.
One threshold controls every larger radius of the actual nonholomorphic
family. The field is the symplectic projection of the base potential field;
this is not a global convexity assertion for the tailored ambient primitive.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped ContDiff Manifold Topology

variable {n : ℕ}

private theorem potentialMetricFiberDefect_lower_of_half_ratio
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (I : ToricInput n) (y : LGSpace n)
    (hr : 0 < metricRadialSq H y.1) (ha : 0 < toricInverseMetricSq H I y)
    (hb : ‖b0 I y‖ / (Real.sqrt (metricRadialSq H y.1) *
      Real.sqrt (toricInverseMetricSq H I y)) ≤ 1 / 2) :
    3 / 4 * metricRadialSq H y.1 ≤ potentialMetricFiberDefect H I y := by
  have hprod : 0 < Real.sqrt (metricRadialSq H y.1) *
      Real.sqrt (toricInverseMetricSq H I y) :=
    mul_pos (Real.sqrt_pos.mpr hr) (Real.sqrt_pos.mpr ha)
  have hn := (div_le_iff₀ hprod).mp hb
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  rw [← Complex.normSq_eq_norm_sq, mul_pow, mul_pow,
    Real.sq_sqrt hr.le, Real.sq_sqrt ha.le] at hsq
  have hquot : Complex.normSq (b0 I y) / toricInverseMetricSq H I y ≤
      metricRadialSq H y.1 / 4 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hsq]
  dsimp [potentialMetricFiberDefect]
  linarith only [hquot]

/-- A single logarithmic threshold gives native projected outwardness and
linear coordinate growth on the entire bounded-value tailored end.
All radii above the threshold are included; there is no upper radial cutoff. -/
theorem tailoringFamily_exists_uniform_whole_end_exhaustion_data
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ x : TangentCoordinates n,
        let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
        F * β ≤ Real.sqrt (metricRadialSq H x.1) →
        ‖tailoringFamily I β s (lgCover x)‖ ≤ 2 →
        ∀ hnd : (lgManifold n).Nondegenerate
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
        0 < toricInverseMetricSq H (tailoringNormalizedInput I β) (lgCover x) ∧
        3 / 4 * metricRadialSq H x.1 ≤
          potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x) ∧
        0 < (lgManifold n).planePairing (lambdaPotentialForm φ)
          (tailoringFamily I β s) (lgCover x) hnd ∧
        metricRadialSq H x.1 / 2 ≤
          potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd ∧
        ‖coverFiberProjection H
          (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x) (x.1, 0)‖ ≤
            C * Real.sqrt (metricRadialSq H x.1) := by
  obtain ⟨C, hC, R, hR, Bp, _hBp, herror⟩ :=
    tailoringFamily_exists_uniform_projected_exhaustion_error I hφ hc hU hlower hupper
  obtain ⟨T, hT, L, hL, htangent⟩ :=
    tailoringFamily_exists_uniform_metric_almostTangent I hc hU
  obtain ⟨dπ, hdπ, Rπ, _hRπ, Bπ, _hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨a, ha, _b, _hb, hheight⟩ := I.exists_supportHeight_linear_bounds
  let d := a / Real.sqrt U
  have hd : 0 < d := div_pos ha (Real.sqrt_pos.mpr hU)
  let F := max 1 (2 / d)
  have hF : 0 < F := zero_lt_one.trans_le (le_max_left _ _)
  have hFd : 2 ≤ d * F := by
    have h := (div_le_iff₀ hd).mp (le_max_right (1 : ℝ) (2 / d))
    simpa only [F, mul_comm] using h
  have htail : Tendsto (fun β : ℝ => T *
      (Real.exp (-β) + Real.exp (-Real.sqrt β) + β⁻¹)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((Real.tendsto_exp_neg_atTop_nhds_zero.add
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)).add
          tendsto_inv_atTop_zero)
  obtain ⟨Bt, hsmall⟩ := eventually_atTop.mp (htail.eventually_lt_const
    (show (0 : ℝ) < 1 / 2 by norm_num))
  have heps : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, hepssmall⟩ := eventually_atTop.mp (heps.eventually_lt_const
    (show (0 : ℝ) < 1 / 4 by norm_num))
  let A := max 1 (max R (max L (max Rπ (REnd + 1))))
  let Bg := Real.sqrt U * A / F
  let β₀ := max 1 (max Bp (max Bπ (max Bt (max Be Bg))))
  refine ⟨F, hF, C, hC, β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs x
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  dsimp only
  intro hx hfs hnd
  dsimp [β₀] at hβ
  simp only [max_le_iff] at hβ
  rcases hβ with ⟨hβ₁, hβp, hβπ, hβt, hβe, hβg⟩
  have hβpos : 0 < β := zero_lt_one.trans_le hβ₁
  let ρ := Real.sqrt (realSquaredNorm x.1)
  let r := Real.sqrt (metricRadialSq H x.1)
  let M := Real.exp (supportHeight I x.1 - β)
  have hr : 0 < r := (mul_pos hF hβpos).trans_le hx
  have hmetric : 0 < metricRadialSq H x.1 := Real.sqrt_pos.mp hr
  have hradup := (metricRadialSq_radius_bounds H hc hU (hlower _) (hupper _) x.1).2
  have hAρ : A ≤ ρ := by
    have hBg := (div_le_iff₀ hF).mp hβg
    have hBg' : Real.sqrt U * A ≤ F * β := by simpa only [mul_comm] using hBg
    have hbound : Real.sqrt U * A ≤ Real.sqrt U * ρ :=
      hBg'.trans (hx.trans hradup)
    exact le_of_mul_le_mul_left hbound (Real.sqrt_pos.mpr hU)
  have hρR : R ≤ ρ := (le_max_left _ _).trans ((le_max_right _ _).trans hAρ)
  have hρL : L ≤ ρ := (le_max_left _ _).trans
    ((le_max_right R _).trans ((le_max_right 1 _).trans hAρ))
  have hρπ : Rπ ≤ ρ := (le_max_left _ _).trans
    ((le_max_right L _).trans ((le_max_right R _).trans ((le_max_right 1 _).trans hAρ)))
  have hρEnd : REnd < ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
    have hbound : REnd + 1 ≤ ρ := (le_max_right _ _).trans
      ((le_max_right L _).trans ((le_max_right R _).trans ((le_max_right 1 _).trans hAρ)))
    have hnorm : ρ = ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
      rw [EuclideanSpace.norm_eq]
      simp [ρ, realSquaredNorm, Real.norm_eq_abs, sq_abs]
    rw [hnorm] at hbound
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end hφ hEnd hhom hREnd heq hρEnd
  have hsymm : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
    inner_fderiv_gradient_symmetric (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
  have hheightmetric : d * r ≤ supportHeight I x.1 := by
    have hρ : r / Real.sqrt U ≤ ρ :=
      (div_le_iff₀ (Real.sqrt_pos.mpr hU)).mpr (by simpa only [mul_comm] using hradup)
    have h := mul_le_mul_of_nonneg_left hρ ha.le
    have h' : d * r ≤ a * ρ := by
      simpa only [d, div_mul_eq_mul_div, mul_div_assoc] using h
    exact h'.trans (hheight x.1).1
  have htwobeta : 2 * β ≤ supportHeight I x.1 := by
    have h1 := mul_le_mul_of_nonneg_right hFd hβpos.le
    have h2 := mul_le_mul_of_nonneg_left hx hd.le
    exact (h1.trans (by simpa only [mul_assoc] using h2)).trans hheightmetric
  have hMinv : M⁻¹ ≤ Real.exp (-β) := by
    dsimp [M]
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith only [htwobeta])
  have hβr : β ≤ r := by
    have h := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 / d)) hβpos.le
    have h' : β ≤ F * β := by simpa only [one_mul] using h
    exact h'.trans hx
  have hrinv : r⁻¹ ≤ β⁻¹ := (inv_le_inv₀ hr hβpos).mpr hβr
  obtain ⟨ha₀, ht⟩ := htangent β s hs (lgCover x) hρL hfs H hsymm (hlower _) (hupper _)
  change ‖b0 (tailoringNormalizedInput I β) (lgCover x)‖ /
    (r * Real.sqrt (toricInverseMetricSq H (tailoringNormalizedInput I β) (lgCover x))) ≤
      T * (M⁻¹ + Real.exp (-Real.sqrt β) + r⁻¹) at ht
  have hratio : ‖b0 (tailoringNormalizedInput I β) (lgCover x)‖ /
      (r * Real.sqrt (toricInverseMetricSq H (tailoringNormalizedInput I β) (lgCover x))) ≤
      1 / 2 := by
    apply ht.trans
    calc
      _ ≤ T * (Real.exp (-β) + Real.exp (-Real.sqrt β) + β⁻¹) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hMinv le_rfl) hrinv) hT.le
      _ ≤ 1 / 2 := (hsmall β hβt).le
  have hdefect := potentialMetricFiberDefect_lower_of_half_ratio H
    (tailoringNormalizedInput I β) (lgCover x) hmetric ha₀ hratio
  change 3 / 4 * metricRadialSq H x.1 ≤
    potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x) at hdefect
  obtain ⟨herr, hnorm⟩ := herror β hβp s hs x hρR hEuler hnd
  change ‖potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd -
    potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x)‖ ≤
      C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 at herr
  have herrsmall : C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 ≤
      metricRadialSq H x.1 / 4 := by
    have h := mul_le_mul_of_nonneg_right (hepssmall β hβe).le hmetric.le
    linarith only [h]
  have hlow : metricRadialSq H x.1 / 2 ≤
      potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd := by
    rw [Real.norm_eq_abs] at herr
    have hb := (abs_le.mp herr).1
    linarith only [hb, hdefect, herrsmall]
  have hπend := (hπ β hβπ s hs (lgCover x) hnd).2.1 hρπ
  exact ⟨ha₀, hdefect,
    (show 0 < dπ * M ^ 2 / 2 by dsimp [M]; positivity).trans_le hπend,
    hlow, hnorm⟩

/-- One logarithmic threshold gives the source's actual native projected
exhaustion inequality and linear field bound throughout the whole end. -/
theorem tailoringFamily_exists_uniform_whole_end_projected_exhaustion
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ x : TangentCoordinates n,
        let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
        F * β ≤ Real.sqrt (metricRadialSq H x.1) →
        ‖tailoringFamily I β s (lgCover x)‖ ≤ 2 →
        ∀ hnd : (lgManifold n).Nondegenerate
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
        0 < (lgManifold n).planePairing (lambdaPotentialForm φ)
          (tailoringFamily I β s) (lgCover x) hnd ∧
        metricRadialSq H x.1 / 2 ≤
          potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd ∧
        ‖coverFiberProjection H
          (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x) (x.1, 0)‖ ≤
            C * Real.sqrt (metricRadialSq H x.1) := by
  obtain ⟨F, hF, C, hC, β₀, hβ₀, hdata⟩ :=
    tailoringFamily_exists_uniform_whole_end_exhaustion_data
      I hφ hc hU hlower hupper hEnd hhom hREnd heq
  refine ⟨F, hF, C, hC, β₀, hβ₀, ?_⟩
  intro β hβ s hs x
  dsimp only
  intro hr hfs hnd
  exact (hdata β hβ s hs x hr hfs hnd).2.2

/-- The primitive-determined intrinsic field of an actual embedded fiber
has exactly the native projected exhaustion derivative. -/
theorem scalarDerivative_potential_fiberLiouville_eq_projected
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (f : LGSpace n → ℂ)
    {d : ℕ} (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
    (x : N.Point)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map x))
    (hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) f (j.map x) hnd ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Geometry.Model d) 𝓘(ℝ, Geometry.Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) f (j.map x)).ker) :
    N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
        potentialFiberProjectedDerivative φ f (j.map x) hnd := by
  have hkernel' := hkernel.trans
    ((lgManifold n).complexDifferential_ker_eq_real_inf_imag f (j.map x))
  have hpush := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) x hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) f (j.map x)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) f (j.map x))) hpi hkernel'
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hchain := mfderiv_comp_apply x
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map x))
    (j.map.contMDiff.mdifferentiable (by simp) x)
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)
  change N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
      (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map x)
        (mfderiv 𝓘(ℝ, Geometry.Model d) 𝓘(ℝ, Geometry.Model (2 * n)) j.map x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)) at hchain
  rw [hchain, hpush]
  rfl

/-- The entire bounded-value end of any actual smooth fiber realization is
outward for its own restricted primitive and native intrinsic Liouville field. -/
theorem tailoringFamily_exists_uniform_whole_end_intrinsic_exhaustion
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ {d : ℕ} (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
        (x : N.Point),
      (mfderiv 𝓘(ℝ, Geometry.Model d) 𝓘(ℝ, Geometry.Model (2 * n)) j.map x).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)).ker →
      let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 (j.map x).1)
      F * β ≤ Real.sqrt (metricRadialSq H (j.map x).1) →
      ‖tailoringFamily I β s (j.map x)‖ ≤ 2 →
        metricRadialSq H (j.map x).1 / 2 ≤
          N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) := by
  obtain ⟨F, hF, _C, _hC, β₀, hβ₀, hout⟩ :=
    tailoringFamily_exists_uniform_whole_end_projected_exhaustion
      I hφ hc hU hlower hupper hEnd hhom hREnd heq
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ s hs d N j x hkernel
  dsimp only
  intro hr hfs
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map x)
  obtain ⟨z, hz⟩ := lgCover_surjective n (j.map x)
  have hr' : F * β ≤ Real.sqrt (metricRadialSq
      (potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)) z.1) := by
    simpa only [← hz, lgCover] using hr
  have hfs' : ‖tailoringFamily I β s (lgCover z)‖ ≤ 2 := by rw [hz]; exact hfs
  have hnd' : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover z) := by
    rw [hz]; exact hnd
  obtain ⟨hπ, hlow, _hnorm⟩ := hout β hβ s hs z hr' hfs' hnd'
  have hπ' : (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) (j.map x) hnd ≠ 0 := by
    simpa only [hz] using hπ.ne'
  rw [scalarDerivative_potential_fiberLiouville_eq_projected hφ
    (tailoringFamily I β s) N j x hnd hπ' hkernel]
  simpa only [← hz, lgCover] using hlow

end FsFltz
