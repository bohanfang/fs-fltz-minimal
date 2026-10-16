import FsFltz.Analysis.SupportHeightBounds
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Function

/-!
# Smooth convex mollification of the actual support height

This implements the first smoothing step of `geometric-part-fsf-proof.tex`,
`lem:potential`, lines 575–580, for the finite support height of the original
`ToricInput`. The radius here uses the native supremum norm on `RealSpace`.
The finite-dimensional bump API works for that norm and gives a kernel
strictly positive throughout its open support. No potential, gradient cone
condition, or geometric comparison is assumed.
-/

noncomputable section

namespace FsFltz

open MeasureTheory ContinuousLinearMap Set
open scoped BigOperators Convolution Topology NNReal ContDiff

variable {n : ℕ}

/-- The literal lattice pairing, packaged as a continuous linear functional. -/
def pairingCLM (v : Lattice n) : RealSpace n →L[ℝ] ℝ :=
  ∑ j : Fin n, (v j : ℝ) • ContinuousLinearMap.proj j

@[simp] theorem pairingCLM_apply (v : Lattice n) (u : RealSpace n) :
    pairingCLM v u = pairing v u := by
  simp [pairingCLM, pairing]

/-- A positive finite Lipschitz constant for the input support height. -/
def supportHeightLipschitzConstant (I : ToricInput n) : ℝ≥0 :=
  1 + ∑ v : {v : Lattice n // v ∈ I.vertices}, ‖pairingCLM v.val‖₊

theorem supportHeightLipschitzConstant_pos (I : ToricInput n) :
    0 < (supportHeightLipschitzConstant I : ℝ) := by
  simp only [supportHeightLipschitzConstant, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_sum, coe_nnnorm]
  positivity

private theorem pairingCLM_norm_le_constant (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    ‖pairingCLM v.val‖ ≤ (supportHeightLipschitzConstant I : ℝ) := by
  have hs : ‖pairingCLM v.val‖ ≤
      ∑ w : {w : Lattice n // w ∈ I.vertices}, ‖pairingCLM w.val‖ :=
    Finset.single_le_sum
      (f := fun w : {v : Lattice n // v ∈ I.vertices} => ‖pairingCLM w.val‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
  simp only [supportHeightLipschitzConstant, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_sum, coe_nnnorm]
  linarith

theorem ToricInput.supportHeight_sub_le (I : ToricInput n) (x y : RealSpace n) :
    supportHeight I x - supportHeight I y ≤
      (supportHeightLipschitzConstant I : ℝ) * ‖x - y‖ := by
  obtain ⟨v, hv⟩ := I.supportHeight_attained x
  have hvy := I.pairing_le_supportHeight y v
  have hb := (pairingCLM v.val).le_opNorm (x - y)
  rw [map_sub, pairingCLM_apply, pairingCLM_apply] at hb
  have hnorm := pairingCLM_norm_le_constant I v
  calc
    supportHeight I x - supportHeight I y ≤ pairing v.val x - pairing v.val y := by
      rw [← hv]
      linarith
    _ ≤ ‖pairing v.val x - pairing v.val y‖ := Real.le_norm_self _
    _ ≤ ‖pairingCLM v.val‖ * ‖x - y‖ := hb
    _ ≤ (supportHeightLipschitzConstant I : ℝ) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

theorem ToricInput.supportHeight_lipschitz (I : ToricInput n) :
    LipschitzWith (supportHeightLipschitzConstant I) (supportHeight I) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := I.supportHeight_sub_le y x
    rw [norm_sub_rev] at h
    linarith
  · exact I.supportHeight_sub_le x y

/-- A vertex maximizing at a point within the smoothing radius has a small
deficit at the center. This is `eq:mollifierdeficit`, lines 585–587, with
the finite operator-norm constant appropriate to the native norm. -/
theorem ToricInput.supportHeight_deficit_le_of_maximizes_nearby (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) (x y : RealSpace n) {ε : ℝ}
    (hmax : pairing v.val y = supportHeight I y) (hnear : dist x y ≤ ε) :
    0 ≤ supportHeight I x - pairing v.val x ∧
      supportHeight I x - pairing v.val x ≤
        2 * (supportHeightLipschitzConstant I : ℝ) * ε := by
  refine ⟨sub_nonneg.mpr (I.pairing_le_supportHeight x v), ?_⟩
  have hheight := I.supportHeight_sub_le x y
  have hpair := (pairingCLM v.val).le_opNorm (y - x)
  rw [map_sub, pairingCLM_apply, pairingCLM_apply] at hpair
  rw [norm_sub_rev y x] at hpair
  have hnorm := mul_le_mul_of_nonneg_right (pairingCLM_norm_le_constant I v)
    (norm_nonneg (x - y))
  have hsigned := Real.le_norm_self (pairing v.val y - pairing v.val x)
  rw [dist_eq_norm] at hnear
  have hstep := mul_le_mul_of_nonneg_left hnear
    (NNReal.coe_nonneg (supportHeightLipschitzConstant I))
  rw [hmax] at hsigned hpair
  linarith

theorem ToricInput.supportHeight_continuous (I : ToricInput n) :
    Continuous (supportHeight I) := I.supportHeight_lipschitz.continuous

theorem ToricInput.supportHeight_convex (I : ToricInput n) :
    ConvexOn ℝ univ (supportHeight I) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  obtain ⟨v, hv⟩ := I.supportHeight_attained (a • x + b • y)
  have he : pairing v.val (a • x + b • y) =
      a * pairing v.val x + b * pairing v.val y := by
    simpa using (pairingCLM v.val).map_add (a • x) (b • y)
  rw [← hv, he]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (I.pairing_le_supportHeight x v) ha)
    (mul_le_mul_of_nonneg_left (I.pairing_le_supportHeight y v) hb)

@[simp] theorem ToricInput.supportHeight_zero (I : ToricInput n) :
    supportHeight I 0 = 0 := by
  obtain ⟨v, hv⟩ := I.supportHeight_attained 0
  simpa [pairing] using hv.symm

/-- The smooth bump has inner radius `ε / 2` and outer radius `ε`. -/
def supportMollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : RealSpace n) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := half_pos hε
  rIn_lt_rOut := half_lt_self hε

/-- A normalized nonnegative smooth kernel, with literal support the `ε`-ball. -/
def supportMollifier (ε : ℝ) (hε : 0 < ε) : RealSpace n → ℝ :=
  (supportMollifierBump ε hε).normed volume

theorem supportMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    0 ≤ supportMollifier ε hε x :=
  (supportMollifierBump ε hε).nonneg_normed x

theorem supportMollifier_contDiff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (supportMollifier (n := n) ε hε) :=
  (supportMollifierBump ε hε).contDiff_normed

theorem supportMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    ∫ x, supportMollifier (n := n) ε hε x = 1 :=
  (supportMollifierBump ε hε).integral_normed

theorem supportMollifier_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (supportMollifier (n := n) ε hε) = Metric.ball 0 ε :=
  (supportMollifierBump ε hε).support_normed_eq

theorem supportMollifier_hasCompactSupport (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (supportMollifier (n := n) ε hε) :=
  (supportMollifierBump ε hε).hasCompactSupport_normed

theorem supportMollifier_pos (ε : ℝ) (hε : 0 < ε) {x : RealSpace n}
    (hx : x ∈ Metric.ball 0 ε) : 0 < supportMollifier ε hε x := by
  exact div_pos ((supportMollifierBump ε hε).pos_of_mem_ball hx)
    (supportMollifierBump ε hε).integral_pos

/-- The actual convolution of the normalized kernel with the input support height. -/
def mollifiedSupportHeight (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) : RealSpace n → ℝ :=
  supportMollifier ε hε ⋆[lsmul ℝ ℝ] supportHeight I

theorem mollifiedSupportHeight_contDiff (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (mollifiedSupportHeight I ε hε) :=
  (supportMollifier_hasCompactSupport ε hε).contDiff_convolution_left
    (lsmul ℝ ℝ) (supportMollifier_contDiff ε hε) I.supportHeight_continuous.locallyIntegrable

/-- The integrand defining the convolution is integrable at every point. -/
theorem mollifiedSupportHeight_integrable (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (x : RealSpace n) :
    Integrable (fun t => supportMollifier ε hε t * supportHeight I (x - t)) := by
  simpa only [lsmul_apply, smul_eq_mul] using
    ((supportMollifier_hasCompactSupport ε hε).convolutionExists_left
      (lsmul ℝ ℝ) (supportMollifier_contDiff ε hε).continuous
      I.supportHeight_continuous.locallyIntegrable x).integrable

theorem mollifiedSupportHeight_convex (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) :
    ConvexOn ℝ univ (mollifiedSupportHeight I ε hε) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hi := (mollifiedSupportHeight_integrable I ε hε x).const_mul a
  have hj := (mollifiedSupportHeight_integrable I ε hε y).const_mul b
  have hm : ∀ t : RealSpace n,
      supportMollifier ε hε t * supportHeight I (a • x + b • y - t) ≤
        a * (supportMollifier ε hε t * supportHeight I (x - t)) +
          b * (supportMollifier ε hε t * supportHeight I (y - t)) := by
    intro t
    have he : a • x + b • y - t = a • (x - t) + b • (y - t) := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (t j) * hab
    have hc := I.supportHeight_convex.2 (x := x - t) (mem_univ _) (y := y - t)
      (mem_univ _) ha hb hab
    rw [← he] at hc
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using
      mul_le_mul_of_nonneg_left hc (supportMollifier_nonneg ε hε t)
  have hint := integral_mono (mollifiedSupportHeight_integrable I ε hε (a • x + b • y))
    (hi.add hj) hm
  simp only [Pi.add_apply] at hint
  rw [integral_add hi hj, integral_const_mul, integral_const_mul] at hint
  simpa only [mollifiedSupportHeight, convolution_def, lsmul_apply, smul_eq_mul] using hint

theorem mollifiedSupportHeight_approximation (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (x : RealSpace n) :
    |mollifiedSupportHeight I ε hε x - supportHeight I x| ≤
      (supportHeightLipschitzConstant I : ℝ) * ε := by
  apply (supportMollifierBump ε hε).dist_normed_convolution_le
    I.supportHeight_continuous.aestronglyMeasurable
  intro y hy
  have hd : dist y x ≤ ε := (Metric.mem_ball.mp hy).le
  exact (I.supportHeight_lipschitz.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))

theorem mollifiedSupportHeight_zero_lt_one (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1) :
    mollifiedSupportHeight I ε hε 0 < 1 := by
  have h := mollifiedSupportHeight_approximation I ε hε 0
  simp only [I.supportHeight_zero, sub_zero] at h
  exact (le_abs_self _).trans_lt (h.trans_lt hsmall)

/-- Coercivity is retained by the uniform error bound, so the closed unit
sublevel is bounded for every positive smoothing radius. -/
theorem mollifiedSupportHeight_sublevel_bounded (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) :
    Bornology.IsBounded {x : RealSpace n | mollifiedSupportHeight I ε hε x ≤ 1} := by
  obtain ⟨c, hc, H, _, hbounds⟩ := I.exists_supportHeight_linear_bounds
  apply Metric.isBounded_closedBall.subset
    (t := Metric.closedBall (0 : RealSpace n)
      ((1 + (supportHeightLipschitzConstant I : ℝ) * ε) / c))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖x‖ ≤ Real.sqrt (realSquaredNorm x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    simpa [EuclideanSpace.norm_eq, realSquaredNorm, Real.norm_eq_abs]
      using PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) j
  have herr := (abs_le.mp (mollifiedSupportHeight_approximation I ε hε x)).1
  have hheight := (hbounds x).1
  apply (le_div_iff₀ hc).mpr
  have : c * ‖x‖ ≤ c * Real.sqrt (realSquaredNorm x) :=
    mul_le_mul_of_nonneg_left hnorm hc.le
  change mollifiedSupportHeight I ε hε x ≤ 1 at hx
  nlinarith

/-- Arbitrarily small radii produce a smooth convex function whose unit
sublevel is bounded and contains zero in its interior. These are the input
properties for the subsequent Minkowski-gauge construction. -/
theorem ToricInput.exists_mollifiedSupportHeight_unit_geometry (I : ToricInput n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε < ε₀ →
      ContDiff ℝ ∞ (mollifiedSupportHeight I ε hε) ∧
      ConvexOn ℝ univ (mollifiedSupportHeight I ε hε) ∧
      mollifiedSupportHeight I ε hε 0 < 1 ∧
      Bornology.IsBounded {x : RealSpace n | mollifiedSupportHeight I ε hε x ≤ 1} := by
  let C : ℝ := supportHeightLipschitzConstant I
  have hC : 0 < C := supportHeightLipschitzConstant_pos I
  refine ⟨1 / C, by positivity, ?_⟩
  intro ε hε hsmall
  have hsmall' : C * ε < 1 := by
    have := (lt_div_iff₀ hC).mp hsmall
    simpa only [mul_comm] using this
  exact ⟨mollifiedSupportHeight_contDiff I ε hε, mollifiedSupportHeight_convex I ε hε,
    mollifiedSupportHeight_zero_lt_one I ε hε hsmall',
    mollifiedSupportHeight_sublevel_bounded I ε hε⟩

end FsFltz
