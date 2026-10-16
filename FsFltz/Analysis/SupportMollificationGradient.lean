import FsFltz.Analysis.SupportMollification
import FsFltz.Analysis.SupportMaximizerRegions
import FsFltz.Analysis.CoordinateLegendre
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivative of the support-height convolution

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 581–587.
The exceptional loci of ties between distinct lattice vertices are proper
linear hyperplanes, hence null. This is the analytic bridge from the actual
convolution to a weighted average of maximizing vertex functionals.
-/

noncomputable section

namespace FsFltz

open MeasureTheory ContinuousLinearMap Set Filter
open scoped BigOperators Convolution Topology NNReal ContDiff

variable {n : ℕ}

theorem pairingCLM_injective : Function.Injective (pairingCLM (n := n)) := by
  intro v w h
  ext j
  have he := DFunLike.congr_fun h (Pi.single j (1 : ℝ))
  simpa [pairing, Pi.single_apply] using he

/-- Distinct vertex pairings differ off a null hyperplane. -/
theorem pairing_ne_ae (v w : Lattice n) (hvw : v ≠ w) :
    ∀ᵐ x : RealSpace n, pairing v x ≠ pairing w x := by
  let L := (pairingCLM v - pairingCLM w).toLinearMap
  have hker : L.ker ≠ ⊤ := by
    intro htop
    have hzero : L = 0 := LinearMap.ker_eq_top.mp htop
    apply hvw
    apply pairingCLM_injective
    apply ContinuousLinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hzero x
    exact sub_eq_zero.mp (by simpa [L] using hx)
  have hm := Measure.addHaar_submodule (volume : Measure (RealSpace n)) L.ker hker
  have hs : (L.ker : Set (RealSpace n)) = {a | pairing v a = pairing w a} := by
    ext a
    change L a = 0 ↔ pairing v a = pairing w a
    simp [L, sub_eq_zero]
  rw [hs] at hm
  rw [ae_iff]
  simpa only [not_not] using hm

/-- Almost every point has one strict maximizing vertex. -/
theorem ToricInput.supportHeight_strict_maximizer_ae (I : ToricInput n) :
    ∀ᵐ x : RealSpace n, ∃ v : {v : Lattice n // v ∈ I.vertices},
      ∀ w : {v : Lattice n // v ∈ I.vertices}, w ≠ v →
        pairing w.val x < pairing v.val x := by
  have hall : ∀ᵐ x : RealSpace n,
      ∀ v w : {v : Lattice n // v ∈ I.vertices}, v ≠ w →
        pairing v.val x ≠ pairing w.val x := by
    rw [ae_all_iff]
    intro v
    rw [ae_all_iff]
    intro w
    by_cases h : v = w
    · exact Eventually.of_forall (by simp [h])
    · exact (pairing_ne_ae v.val w.val (fun he => h (Subtype.ext he))).mono
        (fun _ hx _ => hx)
  filter_upwards [hall] with x hx
  obtain ⟨v, hv⟩ := I.supportHeight_attained x
  refine ⟨v, ?_⟩
  intro w hw
  apply lt_of_le_of_ne
  · rw [hv]
    exact I.pairing_le_supportHeight x w
  · exact hx w v hw

theorem supportHeight_eq_pairing_of_strictMaximizer (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {x : RealSpace n}
    (hx : x ∈ strictMaximizerRegion I v) : supportHeight I x = pairing v.val x := by
  obtain ⟨w, hw⟩ := I.supportHeight_attained x
  by_cases he : w = v
  · simpa [he] using hw.symm
  · have hlt := hx w he
    have hle := I.pairing_le_supportHeight x v
    linarith

theorem supportHeight_hasFDerivAt_of_strictMaximizer (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {x : RealSpace n}
    (hx : x ∈ strictMaximizerRegion I v) :
    HasFDerivAt (supportHeight I) (pairingCLM v.val) x := by
  apply (pairingCLM v.val).hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [(isOpen_strictMaximizerRegion I v).mem_nhds hx] with y hy
  simpa only [pairingCLM_apply] using supportHeight_eq_pairing_of_strictMaximizer I v hy

/-- The almost-everywhere differential, with zero assigned on tie loci. -/
def supportHeightVertexDifferential (I : ToricInput n) (x : RealSpace n) :
    RealSpace n →L[ℝ] ℝ :=
  ∑ v : {v : Lattice n // v ∈ I.vertices},
    (strictMaximizerRegion I v).indicator (fun _ => pairingCLM v.val) x

theorem strictMaximizerRegion_disjoint (I : ToricInput n)
    (v w : {v : Lattice n // v ∈ I.vertices}) (hvw : v ≠ w) :
    Disjoint (strictMaximizerRegion I v) (strictMaximizerRegion I w) := by
  apply disjoint_left.mpr
  intro x hv hw
  exact (hv w hvw.symm).not_gt (hw v hvw)

theorem supportHeightVertexDifferential_eq_of_strictMaximizer (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {x : RealSpace n}
    (hx : x ∈ strictMaximizerRegion I v) :
    supportHeightVertexDifferential I x = pairingCLM v.val := by
  classical
  unfold supportHeightVertexDifferential
  rw [Finset.sum_eq_single v]
  · exact indicator_of_mem hx _
  · intro w _ hw
    have hn : x ∉ strictMaximizerRegion I w := by
      intro hwx
      exact disjoint_left.mp (strictMaximizerRegion_disjoint I v w hw.symm) hx hwx
    exact indicator_of_notMem hn _
  · simp

theorem supportHeightVertexDifferential_stronglyMeasurable (I : ToricInput n) :
    StronglyMeasurable (supportHeightVertexDifferential I) := by
  unfold supportHeightVertexDifferential
  simp only [← Finset.sum_apply]
  apply Finset.stronglyMeasurable_sum
  intro v _
  exact stronglyMeasurable_const.indicator (isOpen_strictMaximizerRegion I v).measurableSet

theorem ToricInput.supportHeight_hasFDerivAt_ae (I : ToricInput n) :
    ∀ᵐ x : RealSpace n,
      HasFDerivAt (supportHeight I) (supportHeightVertexDifferential I x) x := by
  filter_upwards [I.supportHeight_strict_maximizer_ae] with x hx
  obtain ⟨v, hv⟩ := hx
  rw [supportHeightVertexDifferential_eq_of_strictMaximizer I v hv]
  exact supportHeight_hasFDerivAt_of_strictMaximizer I v hv

/-- Differentiating the actual convolution gives the integral of its
almost-everywhere vertex differential. The domination comes from the
proved finite support-height Lipschitz constant. -/
theorem mollifiedSupportHeight_hasFDerivAt_integral (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    HasFDerivAt (mollifiedSupportHeight I ε hε)
      (∫ t, supportMollifier ε hε t • supportHeightVertexDifferential I (x - t)) x := by
  let F : RealSpace n → RealSpace n → ℝ :=
    fun y t => supportMollifier ε hε t * supportHeight I (y - t)
  let D : RealSpace n → RealSpace n →L[ℝ] ℝ :=
    fun t => supportMollifier ε hε t • supportHeightVertexDifferential I (x - t)
  let C : ℝ := supportHeightLipschitzConstant I
  have hC : 0 ≤ C := NNReal.coe_nonneg _
  have hDm : AEStronglyMeasurable D volume := by
    exact ((supportMollifier_contDiff ε hε).continuous.stronglyMeasurable.smul
      ((supportHeightVertexDifferential_stronglyMeasurable I).comp_measurable
        (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hLip : ∀ᵐ t : RealSpace n,
      LipschitzOnWith (Real.nnabs (supportMollifier ε hε t * C)) (F · t) univ := by
    filter_upwards with t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hr := supportMollifier_nonneg ε hε t
    have hq := I.supportHeight_lipschitz.norm_sub_le (y - t) (z - t)
    simp only [sub_sub_sub_cancel_right, Real.norm_eq_abs] at hq
    change ‖supportMollifier ε hε t * supportHeight I (y - t) -
      supportMollifier ε hε t * supportHeight I (z - t)‖ ≤
        |supportMollifier ε hε t * C| * ‖y - z‖
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hr, abs_of_nonneg (mul_nonneg hr hC)]
    calc
      supportMollifier ε hε t * |supportHeight I (y - t) - supportHeight I (z - t)| ≤
          supportMollifier ε hε t * (C * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left hq hr
      _ = supportMollifier ε hε t * C * ‖y - z‖ := (mul_assoc _ _ _).symm
  have hbound : Integrable (fun t : RealSpace n => supportMollifier ε hε t * C) :=
    (supportMollifierBump ε hε).integrable_normed.mul_const C
  have hDiff : ∀ᵐ t : RealSpace n, HasFDerivAt (F · t) (D t) x := by
    have hae := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      I.supportHeight_hasFDerivAt_ae
    filter_upwards [hae] with t ht
    have hq : HasFDerivAt (fun y => supportHeight I (y - t))
        (supportHeightVertexDifferential I (x - t)) x := by
      convert! ht.comp x ((hasFDerivAt_id x).sub_const t) using 1
    exact hq.const_mul (supportMollifier ε hε t)
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (bound := fun t : RealSpace n => supportMollifier ε hε t * C)
    (F := F) (F' := D) (μ := volume)
    (by simp) (Eventually.of_forall fun y =>
      (mollifiedSupportHeight_integrable I ε hε y).aestronglyMeasurable)
    (mollifiedSupportHeight_integrable I ε hε x) hDm hLip hbound hDiff
  convert! h.2 using 1

theorem mollifiedSupportHeight_fderiv_integral (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    fderiv ℝ (mollifiedSupportHeight I ε hε) x =
      ∫ t, supportMollifier ε hε t • supportHeightVertexDifferential I (x - t) :=
  (mollifiedSupportHeight_hasFDerivAt_integral I ε hε x).fderiv

/-- The nonnegative convolution mass of the strict maximizing region of a
specified vertex. Boundary ties have measure zero. -/
def supportMollifierVertexWeight (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (x : RealSpace n) (v : {v : Lattice n // v ∈ I.vertices}) : ℝ :=
  ∫ t, {t : RealSpace n | x - t ∈ strictMaximizerRegion I v}.indicator
    (supportMollifier ε hε) t

theorem supportMollifierVertexWeight_integrable (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    Integrable ({t : RealSpace n | x - t ∈ strictMaximizerRegion I v}.indicator
      (supportMollifier ε hε)) :=
  (supportMollifierBump ε hε).integrable_normed.indicator
    ((isOpen_strictMaximizerRegion I v).measurableSet.preimage
      (measurable_const.sub measurable_id))

theorem supportMollifierVertexWeight_nonneg (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    0 ≤ supportMollifierVertexWeight I ε hε x v := by
  exact integral_nonneg (indicator_nonneg (fun t _ => supportMollifier_nonneg ε hε t))

/-- Every vertex maximizing at the center receives strictly positive mass. -/
theorem supportMollifierVertexWeight_pos_of_maximizer (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices})
    (hmax : pairing v.val x = supportHeight I x) :
    0 < supportMollifierVertexWeight I ε hε x v := by
  apply (integral_pos_iff_support_of_nonneg
    (indicator_nonneg (fun t _ => supportMollifier_nonneg ε hε t))
    (supportMollifierVertexWeight_integrable I ε hε x v)).mpr
  rw [support_indicator, supportMollifier_support, inter_comm]
  exact I.volume_ball_zero_inter_sub_strictMaximizerRegion_pos v hmax hε

/-- Precisely the vertex regions meeting the positive kernel support have
positive averaging coefficients. -/
theorem supportMollifierVertexWeight_pos_iff (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    0 < supportMollifierVertexWeight I ε hε x v ↔
      (Metric.ball (0 : RealSpace n) ε ∩
        {t : RealSpace n | x - t ∈ strictMaximizerRegion I v}).Nonempty := by
  rw [supportMollifierVertexWeight, integral_pos_iff_support_of_nonneg
    (indicator_nonneg (fun t _ => supportMollifier_nonneg ε hε t))
    (supportMollifierVertexWeight_integrable I ε hε x v),
    support_indicator, supportMollifier_support, inter_comm]
  constructor
  · intro h
    exact nonempty_of_measure_ne_zero h.ne'
  · intro h
    exact (Metric.isOpen_ball.inter
      ((isOpen_strictMaximizerRegion I v).preimage
        (continuous_const.sub continuous_id))).measure_pos volume h

theorem supportMollifierVertexWeight_sum (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    (∑ v : {v : Lattice n // v ∈ I.vertices}, supportMollifierVertexWeight I ε hε x v) = 1 := by
  classical
  unfold supportMollifierVertexWeight
  rw [← integral_finsetSum Finset.univ
    (fun v _ => supportMollifierVertexWeight_integrable I ε hε x v)]
  rw [← supportMollifier_integral (n := n) ε hε]
  apply integral_congr_ae
  have hae := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    I.supportHeight_strict_maximizer_ae
  filter_upwards [hae] with t ht
  obtain ⟨v, hv⟩ := ht
  rw [Finset.sum_eq_single v]
  · exact indicator_of_mem
      (show t ∈ {t : RealSpace n | x - t ∈ strictMaximizerRegion I v} from hv) _
  · intro w _ hw
    have hn : x - t ∉ strictMaximizerRegion I w := by
      intro hwx
      exact disjoint_left.mp (strictMaximizerRegion_disjoint I v w hw.symm) hv hwx
    exact indicator_of_notMem
      (show t ∉ {t : RealSpace n | x - t ∈ strictMaximizerRegion I w} from hn) _
  · simp

/-- The derivative is the finite convex average of actual vertex pairings. -/
theorem mollifiedSupportHeight_fderiv_eq_weighted_sum (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    fderiv ℝ (mollifiedSupportHeight I ε hε) x =
      ∑ v : {v : Lattice n // v ∈ I.vertices},
        supportMollifierVertexWeight I ε hε x v • pairingCLM v.val := by
  classical
  rw [mollifiedSupportHeight_fderiv_integral]
  calc
    (∫ t, supportMollifier ε hε t • supportHeightVertexDifferential I (x - t)) =
        ∫ t, ∑ v : {v : Lattice n // v ∈ I.vertices},
          {t : RealSpace n | x - t ∈ strictMaximizerRegion I v}.indicator
            (supportMollifier ε hε) t • pairingCLM v.val := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [supportHeightVertexDifferential, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases ht : x - t ∈ strictMaximizerRegion I v
      · simp [ht]
      · simp [ht]
    _ = ∑ v : {v : Lattice n // v ∈ I.vertices},
        ∫ t, {t : RealSpace n | x - t ∈ strictMaximizerRegion I v}.indicator
          (supportMollifier ε hε) t • pairingCLM v.val :=
      integral_finsetSum Finset.univ
        (fun v _ => (supportMollifierVertexWeight_integrable I ε hε x v).smul_const _)
    _ = ∑ v : {v : Lattice n // v ∈ I.vertices},
        supportMollifierVertexWeight I ε hε x v • pairingCLM v.val := by
      apply Finset.sum_congr rfl
      intro v _
      exact integral_smul_const _ _

/-- The actual native coordinate gradient is the same finite convex average
of the lattice normals used by the fan's common-face theorem. -/
theorem mollifiedSupportHeight_coordinateGradient_eq_weighted_sum (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n) :
    coordinateGradient (mollifiedSupportHeight I ε hε) x =
      ∑ v : {v : Lattice n // v ∈ I.vertices},
        supportMollifierVertexWeight I ε hε x v • latticeReal v.val := by
  ext j
  unfold coordinateGradient
  rw [mollifiedSupportHeight_fderiv_eq_weighted_sum]
  simp [pairing, latticeReal, Pi.single_apply]

/-- A positive coefficient can only come from a vertex with the small
deficit prescribed in `eq:mollifierdeficit`. -/
theorem supportMollifierVertexWeight_deficit_le (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε) (x : RealSpace n)
    (v : {v : Lattice n // v ∈ I.vertices})
    (hv : 0 < supportMollifierVertexWeight I ε hε x v) :
    0 ≤ supportHeight I x - pairing v.val x ∧
      supportHeight I x - pairing v.val x ≤
        2 * (supportHeightLipschitzConstant I : ℝ) * ε := by
  have hpos := (integral_pos_iff_support_of_nonneg
    (indicator_nonneg (fun t _ => supportMollifier_nonneg ε hε t))
    (supportMollifierVertexWeight_integrable I ε hε x v)).mp hv
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hpos.ne'
  rw [support_indicator, supportMollifier_support] at ht
  have hmax : pairing v.val (x - t) = supportHeight I (x - t) :=
    (supportHeight_eq_pairing_of_strictMaximizer I v ht.1).symm
  have hnear : dist x (x - t) ≤ ε := by
    rw [dist_eq_norm, show x - (x - t) = t by abel]
    simpa only [dist_zero_right] using (Metric.mem_ball.mp ht.2).le
  exact I.supportHeight_deficit_le_of_maximizes_nearby v x (x - t) hmax hnear

end FsFltz
