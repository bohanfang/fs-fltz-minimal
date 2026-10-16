import FsFltz.Analysis.CompatiblePotentialGauge
import FsFltz.Analysis.SupportMollification
import FsFltz.Analysis.SquaredLipschitz

/-!
# The homogeneous gauge prepotential from the finite toric input

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 576–620.
This constructs the actual smooth convex homogeneous squared gauge from the
support-height convolution. Fan compatibility and the positive quadratic
perturbation are subsequent obligations; no compatible potential is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz

variable {n : ℕ}

/-- The Minkowski gauge of the smoothed support-height unit body. -/
def mollifiedSupportGauge (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) :
    RealSpace n → ℝ := gauge {x | mollifiedSupportHeight I ε hε x ≤ 1}

/-- The convex degree-two function before the strict quadratic perturbation. -/
def mollifiedSupportPrepotential (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (x : RealSpace n) : ℝ := mollifiedSupportGauge I ε hε x ^ 2

theorem mollifiedSupportGauge_contDiffAt (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (mollifiedSupportGauge I ε hε) x :=
  contDiffAt_gauge_convexSublevel (mollifiedSupportHeight_contDiff I ε hε)
    (mollifiedSupportHeight_convex I ε hε)
    (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)
    (mollifiedSupportHeight_sublevel_bounded I ε hε) hx

theorem mollifiedSupportGauge_continuous (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1) :
    Continuous (mollifiedSupportGauge I ε hε) := by
  apply continuous_gauge
  · simpa using (mollifiedSupportHeight_convex I ε hε).convex_le 1
  · exact convexSublevel_mem_nhds_zero (mollifiedSupportHeight_contDiff I ε hε).continuous
      (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)

theorem mollifiedSupportGauge_pos (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) : 0 < mollifiedSupportGauge I ε hε x := by
  apply (gauge_pos (absorbent_nhds_zero ?_)
    ((NormedSpace.isVonNBounded_iff ℝ).mpr (mollifiedSupportHeight_sublevel_bounded I ε hε))).mpr hx
  exact convexSublevel_mem_nhds_zero (mollifiedSupportHeight_contDiff I ε hε).continuous
    (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)

theorem mollifiedSupportGauge_normalization (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) :
    mollifiedSupportHeight I ε hε ((mollifiedSupportGauge I ε hε x)⁻¹ • x) = 1 :=
  apply_inv_gauge_smul_eq_one (mollifiedSupportHeight_contDiff I ε hε).continuous
    (mollifiedSupportHeight_convex I ε hε)
    (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)
    (mollifiedSupportHeight_sublevel_bounded I ε hε) hx

theorem mollifiedSupportPrepotential_convex (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1) :
    ConvexOn ℝ univ (mollifiedSupportPrepotential I ε hε) := by
  apply convexOn_gauge_sq
  · simpa using (mollifiedSupportHeight_convex I ε hε).convex_le 1
  · exact convexSublevel_mem_nhds_zero (mollifiedSupportHeight_contDiff I ε hε).continuous
      (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)

theorem mollifiedSupportPrepotential_contDiffAt (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (mollifiedSupportPrepotential I ε hε) x :=
  (mollifiedSupportGauge_contDiffAt I ε hε hsmall hx).pow 2

theorem mollifiedSupportPrepotential_continuous (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1) :
    Continuous (mollifiedSupportPrepotential I ε hε) :=
  (mollifiedSupportGauge_continuous I ε hε hsmall).pow 2

/-- The homogeneous degree-two function extends with class `C¹` at zero,
even though its unsquared gauge need not be differentiable there. -/
theorem mollifiedSupportPrepotential_contDiff_one (I : ToricInput n)
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1) :
    ContDiff ℝ 1 (mollifiedSupportPrepotential I ε hε) := by
  have hc : Convex ℝ {x | mollifiedSupportHeight I ε hε x ≤ 1} := by
    simpa using (mollifiedSupportHeight_convex I ε hε).convex_le 1
  have hn := convexSublevel_mem_nhds_zero (mollifiedSupportHeight_contDiff I ε hε).continuous
    (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)
  obtain ⟨C, hC⟩ := hc.lipschitz_gauge hn
  exact contDiff_one_sq_of_lipschitz hC gauge_zero
    (fun _ hx => mollifiedSupportGauge_contDiffAt I ε hε hsmall hx)

theorem mollifiedSupportPrepotential_pos (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) : 0 < mollifiedSupportPrepotential I ε hε x :=
  sq_pos_of_pos (mollifiedSupportGauge_pos I ε hε hsmall hx)

@[simp] theorem mollifiedSupportPrepotential_zero (I : ToricInput n) (ε : ℝ) (hε : 0 < ε) :
    mollifiedSupportPrepotential I ε hε 0 = 0 := by
  simp [mollifiedSupportPrepotential, mollifiedSupportGauge]

theorem mollifiedSupportPrepotential_smul (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    {a : ℝ} (ha : 0 ≤ a) (x : RealSpace n) :
    mollifiedSupportPrepotential I ε hε (a • x) =
      a ^ 2 * mollifiedSupportPrepotential I ε hε x := gauge_sq_smul ha x

/-- The actual toric prepotential has the defining convolution normal,
rescaled by a positive number, at every nonzero point. -/
theorem mollifiedSupportPrepotential_fderiv (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ fderiv ℝ (mollifiedSupportPrepotential I ε hε) x =
      c • fderiv ℝ (mollifiedSupportHeight I ε hε)
        ((mollifiedSupportGauge I ε hε x)⁻¹ • x) :=
  fderiv_gauge_sq_positive_multiple (mollifiedSupportHeight_contDiff I ε hε)
    (mollifiedSupportHeight_convex I ε hε)
    (mollifiedSupportHeight_zero_lt_one I ε hε hsmall)
    (mollifiedSupportHeight_sublevel_bounded I ε hε) hx

end FsFltz
