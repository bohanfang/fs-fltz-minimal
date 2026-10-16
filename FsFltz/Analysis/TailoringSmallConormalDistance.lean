import FsFltz.Analysis.TailoringSmallConormal
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The literal Euclidean small-conormal-distance localization

Source: `geometric-part-fsf-proof.tex`, `lem:smallzeta`, lines 1354–1391.
The distance below is the infimum to the actual retained complex normal line,
in the prescribed based Euclidean norm. A proved change of norm transfers
the quantitative coordinate theorem to this literal distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology ContDiff

variable {n : ℕ}

/-- The source's normalized Euclidean distance from the homogeneous
gradient to the actual retained complex normal line. -/
def tailoringConormalDistance (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β : ℝ) (y : LGSpace n) : ℝ :=
  Metric.infDist
    (WithLp.toLp 2 (fun j => (coordinateGradient φ y.1 j : ℂ)) : EuclideanSpace ℂ (Fin n))
    (Set.range fun t : ℂ =>
      (WithLp.toLp 2 (t • tailoringRetainedNormal I β y) : EuclideanSpace ℂ (Fin n))) /
    ‖(WithLp.toLp 2 (coordinateGradient φ y.1) : EuclideanSpace ℝ (Fin n))‖

theorem tailoringConormalDistance_nonneg (I : ToricInput n)
    (φ : RealSpace n → ℝ) (β : ℝ) (y : LGSpace n) :
    0 ≤ tailoringConormalDistance I φ β y :=
  div_nonneg Metric.infDist_nonneg (norm_nonneg _)

/-- Small literal Euclidean distance supplies an actual complex-line
approximant satisfying the quantitative native coordinate estimate. -/
theorem exists_retained_normal_approximant_of_small_conormalDistance
    (I : ToricInput n) (φ : RealSpace n → ℝ) (β : ℝ) (y : LGSpace n)
    {δ : ℝ} (hδ : 0 < δ) (hp : coordinateGradient φ y.1 ≠ 0)
    (hz : tailoringConormalDistance I φ β y ≤
      δ / (2 * (1 + ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖))) :
    ∃ t : ℂ, ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
      t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖ := by
  let p := coordinateGradient φ y.1
  let pc : Fin n → ℂ := fun j => (p j : ℂ)
  let G := tailoringRetainedNormal I β y
  let A := 1 + ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖
  have hA : 0 < A := by dsimp [A]; positivity
  let P := ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖
  have hP : 0 < P := by
    apply norm_pos_iff.mpr
    intro he
    apply hp
    exact congrArg WithLp.ofLp he
  have hbound : P ≤ A * ‖p‖ := by
    exact ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (norm_nonneg _))
  let S : Set (EuclideanSpace ℂ (Fin n)) :=
    Set.range fun t : ℂ => (WithLp.toLp 2 (t • G) : EuclideanSpace ℂ (Fin n))
  let q : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 pc
  have hz' : Metric.infDist q S ≤ δ / (2 * A) * P :=
    (div_le_iff₀ hP).mp hz
  have hsmall : Metric.infDist q S < δ * ‖p‖ := by
    have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ δ / (2 * A) by positivity)
    have he : δ / (2 * A) * (A * ‖p‖) = δ / 2 * ‖p‖ := by field_simp
    rw [he] at hb
    have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    nlinarith [mul_pos hδ hpn]
  have hS : S.Nonempty := ⟨WithLp.toLp 2 ((0 : ℂ) • G), ⟨0, rfl⟩⟩
  obtain ⟨z, hzS, hdist⟩ := (Metric.infDist_lt_iff hS).mp hsmall
  obtain ⟨t, rfl⟩ := hzS
  rw [dist_eq_norm, ← WithLp.toLp_sub] at hdist
  refine ⟨t, le_trans ?_ hdist.le⟩
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 (pc - t • G) : EuclideanSpace ℂ (Fin n)) j

/-- The source's small-conormal lemma, with the literal Euclidean normalized
distance and all conclusions quantified uniformly on the full endpoint fiber. -/
theorem tailoringEndpoint_exists_small_conormalDistance_localization
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∃ d : ℝ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      tailoringConormalDistance I φ β y ≤ ζ →
      1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) ∧
      Real.exp (supportHeight I y.1 - β) ≤ M₀ ∧
      tailoringCutoff I β 0 y.1 = 1 ∧
      |supportHeight I y.1 - β| ≤ C ∧
      d * β ≤ Real.sqrt (realSquaredNorm y.1) ∧
      Real.sqrt (realSquaredNorm y.1) ≤ D * β := by
  obtain ⟨δ, hδ, M₀, hM₀, C, hC, d, hd, D, hD, B, hB, hloc⟩ :=
    tailoringEndpoint_exists_small_conormal_localization I hφ ha hlower
  obtain ⟨_, _, B', hB', hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨_, _, hangle⟩ := hφ.exists_coordinateGradient_radial_angle ha hlower
  let A := 1 + ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨δ / (2 * (1 + ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖)),
    by positivity, M₀, hM₀, C, hC, d, hd, A * D, mul_pos hA hD, max B B',
    hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy hz
  have hu := (hrad β ((le_max_right _ _).trans hβ) y hy).1
  have hp := (hangle y.1 hu).1
  obtain ⟨hMlower, hMupper, hχ, herror, hlow, hupper⟩ := hloc β ((le_max_left _ _).trans hβ) y hy
    (exists_retained_normal_approximant_of_small_conormalDistance I φ β y hδ hp hz)
  have he : Real.sqrt (realSquaredNorm y.1) =
      ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    simp only [EuclideanSpace.norm_eq, realSquaredNorm, Real.norm_eq_abs, sq_abs]
  have hnative : ‖y.1‖ ≤ Real.sqrt (realSquaredNorm y.1) := by
    rw [he]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact PiLp.norm_apply_le (WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n)) j
  have hbound : Real.sqrt (realSquaredNorm y.1) ≤ A * ‖y.1‖ := by
    rw [he]
    exact ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm y.1).trans
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (norm_nonneg _))
  refine ⟨hMlower, hMupper, hχ, herror, hlow.trans hnative, hbound.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hupper hA.le

/-- The original finite input produces the potential and the literal
Euclidean small-conormal-distance localization, including its exact
constant cutoff and its Euclidean radial annulus. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential_with_smallConormalDistance_localization
    (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∃ ζ : ℝ, 0 < ζ ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∃ d : ℝ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      tailoringConormalDistance I φ β y ≤ ζ →
      1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) ∧
      Real.exp (supportHeight I y.1 - β) ≤ M₀ ∧
      tailoringCutoff I β 0 y.1 = 1 ∧
      |supportHeight I y.1 - β| ≤ C ∧
      d * β ≤ Real.sqrt (realSquaredNorm y.1) ∧
      Real.sqrt (realSquaredNorm y.1) ≤ D * β := by
  obtain ⟨φ, hφ, hφ1, hφ0, a, ha, _, hpos, _⟩ := I.exists_stronglyCompatibleEndPotential
  refine ⟨φ, hφ, hφ1, hφ0, tailoringEndpoint_exists_small_conormalDistance_localization I hφ ha ?_⟩
  intro u
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hn : ‖u‖ ≤ ‖e.symm u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact PiLp.norm_apply_le (e.symm u) j
  have hsq : ‖u‖ ^ 2 ≤ ‖e.symm u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact (mul_le_mul_of_nonneg_left hsq ha.le).trans
    (by simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hpos (e.symm u))

end FsFltz
