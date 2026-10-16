import FsFltz.Analysis.TailoringCriticalNormals
import FsFltz.Analysis.TailoringSupport
import FsFltz.Analysis.HomogeneousPotential
import FsFltz.Analysis.CompatiblePotentialExistence

/-!
# Quantitative radial estimates for small tailored conormal distance

Source: `geometric-part-fsf-proof.tex`, `lem:smallzeta`, lines 1375–1391.
All retained coefficients and cutoffs are the literal finite-input objects.
Norms in this module are coordinate supremum norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology ContDiff

variable {n : ℕ}

/-- Complex contraction in the prescribed real coordinate basis. -/
def complexRadialPairing (u : RealSpace n) (g : Fin n → ℂ) : ℂ :=
  ∑ j, (u j : ℂ) * g j

theorem norm_complexRadialPairing_le (u : RealSpace n) (g : Fin n → ℂ) :
    ‖complexRadialPairing u g‖ ≤ (n : ℝ) * ‖u‖ * ‖g‖ := by
  calc
    _ ≤ ∑ j : Fin n, ‖(u j : ℂ) * g j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖u‖ * ‖g‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (norm_le_pi_norm u j) (norm_le_pi_norm g j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem complexRadialPairing_retainedNormal (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) :
    complexRadialPairing y.1 (tailoringRetainedNormal I β y) =
      ∑ v ∈ I.vertices, (pairing v y.1 : ℂ) * tailoringRetainedMonomial I β v y := by
  simp only [complexRadialPairing, tailoringRetainedNormal, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [pairing, Complex.ofReal_sum, Complex.ofReal_mul, latticeComplex,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- The exact fiber equation cancels the support-height component, leaving
only retained deficits. This is the radial estimate in `lem:smallzeta`. -/
theorem tailoringEndpoint_retainedNormal_radial_bound (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hy : tailoringFamily I β 1 y = 1) :
    ‖complexRadialPairing y.1 (tailoringRetainedNormal I β y)‖ ≤
      supportHeight I y.1 * tailoringCutoff I β 0 y.1 +
        I.vertices.card * (Real.sqrt β + 2) * Real.exp (supportHeight I y.1 - β) := by
  let h := supportHeight I y.1
  let q := fun v => tailoringRetainedMonomial I β v y
  have hh : 0 ≤ h := by
    obtain ⟨a, ha, _, _, hb⟩ := I.exists_supportHeight_linear_bounds
    exact (mul_nonneg ha.le (Real.sqrt_nonneg _)).trans (hb y.1).1
  have he : complexRadialPairing y.1 (tailoringRetainedNormal I β y) =
      (h : ℂ) * (tailoringCutoff I β 0 y.1 : ℂ) -
        ∑ v ∈ I.vertices, ((h - pairing v y.1 : ℝ) : ℂ) * q v := by
    rw [complexRadialPairing_retainedNormal]
    simp only [q, Complex.ofReal_sub, sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β y hy]
    ring
  have hterm (v : Lattice n) (hv : v ∈ I.vertices) :
      ‖((h - pairing v y.1 : ℝ) : ℂ) * q v‖ ≤
        (Real.sqrt β + 2) * Real.exp (h - β) := by
    by_cases hret : v ∈ tailoringRetainedVertices I β y.1
    · have hgap := (tailoringRetainedVertex_estimates I β y.1 v hret).1
      have hnonneg : 0 ≤ h - pairing v y.1 :=
        sub_nonneg.mpr (I.pairing_le_supportHeight y.1 ⟨v, hv⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact mul_le_mul hgap.le (norm_tailoringRetainedMonomial_le_max I β v hv y)
        (norm_nonneg _) (by positivity)
    · have hzero : q v = 0 :=
        tailoringRetainedMonomial_eq_zero_of_not_mem_support I β y le_rfl hv hret
      rw [hzero, mul_zero, norm_zero]
      positivity
  rw [he]
  calc
    _ ≤ ‖(h : ℂ) * (tailoringCutoff I β 0 y.1 : ℂ)‖ +
        ‖∑ v ∈ I.vertices, ((h - pairing v y.1 : ℝ) : ℂ) * q v‖ := norm_sub_le _ _
    _ ≤ h * tailoringCutoff I β 0 y.1 +
        ∑ _v ∈ I.vertices, (Real.sqrt β + 2) * Real.exp (h - β) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hh,
          abs_of_nonneg (tailoringCutoff_nonneg I β 0 y.1)]
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = _ := by simp [h, mul_assoc]

/-- A scalar differential contracts its literal coordinate gradient. -/
theorem fderiv_apply_eq_coordinateGradient_pairing (φ : RealSpace n → ℝ)
    (u d : RealSpace n) :
    fderiv ℝ φ u d = ∑ j, coordinateGradient φ u j * d j := by
  have hd : d = ∑ j : Fin n, d j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hd]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateGradient]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Complexification preserves the coordinate supremum norm exactly. -/
theorem norm_coordinateComplexification (p : RealSpace n) :
    ‖(fun j => (p j : ℂ))‖ = ‖p‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm p j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (p j : ℂ)))).mpr
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun j => (p j : ℂ)) j

/-- Compactness on the unit sphere gives a uniform linear bound for the
actual homogeneous coordinate gradient. -/
theorem IsStronglyCompatibleEndPotential.exists_coordinateGradient_upper
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∃ P : ℝ, 0 < P ∧ ∀ u ≠ 0, ‖coordinateGradient φ u‖ ≤ P * ‖u‖ := by
  have hs : ContinuousOn (coordinateGradient φ) (Metric.sphere (0 : RealSpace n) 1) := by
    intro u hu
    apply (continuousAt_coordinateGradient (hφ.smooth u ?_)).continuousWithinAt
    have hn : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hu
    intro he
    simp [he] at hn
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : RealSpace n) 1).exists_bound_of_continuousOn hs
  let P := max C 1
  refine ⟨P, zero_lt_one.trans_le (le_max_right _ _), fun u hu => ?_⟩
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb := hC (‖u‖⁻¹ • u) (by simp [norm_smul, hn.ne'])
  rw [coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
    (fun x hx => (hφ.smooth x hx).differentiableAt (by simp)) hu (inv_pos.mpr hn),
    norm_smul, Real.norm_of_nonneg (inv_pos.mpr hn).le] at hb
  have hb' : ‖u‖⁻¹ * ‖coordinateGradient φ u‖ ≤ P := hb.trans (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_left hb' hn.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_comm] using hm

/-- Euler positivity produces a fixed positive radial angle. The positive
quadratic lower bound is supplied by the constructive potential producer. -/
theorem IsStronglyCompatibleEndPotential.exists_coordinateGradient_radial_angle
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ k : ℝ, 0 < k ∧ ∀ u ≠ 0,
      coordinateGradient φ u ≠ 0 ∧
      k * ‖coordinateGradient φ u‖ * ‖u‖ ≤ fderiv ℝ φ u u := by
  obtain ⟨P, hP, hbound⟩ := hφ.exists_coordinateGradient_upper
  refine ⟨2 * a / P, by positivity, fun u hu => ?_⟩
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he := fderiv_self_of_homogeneous_two
    ((hφ.smooth u hu).differentiableAt (by simp)) (fun t ht => hφ.homogeneous t ht u)
  have hp : 0 < fderiv ℝ φ u u := by
    rw [he]
    exact (mul_pos (by norm_num) (mul_pos ha (sq_pos_of_pos hn))).trans_le
      (mul_le_mul_of_nonneg_left (hlower u) (by norm_num))
  refine ⟨?_, ?_⟩
  · intro hz
    rw [fderiv_apply_eq_coordinateGradient_pairing, hz] at hp
    simp at hp
  · have hb := mul_le_mul_of_nonneg_left (hbound u hu) (show 0 ≤ 2 * a / P * ‖u‖ by positivity)
    have hcancel : (2 * a / P * ‖u‖) * (P * ‖u‖) = 2 * a * ‖u‖ ^ 2 := by
      field_simp
    rw [hcancel] at hb
    rw [he]
    calc
      _ ≤ 2 * a * ‖u‖ ^ 2 := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
      _ ≤ 2 * φ u := by nlinarith [hlower u]

end FsFltz
