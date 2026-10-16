import FsFltz.Analysis.TailoringCriticalNormals

/-!
# Explicit comparison of actual and leading tailored tangent hyperplanes

Source: `geometric-part-fsf-proof.tex`, `eq:exactdF`, `eq:Gchi`,
lines 1334–1352. The exact coordinate normal supplies a right inverse by
correcting a coordinate of maximal complex normal magnitude. This turns the
proved relative differential error into an actual nearby vector in the
leading complex tangent hyperplane. A real two-dimensional inverse
construction gives the reverse tangent correction. Norms are the fixed logarithmic
coordinate supremum/product norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology

variable {n : ℕ}

/-- The exact normal-coordinate formula for the leading differential. -/
theorem tailoringLeadingDifferential_apply_eq_normal
    (I : ToricInput n) (β : ℝ) (y : LGSpace n) (x : TangentCoordinates n) :
    tailoringLeadingDifferential I β y x =
      ∑ j : Fin n, tailoringRetainedNormal I β y j *
        ((x.1 j : ℂ) + Complex.I * (x.2 j : ℂ)) := by
  have hterm (v : Lattice n) : exponentLinearMap v x =
      ∑ j : Fin n, latticeComplex v j * ((x.1 j : ℂ) + Complex.I * (x.2 j : ℂ)) := by
    rw [exponentLinearMap_eq_pairing]
    simp only [pairing, Complex.ofReal_sum, Complex.ofReal_mul, latticeComplex,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  calc
    _ = ∑ v ∈ I.vertices, ∑ j : Fin n, tailoringRetainedMonomial I β v y *
        (latticeComplex v j * ((x.1 j : ℂ) + Complex.I * (x.2 j : ℂ))) := by
      simp only [tailoringLeadingDifferential, sum_apply, smul_apply, smul_eq_mul,
        hterm, Finset.mul_sum]
    _ = ∑ j : Fin n, (∑ v ∈ I.vertices,
        tailoringRetainedMonomial I β v y * latticeComplex v j) *
        ((x.1 j : ℂ) + Complex.I * (x.2 j : ℂ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by
      simp only [tailoringRetainedNormal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- One complex coordinate determines radial and angular corrections. -/
def logarithmicCoordinateCorrection (j : Fin n) (z : ℂ) : TangentCoordinates n :=
  (Pi.single j z.re, Pi.single j z.im)

theorem tailoringLeadingDifferential_coordinateCorrection
    (I : ToricInput n) (β : ℝ) (y : LGSpace n) (j : Fin n) (z : ℂ) :
    tailoringLeadingDifferential I β y (logarithmicCoordinateCorrection j z) =
      tailoringRetainedNormal I β y j * z := by
  rw [tailoringLeadingDifferential_apply_eq_normal]
  classical
  simp only [logarithmicCoordinateCorrection, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    rw [mul_comm Complex.I, Complex.re_add_im]
  · intro k _ hkj
    simp [hkj]
  · simp

theorem norm_logarithmicCoordinateCorrection_le (j : Fin n) (z : ℂ) :
    ‖logarithmicCoordinateCorrection j z‖ ≤ ‖z‖ := by
  classical
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro k
    by_cases hk : k = j
    · simpa only [logarithmicCoordinateCorrection, Pi.single_apply, hk,
        ite_true, Real.norm_eq_abs] using Complex.abs_re_le_norm z
    · simp only [logarithmicCoordinateCorrection, Pi.single_apply, ite_eq_right hk, norm_zero]
      exact norm_nonneg _
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro k
    by_cases hk : k = j
    · simpa only [logarithmicCoordinateCorrection, Pi.single_apply, hk,
        ite_true, Real.norm_eq_abs] using Complex.abs_im_le_norm z
    · simp only [logarithmicCoordinateCorrection, Pi.single_apply, ite_eq_right hk, norm_zero]
      exact norm_nonneg _

private theorem exists_maximal_normal_coordinate (I : ToricInput n)
    (G : Fin n → ℂ) : ∃ j : Fin n, ‖G j‖ = ‖G‖ := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one I.positive_rank
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j : Fin n => ‖G j‖₊)
  refine ⟨j, ?_⟩
  rw [Pi.norm_def, hj]
  rfl

/-- An explicit coordinate correction produces a vector in the leading
complex hyperplane, with distance controlled by the exact normal defect. -/
theorem exists_nearby_leading_kernel_vector (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hG : tailoringRetainedNormal I β y ≠ 0)
    (v : TangentCoordinates n) :
    ∃ w : TangentCoordinates n,
      tailoringLeadingDifferential I β y w = 0 ∧
      ‖v - w‖ ≤ ‖tailoringLeadingDifferential I β y v‖ /
        ‖tailoringRetainedNormal I β y‖ := by
  obtain ⟨j, hj⟩ := exists_maximal_normal_coordinate I (tailoringRetainedNormal I β y)
  have hjpos : 0 < ‖tailoringRetainedNormal I β y j‖ := by
    rw [hj]
    exact norm_pos_iff.mpr hG
  have hjne : tailoringRetainedNormal I β y j ≠ 0 := norm_pos_iff.mp hjpos
  let z := tailoringLeadingDifferential I β y v / tailoringRetainedNormal I β y j
  let e := logarithmicCoordinateCorrection j z
  have he : tailoringLeadingDifferential I β y e =
      tailoringLeadingDifferential I β y v := by
    rw [tailoringLeadingDifferential_coordinateCorrection]
    dsimp [z]
    exact mul_div_cancel₀ _ hjne
  refine ⟨v - e, ?_, ?_⟩
  · rw [map_sub, he, sub_self]
  · rw [sub_sub_cancel]
    exact (norm_logarithmicCoordinateCorrection_le j z).trans_eq (by
      dsimp [z]
      rw [norm_div, hj])

/-- From the original finite toric input, every actual endpoint tangent
vector has a uniformly exponentially close vector in the leading complex
tangent hyperplane. The full fiber and all its tangent vectors are covered. -/
theorem tailoringEndpoint_exists_uniform_nearby_leading_tangent (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ v : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
      ∃ w : TangentCoordinates n,
        tailoringLeadingDifferential I β (lgCover x) w = 0 ∧
        ‖v - w‖ ≤ C * Real.exp (-Real.sqrt β) * ‖v‖ := by
  obtain ⟨C, hC, B, hB, hrelative⟩ := tailoringEndpoint_exists_uniform_relative_tangent_error I
  obtain ⟨B', hB', hnonzero⟩ := tailoringEndpoint_exists_uniform_retainedNormal_ne_zero I
  refine ⟨C, hC, max B B', hB.trans_le (le_max_left _ _), fun β hβ x hx v hv => ?_⟩
  have hG := hnonzero β ((le_max_right _ _).trans hβ) (lgCover x) hx
  obtain ⟨w, hw, hdist⟩ := exists_nearby_leading_kernel_vector I β (lgCover x) hG v
  refine ⟨w, hw, hdist.trans ?_⟩
  apply (div_le_iff₀ (norm_pos_iff.mpr hG)).mpr
  have h := hrelative β ((le_max_left _ _).trans hβ) x hx v hv
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

private def coordinateCorrectionLinearMap (j : Fin n) (g : ℂ) :
    ℂ →ₗ[ℝ] TangentCoordinates n where
  toFun z := logarithmicCoordinateCorrection j (z / g)
  map_add' z w := by
    simp [logarithmicCoordinateCorrection, add_div, Pi.single_add]
  map_smul' c z := by
    change logarithmicCoordinateCorrection j ((c • z) / g) =
      c • logarithmicCoordinateCorrection j (z / g)
    rw [smul_div_assoc]
    apply Prod.ext <;>
      simp only [logarithmicCoordinateCorrection, Complex.smul_re,
        Complex.smul_im, Pi.single_smul, Prod.smul_fst, Prod.smul_snd]

/-- Smallness of the already defined radial error yields an actual
tangent correction, using a real two-dimensional endomorphism. -/
theorem exists_nearby_actual_kernel_vector (I : ToricInput n) (β : ℝ)
    (x : TangentCoordinates n) (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hG : tailoringRetainedNormal I β (lgCover x) ≠ 0)
    (hE : ‖tailoringRadialError I β (lgCover x)‖ ≤
      ‖tailoringRetainedNormal I β (lgCover x)‖ / 2) (v : TangentCoordinates n) :
    ∃ w : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w = 0 ∧
      ‖v - w‖ ≤ 2 * ‖fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v‖ /
        ‖tailoringRetainedNormal I β (lgCover x)‖ := by
  let G := tailoringRetainedNormal I β (lgCover x)
  let E := tailoringRadialError I β (lgCover x)
  let L := tailoringLeadingDifferential I β (lgCover x)
  let D := fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
  have hD (w : TangentCoordinates n) : D w = L w + E w.1 := by
    dsimp [D, L, E]
    rw [fderiv_tailoringFamily_one_eq_equation_of_fiber I β x hx,
      fderiv_tailoringEquation_cover, add_apply, ContinuousLinearMap.comp_apply]
    rfl
  obtain ⟨j, hj⟩ := exists_maximal_normal_coordinate I G
  have hGpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hjne : G j ≠ 0 := norm_pos_iff.mp (hj.symm ▸ hGpos)
  let R := coordinateCorrectionLinearMap j (G j)
  have hR (z : ℂ) : ‖R z‖ ≤ ‖z‖ / ‖G‖ := by
    exact (norm_logarithmicCoordinateCorrection_le j (z / G j)).trans_eq (by rw [norm_div, hj])
  have hLR (z : ℂ) : L (R z) = z := by
    change tailoringLeadingDifferential I β (lgCover x)
      (logarithmicCoordinateCorrection j (z / G j)) = z
    rw [tailoringLeadingDifferential_coordinateCorrection]
    exact mul_div_cancel₀ _ hjne
  let T : ℂ →ₗ[ℝ] ℂ := D.toLinearMap.comp R
  have hT (z : ℂ) : ‖T z - z‖ ≤ ‖z‖ / 2 := by
    change ‖D (R z) - z‖ ≤ ‖z‖ / 2
    rw [hD, hLR, add_sub_cancel_left]
    calc
      ‖E (R z).1‖ ≤ ‖E‖ * ‖(R z).1‖ := E.le_opNorm _
      _ ≤ (‖G‖ / 2) * (‖z‖ / ‖G‖) :=
        mul_le_mul hE ((norm_fst_le _).trans (hR z)) (norm_nonneg _) (by positivity)
      _ = ‖z‖ / 2 := by field_simp
  have hcoercive (z : ℂ) : ‖z‖ ≤ 2 * ‖T z‖ := by
    have ht := hT z
    have htri := norm_le_insert (T z) z
    linarith
  have hTinj : Function.Injective T := by
    intro z u he
    have hzero : T (z - u) = 0 := by rw [map_sub, he, sub_self]
    have hnorm := hcoercive (z - u)
    rw [hzero, norm_zero, mul_zero] at hnorm
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hTinj) (D v)
  refine ⟨v - R z, ?_, ?_⟩
  · change D (v - R z) = 0
    rw [map_sub]
    change D v - T z = 0
    rw [hz, sub_self]
  · rw [sub_sub_cancel]
    exact (hR z).trans (div_le_div_of_nonneg_right
      (by simpa only [hz] using hcoercive z) hGpos.le)

/-- Both tangent hyperplanes are uniformly close: every leading tangent
vector has an exponentially nearby actual endpoint tangent vector. -/
theorem tailoringEndpoint_exists_uniform_nearby_actual_tangent (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ v : TangentCoordinates n, tailoringLeadingDifferential I β (lgCover x) v = 0 →
      ∃ w : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w = 0 ∧
        ‖v - w‖ ≤ C * Real.exp (-Real.sqrt β) * ‖v‖ := by
  obtain ⟨c, hc, B, hB, hlower⟩ := tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  obtain ⟨D, hD, herror⟩ := tailoringEndpoint_exists_uniform_radialError_bound I
  have hsmall : Tendsto (fun β : ℝ => D * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨B', hB'⟩ := eventually_atTop.mp (hsmall.eventually_lt_const (half_pos hc))
  refine ⟨2 * D / c, div_pos (mul_pos (by norm_num) hD) hc,
    max B B', hB.trans_le (le_max_left _ _), fun β hβ x hx v hv => ?_⟩
  let M := Real.exp (supportHeight I x.1 - β)
  let G := tailoringRetainedNormal I β (lgCover x)
  let E := tailoringRadialError I β (lgCover x)
  have hGlower : c * M ≤ ‖G‖ := hlower β ((le_max_left _ _).trans hβ) (lgCover x) hx
  have hGpos : 0 < ‖G‖ := (mul_pos hc (Real.exp_pos _)).trans_le hGlower
  have hEbound : ‖E‖ ≤ D * Real.exp (-Real.sqrt β) * M := herror β (lgCover x) hx
  have hEsmall : ‖E‖ ≤ ‖G‖ / 2 := by
    have h := mul_le_mul_of_nonneg_right (hB' β ((le_max_right _ _).trans hβ)).le
      (Real.exp_pos (supportHeight I x.1 - β)).le
    linarith only [h, hEbound, hGlower]
  obtain ⟨w, hw, hdist⟩ := exists_nearby_actual_kernel_vector I β x hx
    (norm_pos_iff.mp hGpos) hEsmall v
  refine ⟨w, hw, hdist.trans ?_⟩
  have hDv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = E v.1 := by
    rw [fderiv_tailoringFamily_one_eq_equation_of_fiber I β x hx,
      fderiv_tailoringEquation_cover, add_apply, ContinuousLinearMap.comp_apply, hv, zero_add]
    rfl
  rw [hDv]
  apply (div_le_iff₀ hGpos).mpr
  have hbound : ‖E v.1‖ ≤ D * Real.exp (-Real.sqrt β) * M * ‖v‖ :=
    (E.le_opNorm _).trans (mul_le_mul hEbound (norm_fst_le _) (norm_nonneg _) (by positivity))
  have hM : M ≤ ‖G‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hGlower)
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hM (norm_nonneg v))
    (show 0 ≤ 2 * D * Real.exp (-Real.sqrt β) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * ‖E v.1‖ ≤ 2 * D * Real.exp (-Real.sqrt β) * (M * ‖v‖) := by
      simpa only [mul_assoc] using h2
    _ ≤ 2 * D * Real.exp (-Real.sqrt β) * (‖G‖ / c * ‖v‖) := h
    _ = _ := by ring

end FsFltz
