import FsFltz.Analysis.TailoringCriticalTangent

/-!
# The retained conormal line at actual tailored critical points

Source: `geometric-part-fsf-proof.tex`, `sec:critical`, lines 1354–1365,
and the first step of `lem:localcritical`, lines 1452–1454.
Actual annihilation on the endpoint tangent kernel is converted into an
explicit complex-line approximation by the proved reverse tangent estimate.
Coordinate supremum norms and Euclidean norms are kept distinct.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

private def realCoordinatePairing (p : RealSpace n) (angular : Bool)
    (v : TangentCoordinates n) : ℝ :=
  ∑ j, p j * (if angular then v.2 else v.1) j

private theorem realCoordinatePairing_sub (p : RealSpace n) (b : Bool)
    (v w : TangentCoordinates n) :
    realCoordinatePairing p b (v - w) =
      realCoordinatePairing p b v - realCoordinatePairing p b w := by
  cases b <;> simp [realCoordinatePairing, mul_sub, Finset.sum_sub_distrib]

private theorem norm_realCoordinatePairing_le (p : RealSpace n) (b : Bool)
    (v : TangentCoordinates n) :
    ‖realCoordinatePairing p b v‖ ≤ (n : ℝ) * ‖p‖ * ‖v‖ := by
  have hcomponent (j : Fin n) : ‖(if b then v.2 else v.1) j‖ ≤ ‖v‖ := by
    cases b
    · exact (norm_le_pi_norm v.1 j).trans (norm_fst_le v)
    · exact (norm_le_pi_norm v.2 j).trans (norm_snd_le v)
  calc
    _ ≤ ∑ j : Fin n, ‖p j * (if b then v.2 else v.1) j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖p‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm p j) (hcomponent j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

private theorem realCoordinatePairing_coordinateCorrection (p : RealSpace n)
    (b : Bool) (j : Fin n) (z : ℂ) :
    realCoordinatePairing p b (logarithmicCoordinateCorrection j z) =
      if b then ((p j : ℂ) * z).im else ((p j : ℂ) * z).re := by
  classical
  cases b <;> simp [realCoordinatePairing, logarithmicCoordinateCorrection,
    Pi.single_apply, Complex.mul_re, Complex.mul_im]

private theorem exists_maximal_complex_coordinate (I : ToricInput n)
    (G : Fin n → ℂ) : ∃ j : Fin n, ‖G j‖ = ‖G‖ := by
  let : Nonempty (Fin n) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one I.positive_rank⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j : Fin n => ‖G j‖₊)
  refine ⟨j, ?_⟩
  rw [Pi.norm_def, hj]
  rfl

/-- Quantitative coordinate extraction of the complex normal line. The
hypothesis controls a radial or angular covector on the leading hyperplane;
the complex coefficient is constructed from a maximal normal coordinate. -/
theorem exists_retained_line_approximation_of_leading_pairing_bound
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hG : tailoringRetainedNormal I β y ≠ 0) (p : RealSpace n)
    {η : ℝ} (hη : 0 ≤ η)
    (hp : (∀ v : TangentCoordinates n,
        tailoringLeadingDifferential I β y v = 0 →
        ‖∑ j, p j * v.1 j‖ ≤ η * ‖v‖) ∨
      (∀ v : TangentCoordinates n,
        tailoringLeadingDifferential I β y v = 0 →
        ‖∑ j, p j * v.2 j‖ ≤ η * ‖v‖)) :
    ∃ t : ℂ, ‖(fun j => (p j : ℂ)) - t • tailoringRetainedNormal I β y‖ ≤ 4 * η := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ v : TangentCoordinates n,
      tailoringLeadingDifferential I β y v = 0 →
      ‖realCoordinatePairing p b v‖ ≤ η * ‖v‖ := by
    rcases hp with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, hp⟩
  let G := tailoringRetainedNormal I β y
  obtain ⟨j, hj⟩ := exists_maximal_complex_coordinate I G
  have hjpos : 0 < ‖G j‖ := hj.symm ▸ norm_pos_iff.mpr hG
  have hjne : G j ≠ 0 := norm_pos_iff.mp hjpos
  let t : ℂ := (p j : ℂ) / G j
  refine ⟨t, (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_⟩
  let d : ℂ := (p k : ℂ) - t * G k
  have htest (a : ℂ) (ha : ‖a‖ = 1) :
      ‖if b then (a * d).im else (a * d).re‖ ≤ 2 * η := by
    let v := logarithmicCoordinateCorrection k a -
      logarithmicCoordinateCorrection j (a * G k / G j)
    have hv : tailoringLeadingDifferential I β y v = 0 := by
      rw [map_sub, tailoringLeadingDifferential_coordinateCorrection,
        tailoringLeadingDifferential_coordinateCorrection]
      change G k * a - G j * (a * G k / G j) = 0
      field_simp
      ring
    have hratio : ‖a * G k / G j‖ ≤ 1 := by
      rw [norm_div, norm_mul, ha, one_mul]
      exact (div_le_one hjpos).mpr (hj.symm ▸ norm_le_pi_norm G k)
    have hnorm : ‖v‖ ≤ 2 :=
      (norm_sub_le _ _).trans ((add_le_add
        ((norm_logarithmicCoordinateCorrection_le k a).trans_eq ha)
        ((norm_logarithmicCoordinateCorrection_le j _).trans hratio)).trans_eq (by norm_num))
    have hid : (p k : ℂ) * a - (p j : ℂ) * (a * G k / G j) = a * d := by
      dsimp [d, t]
      field_simp
    have heval : realCoordinatePairing p b v =
        if b then (a * d).im else (a * d).re := by
      rw [realCoordinatePairing_sub, realCoordinatePairing_coordinateCorrection,
        realCoordinatePairing_coordinateCorrection]
      cases b
      · simpa only [Bool.false_eq_true, ite_false, Complex.sub_re] using congrArg Complex.re hid
      · simpa only [ite_true, Complex.sub_im] using congrArg Complex.im hid
    rw [← heval]
    exact (hb v hv).trans ((mul_le_mul_of_nonneg_left hnorm hη).trans_eq (mul_comm _ _))
  have h1 := htest 1 (by simp)
  have hI := htest Complex.I (by simp)
  have hre : |d.re| ≤ 2 * η := by
    cases b
    · simpa using h1
    · simpa using hI
  have him : |d.im| ≤ 2 * η := by
    cases b
    · simpa using hI
    · simpa using h1
  change ‖d‖ ≤ 4 * η
  exact (Complex.norm_le_abs_re_add_abs_im d).trans
    ((add_le_add hre him).trans_eq (by ring))

/-- Every actual radial or angular endpoint conormal lies exponentially
close to the retained complex normal line. This includes the zero covector. -/
theorem tailoringEndpoint_exists_uniform_annihilator_line_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ p : RealSpace n,
      ((∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, p j * v.1 j = 0) ∨
       (∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, p j * v.2 j = 0)) →
      ∃ t : ℂ, ‖(fun j => (p j : ℂ)) - t • tailoringRetainedNormal I β (lgCover x)‖ ≤
        C * Real.exp (-Real.sqrt β) * ‖p‖ := by
  obtain ⟨D, hD, B, hB, htangent⟩ :=
    tailoringEndpoint_exists_uniform_nearby_actual_tangent I
  obtain ⟨B', hB', hnonzero⟩ := tailoringEndpoint_exists_uniform_retainedNormal_ne_zero I
  have hn : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one I.positive_rank
  refine ⟨4 * n * D, by positivity, max B B', hB.trans_le (le_max_left _ _),
    fun β hβ x hx p hp => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ v : TangentCoordinates n,
      fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
      realCoordinatePairing p b v = 0 := by
    rcases hp with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, hp⟩
  let η := (n : ℝ) * D * Real.exp (-Real.sqrt β) * ‖p‖
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hcontrol (v : TangentCoordinates n)
      (hv : tailoringLeadingDifferential I β (lgCover x) v = 0) :
      ‖realCoordinatePairing p b v‖ ≤ η * ‖v‖ := by
    obtain ⟨w, hw, hdist⟩ := htangent β ((le_max_left _ _).trans hβ) x hx v hv
    have heq : realCoordinatePairing p b v = realCoordinatePairing p b (v - w) := by
      rw [realCoordinatePairing_sub, hb w hw, sub_zero]
    rw [heq]
    exact (norm_realCoordinatePairing_le p b (v - w)).trans
      ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ (n : ℝ) * ‖p‖)).trans_eq
        (by dsimp [η]; ring))
  obtain ⟨t, ht⟩ := exists_retained_line_approximation_of_leading_pairing_bound I β
    (lgCover x) (hnonzero β ((le_max_right _ _).trans hβ) (lgCover x) hx) p hη
    (by cases b; exact Or.inl hcontrol; exact Or.inr hcontrol)
  exact ⟨t, ht.trans_eq (by dsimp [η]; ring)⟩

/-- The real coordinate supremum norm is bounded by its Euclidean norm. -/
theorem real_pi_norm_le_euclidean_norm (p : RealSpace n) :
    ‖p‖ ≤ ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact PiLp.norm_apply_le (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n)) j

/-- Explicit fixed-coordinate norm transfer, using the canonical change
from the complex supremum norm to the Euclidean norm. -/
theorem complex_euclidean_norm_le_pi_norm (z : Fin n → ℂ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap‖ * ‖z‖ :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.le_opNorm z

/-- Complexifying a real vector preserves its Euclidean norm. -/
theorem euclidean_norm_complex_ofReal (p : RealSpace n) :
    ‖(WithLp.toLp 2 (fun j => (p j : ℂ)) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖ := by
  simp only [EuclideanSpace.norm_eq, Complex.norm_real]

/-- The manuscript's Euclidean conormal-distance estimate follows from the
coordinate estimate by an explicit proved change of norm. -/
theorem tailoringEndpoint_exists_uniform_euclidean_annihilator_line_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ p : RealSpace n,
      ((∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, p j * v.1 j = 0) ∨
       (∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, p j * v.2 j = 0)) →
      ∃ t : ℂ,
        ‖(WithLp.toLp 2 ((fun j => (p j : ℂ)) - t • tailoringRetainedNormal I β (lgCover x)) :
          EuclideanSpace ℂ (Fin n))‖ ≤ C * Real.exp (-Real.sqrt β) *
            ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖ := by
  obtain ⟨D, hD, B, hB, hline⟩ := tailoringEndpoint_exists_uniform_annihilator_line_bound I
  let A := 1 + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap‖
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A * D, mul_pos hA hD, B, hB, fun β hβ x hx p hp => ?_⟩
  obtain ⟨t, ht⟩ := hline β hβ x hx p hp
  refine ⟨t, (complex_euclidean_norm_le_pi_norm _).trans ?_⟩
  have htransfer := mul_le_mul_of_nonneg_right
    (show ‖(EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap‖ ≤ A by
      dsimp [A]; linarith) (norm_nonneg ((fun j => (p j : ℂ)) - t • tailoringRetainedNormal I β (lgCover x)))
  apply htransfer.trans
  have hbound := mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left (real_pi_norm_le_euclidean_norm p)
      (by positivity : 0 ≤ D * Real.exp (-Real.sqrt β)))) hA.le
  simpa only [mul_assoc] using hbound

end FsFltz
