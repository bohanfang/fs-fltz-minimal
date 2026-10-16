import FsFltz.Analysis.TailoringFamily

/-!
# Nonempty tailored fibers from the positive real locus

Source: `geometric-part-fsf-proof.tex`, `eq:fs`, lines 1097–1114 and
`sec:assembly`, lines 2159–2166. A direct intermediate-value argument
replaces the open-and-closed family argument for nonemptiness alone.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Manifold ContDiff
open Set

namespace FsFltz
variable {n : ℕ}

/-- Every normalized monomial is positive real at zero angle. -/
theorem tailoring_monomial_zero_angle (β : ℝ) (v : Lattice n) (u : RealSpace n) :
    monomial (Real.exp (-β) : ℂ) v (u, 0) =
      (Real.exp (pairing v u - β) : ℂ) := by
  simp [monomial, character, integralAngle, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, ← Real.exp_add, sub_eq_add_neg, add_comm]

/-- The whole interpolating function is real on the positive real locus. -/
theorem tailoringFamily_zero_angle (I : ToricInput n) (β s : ℝ) (u : RealSpace n) :
    tailoringFamily I β s (u, 0) =
      ((s * tailoringEta I β (u, 0) * (1 - tailoringCutoff I β 0 u) +
        ∑ v ∈ I.vertices, (1 + s * tailoringEta I β (u, 0) *
          (tailoringCutoff I β v u - 1)) * Real.exp (pairing v u - β) : ℝ) : ℂ) := by
  rw [tailoringFamily_weighted_sum]
  simp only [tailoring_monomial_zero_angle]
  push_cast
  rfl

/-- At the origin the interpolating function has the same uniform small
upper bound as the uncut normalized sum. -/
theorem tailoringFamily_zero_angle_origin_le (I : ToricInput n) {β s : ℝ}
    (hβ : 0 ≤ β) (hs : s ∈ Icc (0 : ℝ) 1) :
    (tailoringFamily I β s (0, 0)).re ≤ I.vertices.card * Real.exp (-β) := by
  have hχ : tailoringCutoff I β 0 0 = 1 := by
    apply tailoringCutoff_eq_one_of_maximal
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_zero]
    simpa [pairing] using hβ
  rw [tailoringFamily_zero_angle]
  simp only [Complex.ofReal_re, hχ, sub_self, mul_zero, zero_add]
  calc
    _ ≤ ∑ _v ∈ I.vertices, Real.exp (-β) := by
      apply Finset.sum_le_sum
      intro v hv
      simp only [pairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_sub]
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        (tailoringFamily_weight_mem_Icc I β hs (0, 0) v).2
    _ = _ := by simp

/-- A large positive monomial survives tailoring and forces a large
positive real value, uniformly over the interpolation parameter. -/
theorem exists_tailoringFamily_zero_angle_ge_one (I : ToricInput n) (β : ℝ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ u : RealSpace n, 1 ≤ (tailoringFamily I β s (u, 0)).re := by
  classical
  obtain ⟨v, hv⟩ := I.vertices_nonempty
  have hvne : v ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ hv)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hvne (funext h)
  let u : RealSpace n := Pi.single j ((β + 1) / (v j : ℝ))
  have hvj : (v j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  have hpair : pairing v u = β + 1 := by
    simp only [pairing, u, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    field_simp
  obtain ⟨w, hw⟩ := I.supportHeight_attained u
  have hbig : β + 1 ≤ pairing w.val u := by
    rw [hw, ← hpair]
    exact I.pairing_le_supportHeight u ⟨v, hv⟩
  have hχ : tailoringCutoff I β w.val u = 1 := by
    apply tailoringCutoff_eq_one_of_maximal
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [tailoringWeight_zero, tailoringWeight_vertex I β w]
      linarith
    · rw [tailoringWeight_vertex I β ⟨a, ha⟩, tailoringWeight_vertex I β w, hw]
      exact sub_le_sub_right (I.pairing_le_supportHeight u ⟨a, ha⟩) β
  refine ⟨u, ?_⟩
  rw [tailoringFamily_zero_angle, Complex.ofReal_re]
  have hfirst : 0 ≤ s * tailoringEta I β (u, 0) * (1 - tailoringCutoff I β 0 u) :=
    mul_nonneg (mul_nonneg hs.1 (tailoringEta_nonneg I β _))
      (sub_nonneg.mpr (tailoringCutoff_le_one I β 0 u))
  have hsum : (1 + s * tailoringEta I β (u, 0) *
      (tailoringCutoff I β w.val u - 1)) * Real.exp (pairing w.val u - β) ≤
      ∑ a ∈ I.vertices, (1 + s * tailoringEta I β (u, 0) *
        (tailoringCutoff I β a u - 1)) * Real.exp (pairing a u - β) := Finset.single_le_sum
    (fun a (_ha : a ∈ I.vertices) => mul_nonneg
      (tailoringFamily_weight_mem_Icc I β hs (u, 0) a).1
        (Real.exp_pos (pairing a u - β)).le) w.property
  simp only [hχ, sub_self, mul_zero, add_zero, one_mul] at hsum
  have hexp : 1 ≤ Real.exp (pairing w.val u - β) :=
    Real.one_le_exp_iff.mpr (by linarith)
  linarith

/-- Every sufficiently far tailored fiber is nonempty, including rank one,
without assuming any smooth bundle or completion marking. -/
theorem tailoringFamily_exists_uniform_nonempty_fiber (I : ToricInput n) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ u : RealSpace n, tailoringFamily I β s (u, 0) = 1 := by
  let β₀ := max 1 (Real.log (I.vertices.card + 1))
  refine ⟨β₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ s hs
  have hβpos : 0 ≤ β := le_trans (by positivity) ((le_max_left _ _).trans hβ)
  have hN : (I.vertices.card : ℝ) ≤ Real.exp β := by
    have he := Real.exp_le_exp.mpr ((le_max_right _ _).trans hβ)
    rw [Real.exp_log (by positivity)] at he
    linarith
  have hsmall : (tailoringFamily I β s (0, 0)).re ≤ 1 := by
    apply (tailoringFamily_zero_angle_origin_le I hβpos hs).trans
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact hN
  obtain ⟨u, hu⟩ := exists_tailoringFamily_zero_angle_ge_one I β hs
  have hmap : Continuous (fun u : RealSpace n => (s, (u, (0 : Torus n)))) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hfamily : Continuous (fun p : ℝ × LGSpace n => tailoringFamily I β p.1 p.2) :=
    (contMDiff_tailoringFamily I β).continuous
  have hslice := hfamily.comp hmap
  have hcont := Complex.continuous_re.comp hslice
  obtain ⟨x, hx⟩ := intermediate_value_univ (0 : RealSpace n) u hcont ⟨hsmall, hu⟩
  refine ⟨x, Complex.ext hx ?_⟩
  rw [tailoringFamily_zero_angle]
  simp only [Complex.ofReal_im, Complex.one_im]

end FsFltz
