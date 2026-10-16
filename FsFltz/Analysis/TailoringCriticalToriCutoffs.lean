import FsFltz.Analysis.TailoringCriticalHolomorphic
import FsFltz.Analysis.TailoringCriticalToriAsymptotics

/-!
# Exact cutoff plateaus along reconstructed face branches

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1526–1528.
A bounded displacement from a dilated relative-interior polar-face point
forces precisely the desired active and inactive cutoffs, on an actual
open neighborhood. This supplies the forward direction needed when
reconstructing critical points from the reduced equations.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped Topology BigOperators

private theorem eventually_linear_deficit_lt_sqrt (C : ℝ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ β : ℝ in atTop, C - β * d < -Real.sqrt β - 2 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 / d)),
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (C + 2))]
    with β hβ hlarge hC
  have htwo : 2 ≤ d * Real.sqrt β := by
    exact (div_le_iff₀ hd).mp hlarge |>.trans_eq (mul_comm _ _)
  have hm := mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg β)
  have he := congrArg (fun t : ℝ => d * t) (Real.sq_sqrt hβ)
  nlinarith

variable {n : ℕ}

/-- Uniform bounded displacement controls all finite face pairings. -/
theorem eventually_bounded_face_pairing_errors (I : ToricInput n)
    {u : ℝ → RealSpace n} {x : RealSpace n} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ β : ℝ in atTop, ‖u β - β • x‖ ≤ C) :
    ∃ D ≥ 0, ∀ᶠ β : ℝ in atTop, ∀ v ∈ I.vertices,
      |pairing v (u β) - β * pairing v x| ≤ D := by
  classical
  let D := (∑ v ∈ I.vertices, ‖pairingCLM v‖) * C
  refine ⟨D, mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC, ?_⟩
  filter_upwards [hbound] with β hβ v hv
  have hnorm := (pairingCLM v).le_opNorm (u β - β • x)
  have he : pairing v (u β) - β * pairing v x =
      pairingCLM v (u β - β • x) := by
    rw [map_sub, map_smul]
    simp
  rw [he, ← Real.norm_eq_abs]
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hβ (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun v _ => norm_nonneg (pairingCLM v)) hv) hC))

/-- A bounded error from a dilated relative-interior polar-face point
gives all strict plateau gaps simultaneously. -/
theorem eventually_tailoring_strict_gaps_of_pairing_errors (I : ToricInput n)
    {s : Finset (Lattice n)} {x : RealSpace n}
    (hface : ∀ v ∈ I.vertices, if v ∈ s then pairing v x = 1 else pairing v x < 1)
    {u : ℝ → RealSpace n} {C : ℝ} (hC : 0 ≤ C)
    (herror : ∀ᶠ β : ℝ in atTop, ∀ v ∈ I.vertices,
      |pairing v (u β) - β * pairing v x| ≤ C) :
    ∀ᶠ β : ℝ in atTop, ∀ a ∈ tailoringExponents I,
      if a = 0 ∨ a ∈ s then
        tailoringMaxWeight I β (u β) - Real.sqrt β < tailoringWeight β a (u β)
      else
        tailoringWeight β a (u β) < tailoringMaxWeight I β (u β) - Real.sqrt β - 2 := by
  classical
  have hnegative : ∀ᶠ β : ℝ in atTop, ∀ v ∈ I.vertices,
      v ∉ s → C - β * (1 - pairing v x) < -Real.sqrt β - 2 := by
    apply (eventually_all_finite I.vertices.finite_toSet).mpr
    intro v hv
    by_cases hs : v ∈ s
    · exact Eventually.of_forall fun _ h => (h hs).elim
    · have hp : pairing v x < 1 := by simpa [hs] using hface v hv
      filter_upwards [eventually_linear_deficit_lt_sqrt C (sub_pos.mpr hp)] with β hβ
      exact fun _ => hβ
  filter_upwards [herror, hnegative, eventually_ge_atTop (0 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (2 * C))]
    with β he hn hβ hsqrt a ha
  have hweight (v : Lattice n) (hv : v ∈ I.vertices) :
      tailoringWeight β v (u β) ≤ C := by
    have hp : pairing v x ≤ 1 := by
      by_cases hs : v ∈ s
      · exact le_of_eq (by simpa [hs] using hface v hv)
      · exact le_of_lt (by simpa [hs] using hface v hv)
    rw [tailoringWeight_vertex I β ⟨v, hv⟩]
    have hh := (abs_le.mp (he v hv)).2
    have hm := mul_le_mul_of_nonneg_left hp hβ
    linarith
  have hmax : tailoringMaxWeight I β (u β) ≤ C := by
    obtain ⟨v, hv, hvmax⟩ := tailoringMaxWeight_attained I β (u β)
    rw [← hvmax]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simpa using hC
    · exact hweight v hv
  have hmax0 : 0 ≤ tailoringMaxWeight I β (u β) := le_max_left _ _
  split_ifs with hactive
  · rcases hactive with rfl | has
    · rw [tailoringWeight_zero]
      linarith
    · by_cases ha0 : a = 0
      · subst a
        rw [tailoringWeight_zero]
        linarith
      · have hav : a ∈ I.vertices := (Finset.mem_insert.mp ha).resolve_left ha0
        have hp : pairing a x = 1 := by simpa [has] using hface a hav
        have hl := (abs_le.mp (he a hav)).1
        rw [hp, mul_one] at hl
        rw [tailoringWeight_vertex I β ⟨a, hav⟩]
        linarith
  · have ha0 : a ≠ 0 := fun h => hactive (Or.inl h)
    have has : a ∉ s := fun h => hactive (Or.inr h)
    have hav : a ∈ I.vertices := (Finset.mem_insert.mp ha).resolve_left ha0
    have hl := (abs_le.mp (he a hav)).2
    have hh := hn a hav has
    rw [tailoringWeight_vertex I β ⟨a, hav⟩]
    nlinarith

/-- The cutoff values are exact on an open neighborhood, not merely at
the reconstructed point. -/
theorem eventually_tailoring_face_plateau_neighborhood (I : ToricInput n)
    {s : Finset (Lattice n)} {x : RealSpace n}
    (hface : ∀ v ∈ I.vertices, if v ∈ s then pairing v x = 1 else pairing v x < 1)
    {u : ℝ → RealSpace n} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ β : ℝ in atTop, ‖u β - β • x‖ ≤ C) :
    ∀ᶠ β : ℝ in atTop, ∃ U : Set (RealSpace n), IsOpen U ∧ u β ∈ U ∧
      ∀ w ∈ U, ∀ a ∈ tailoringExponents I,
        tailoringCutoff I β a w = if a = 0 ∨ a ∈ s then 1 else 0 := by
  classical
  obtain ⟨D, hD, he⟩ := eventually_bounded_face_pairing_errors I hC hbound
  filter_upwards [eventually_tailoring_strict_gaps_of_pairing_errors I hface hD he]
    with β hβ
  have hgap : ∀ a ∈ tailoringExponents I,
      tailoringWeight β a (u β) < tailoringMaxWeight I β (u β) - Real.sqrt β - 2 ∨
      tailoringMaxWeight I β (u β) - Real.sqrt β < tailoringWeight β a (u β) := by
    intro a ha
    have hh := hβ a ha
    split_ifs at hh with h
    · exact Or.inr hh
    · exact Or.inl hh
  obtain ⟨U, hU, hu, hconstant⟩ :=
    tailoringCutoffs_exists_open_constant_of_strict_gaps I β (u β) hgap
  refine ⟨U, hU, hu, fun w hw a ha => ?_⟩
  rw [hconstant w hw a ha]
  have hh := hβ a ha
  split_ifs with h
  · simp only [h, ↓reduceIte] at hh
    apply tailoringCutoff_eq_one_of_gap
    intro b hb
    exact (sub_le_sub_right (tailoringWeight_le_max I β b hb (u β)) _).trans hh.le
  · simp only [h, ↓reduceIte] at hh
    exact tailoringCutoff_eq_zero_of_strict_deficit I β a (u β) hh

/-- Apply the bounded radial reconstruction directly to the smooth
constrained-minimum and reduced-weight maps used in the critical equations. -/
theorem critical_reduced_branch_eventually_face_plateaus
    (I : ToricInput n) {ι : Type*} [Fintype ι]
    {s : Finset (Lattice n)} {x : (ι → ℝ) → RealSpace n}
    (hx : DifferentiableAt ℝ x 0)
    (hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1)
    {q : ℝ → (ι → ℝ)} (hq : DifferentiableAt ℝ q 0)
    (hpositive : ∀ i, 0 < q 0 i) :
    ∀ᶠ β : ℝ in atTop, ∃ U : Set (RealSpace n), IsOpen U ∧
      β • x (β⁻¹ • (fun i => Real.log (q β⁻¹ i))) ∈ U ∧
      ∀ w ∈ U, ∀ a ∈ tailoringExponents I,
        tailoringCutoff I β a w = if a = 0 ∨ a ∈ s then 1 else 0 := by
  obtain ⟨C, hC, hb⟩ := (critical_radial_displacement hx hq hpositive).1
  exact eventually_tailoring_face_plateau_neighborhood I hface hC.le hb

end FsFltz
