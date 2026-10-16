import FsFltz.Geometry.LocalNormalTrapping

/-!
# Local expansion for a fixed continuous bilinear metric

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1675–1700.
This version retains the normed-space structure of the actual transverse
coordinate space and uses its separately constructed bilinear metric.
The immediate consumer is the critical-torus transverse-rate estimate.
-/

noncomputable section
open Set Topology
namespace FsFltz.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Homogeneity transfers a unit-sphere bilinear bound to all vectors. -/
theorem bilinear_apply_ge_of_unit_sphere
    (G : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E) {a : ℝ}
    (hunit : ∀ u : E, ‖u‖ = 1 → a ≤ G (D u) u) (v : E) :
    a * ‖v‖ ^ 2 ≤ G (D v) v := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
  have h := mul_le_mul_of_nonneg_right (hunit u hu) (sq_nonneg ‖v‖)
  have hvu : ‖v‖ • u = v := by simp [u, smul_smul, hn]
  calc
    a * ‖v‖ ^ 2 ≤ G (D u) u * ‖v‖ ^ 2 := h
    _ = G (D (‖v‖ • u)) (‖v‖ • u) := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
    _ = G (D v) v := by rw [hvu]

/-- Integrate the normal derivative along the one segment where it is needed. -/
theorem bilinear_normal_ge_of_segment_derivative_ge (G : E →L[ℝ] E →L[ℝ] ℝ) (w : E → E) (D : E → E →L[ℝ] E)
    (v : E) (a : ℝ) (hzero : w 0 = 0)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt w (D (t • v)) (t • v))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, a * ‖v‖ ^ 2 ≤ G (D (t • v) v) v) :
    a * ‖v‖ ^ 2 ≤ G (w v) v := by
  let f : ℝ → ℝ := fun t => G (w (t • v)) v
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (G (D (t • v) v) v) t := by
    intro t ht
    have hw := (hderiv t ht).comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
    simpa only [Function.comp_def, id_eq, one_smul, f, ContinuousLinearMap.flip_apply]
      using (G.flip v).hasFDerivAt.comp_hasDerivAt t hw
  have hd : DifferentiableOn ℝ f (Icc 0 1) := fun t ht =>
    (hf t ht).differentiableAt.differentiableWithinAt
  have hslope := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    hd.continuousOn (hd.mono interior_subset)
    (fun t ht => by rw [(hf t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [f, one_smul, zero_smul, hzero, map_zero, zero_apply,
    sub_zero, mul_one] using hslope

/-- A compact zero section has an expanding tube inside any supplied local
coordinate domain; the derivative is assumed continuous only at that section. -/
theorem exists_local_bilinear_normal_expansion_tube {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) (C : Set X) (hC : IsCompact C)
    (O : Set (X × E)) (hO : IsOpen O) (hCO : C ×ˢ ({0} : Set E) ⊆ O)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, (s, y) ∈ O → HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : ∀ c ∈ C, ContinuousAt D (c, 0))
    (hzero : ∀ s, (s, 0) ∈ O → w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < G (D (c, 0) v) v) :
    ∃ a : ℝ, 0 < a ∧ ∃ U : Set (X × E), IsOpen U ∧
      C ×ˢ ({0} : Set E) ⊆ U ∧ U ⊆ O ∧
      (∀ p ∈ U, ‖p.2‖ < 1) ∧
      (∀ p ∈ U, a * ‖p.2‖ ^ 2 ≤ G (w p) p.2) := by
  let sphere : Set E := Metric.sphere (0 : E) 1
  have hsphere : IsCompact sphere := isCompact_sphere 0 1
  have hcenter : ContinuousOn (fun p : X × E => G (D (p.1, 0) p.2) p.2)
      (C ×ˢ sphere) := by
    intro p hp
    exact ((G.continuous.continuousAt.comp (((hD p.1 hp.1).comp (f := fun q : X × E => (q.1, (0 : E))) (continuousAt_fst.prodMk continuousAt_const)).clm_apply
      continuousAt_snd)).clm_apply continuousAt_snd).continuousWithinAt
  obtain ⟨b, hb, hmin⟩ := (hC.prod hsphere).exists_forall_le' hcenter
    (a := 0) (by
      rintro ⟨c, u⟩ ⟨hc, hu⟩
      apply hpos c hc u
      have hun : ‖u‖ = 1 := by simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hu
      intro heq
      simp [heq] at hun)
  have hlocal : ∀ c ∈ C, ∃ V : Set X, IsOpen V ∧ c ∈ V ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        V ×ˢ Metric.ball (0 : E) r ⊆ O ∧
        ∀ s ∈ V, ∀ y ∈ Metric.ball (0 : E) r, ∀ u : E, ‖u‖ = 1 →
          b / 2 ≤ G (D (s, y) u) u := by
    intro c hc
    have hevent : ∀ᶠ p : X × E in 𝓝 (c, 0),
        ∀ u ∈ sphere, b / 2 < G (D p u) u := by
      apply hsphere.eventually_forall_of_forall_eventually
      intro u hu
      have hquad : ContinuousAt (fun p : (X × E) × E => G (D p.1 p.2) p.2)
          ((c, 0), u) :=
        (G.continuous.continuousAt.comp ((hD c hc).comp (f := fun q : (X × E) × E => q.1) continuousAt_fst |>.clm_apply continuousAt_snd)).clm_apply continuousAt_snd
      apply continuousAt_const.eventually_lt hquad
      have h := hmin (c, u) ⟨hc, hu⟩
      dsimp only at h ⊢
      linarith
    have hboth := Filter.inter_mem
      (hO.mem_nhds (hCO (show (c, (0 : E)) ∈ C ×ˢ ({0} : Set E) from
        ⟨hc, mem_singleton 0⟩))) hevent
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hboth
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
      min r 1, lt_min hr (by norm_num), min_le_right _ _, ?_, ?_⟩
    · rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact (hVW ⟨interior_subset hs,
        hball (Metric.ball_subset_ball (min_le_left r 1) hy)⟩).1
    · intro s hs y hy u hu
      exact ((hVW ⟨interior_subset hs,
        hball (Metric.ball_subset_ball (min_le_left r 1) hy)⟩).2 u
          (by simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hu)).le
  choose V hV hcV r hr hrone hVO hbound using hlocal
  let U : Set (X × E) := ⋃ c : C, V c c.property ×ˢ Metric.ball (0 : E) (r c c.property)
  refine ⟨b / 2, by linarith, U, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun c => (hV c c.property).prod Metric.isOpen_ball
  · rintro ⟨c, y⟩ ⟨hc, hy⟩
    have hy' : y = 0 := mem_singleton_iff.mp hy
    subst y
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hcV c hc, Metric.mem_ball_self (hr c hc)⟩
  · intro p hp
    obtain ⟨c, hcp⟩ := mem_iUnion.mp hp
    exact hVO c c.property hcp
  · intro p hp
    obtain ⟨c, hcp⟩ := mem_iUnion.mp hp
    have hnorm : ‖p.2‖ < r c c.property := by
      simpa only [Metric.mem_ball, dist_zero_right] using hcp.2
    exact hnorm.trans_le (hrone c c.property)
  · intro p hp
    obtain ⟨c, hcp⟩ := mem_iUnion.mp hp
    have htv : ∀ t ∈ Icc (0 : ℝ) 1, t • p.2 ∈ Metric.ball (0 : E) (r c c.property) := by
      intro t ht
      rw [Metric.mem_ball, dist_zero_right, norm_smul_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg p.2) ht.2).trans_lt
        (by simpa only [Metric.mem_ball, dist_zero_right] using hcp.2)
    apply bilinear_normal_ge_of_segment_derivative_ge G (fun v => w (p.1, v))
      (fun v => D (p.1, v)) p.2 (b / 2)
      (hzero p.1 (hVO c c.property ⟨hcp.1, Metric.mem_ball_self (hr c c.property)⟩))
      (fun t ht => hderiv p.1 (t • p.2) (hVO c c.property ⟨hcp.1, htv t ht⟩))
    intro t ht
    exact bilinear_apply_ge_of_unit_sphere G (D (p.1, t • p.2))
      (hbound c c.property p.1 hcp.1 (t • p.2) (htv t ht)) p.2


/-- The quadratic scalar of a fixed symmetric positive bilinear form traps
bounded forward curves satisfying its strict transverse expansion estimate. -/
theorem eq_zero_of_bounded_bilinear_expansion
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, G v w = G w v)
    (hpos : ∀ v, v ≠ 0 → 0 < G v v)
    (v w : ℝ → E) {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt v (w t) t)
    (hbounded : ∀ t, 0 ≤ t → ‖v t‖ < 1)
    (hexpand : ∀ t, 0 ≤ t → a * ‖v t‖ ^ 2 ≤ G (w t) (v t)) : v 0 = 0 := by
  have hupper (z : E) : G z z ≤ ‖G‖ * ‖z‖ ^ 2 := by
    calc
      G z z ≤ ‖G z z‖ := le_abs_self _
      _ ≤ ‖G‖ * ‖z‖ * ‖z‖ := G.le_opNorm₂ z z
      _ = ‖G‖ * ‖z‖ ^ 2 := by ring
  have hnonneg (z : E) : 0 ≤ G z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  have hnorm : 0 < ‖G‖ + 1 := by positivity
  have hzero := scalar_eq_zero_of_bounded_forward_expansion
    (r := fun t => G (v t) (v t)) (q := fun t => 2 * G (w t) (v t))
    (a := 2 * a / (‖G‖ + 1)) (B := ‖G‖) (by positivity)
    (fun t ht => by
      have hh := ContinuousLinearMap.hasDerivAt_of_bilinear (B := G)
        (fun _ => hderiv t ht) (fun _ => hderiv t ht)
      convert hh using 1
      rw [hsym (v t) (w t)]
      ring)
    (fun t _ => hnonneg (v t))
    (fun t ht => (hupper _).trans (by
      have hb := hbounded t ht
      have hn := norm_nonneg (v t)
      have hsq : ‖v t‖ ^ 2 ≤ 1 := by nlinarith
      simpa using mul_le_mul_of_nonneg_left hsq (norm_nonneg G)))
    (fun t ht => by
      have hu : G (v t) (v t) ≤ (‖G‖ + 1) * ‖v t‖ ^ 2 :=
        (hupper _).trans (by nlinarith [sq_nonneg ‖v t‖])
      have he := hexpand t ht
      have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * a / (‖G‖ + 1) by positivity)
      have hc : (2 * a / (‖G‖ + 1)) * ((‖G‖ + 1) * ‖v t‖ ^ 2) =
          2 * (a * ‖v t‖ ^ 2) := by field_simp
      rw [hc] at hm
      exact hm.trans (by linarith))
  by_contra hv
  exact (hpos _ hv).ne' hzero

/-- The actual derivative of a local normal field constructs a trapping
tube for the fixed metric, without changing normed-space instances. -/
theorem exists_local_bilinear_normal_trapping_tube {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, G v w = G w v) (hmetric : ∀ v, v ≠ 0 → 0 < G v v)
    (C : Set X) (hC : IsCompact C)
    (O : Set (X × E)) (hO : IsOpen O) (hCO : C ×ˢ ({0} : Set E) ⊆ O)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, (s, y) ∈ O → HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : ∀ c ∈ C, ContinuousAt D (c, 0))
    (hzero : ∀ s, (s, 0) ∈ O → w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < G (D (c, 0) v) v) :
    ∃ U : Set (X × E), IsOpen U ∧ C ×ˢ ({0} : Set E) ⊆ U ∧ U ⊆ O ∧
      ∀ γ : ℝ → X × E, (∀ t, 0 ≤ t → γ t ∈ U) →
        (∀ t, 0 ≤ t → HasDerivAt (fun s => (γ s).2) (w (γ t)) t) →
        (γ 0).2 = 0 := by
  obtain ⟨a, ha, U, hU, hCU, hUO, hb, he⟩ :=
    exists_local_bilinear_normal_expansion_tube G C hC O hO hCO w D hderiv hD hzero hpos
  refine ⟨U, hU, hCU, hUO, ?_⟩
  intro γ hγ hd
  exact eq_zero_of_bounded_bilinear_expansion G hsym hmetric
    (fun t => (γ t).2) (fun t => w (γ t)) ha hd
    (fun t ht => hb _ (hγ t ht)) (fun t ht => he _ (hγ t ht))

/-- Point-local estimates for the same nonnegative scalar have one positive
coefficient on a neighborhood of a compact set. No product coordinates need
to be identified on overlaps. -/
theorem compact_uniform_local_expansion {M : Type*} [TopologicalSpace M]
    (C : Set M) (hC : IsCompact C) (ρ Q : M → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x)
    (hlocal : ∀ c ∈ C, ∃ a : ℝ, 0 < a ∧ ∃ U : Set M,
      IsOpen U ∧ c ∈ U ∧ ∀ x ∈ U, a * ρ x ≤ Q x) :
    ∃ a : ℝ, 0 < a ∧ ∃ U : Set M, IsOpen U ∧ C ⊆ U ∧
      ∀ x ∈ U, a * ρ x ≤ Q x := by
  classical
  choose a ha U hU hcU hbound using hlocal
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : C => U c c.property) (fun c => hU c c.property) (by
      intro c hc
      exact mem_iUnion.mpr ⟨⟨c, hc⟩, hcU c hc⟩)
  let A : Set ℝ := (fun c : C => a c c.property) '' (↑t : Set C)
  have hA : IsCompact A := (t.finite_toSet.image _).isCompact
  obtain ⟨b, hb, hbA⟩ := hA.exists_forall_le' continuous_id.continuousOn (a := 0) (by
    rintro _ ⟨c, _, rfl⟩
    exact ha c c.property)
  refine ⟨b, hb, ⋃ c ∈ t, U c c.property,
    isOpen_iUnion (fun c => isOpen_iUnion (fun _ => hU c c.property)), ht, ?_⟩
  intro x hx
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp hx
  exact (mul_le_mul_of_nonneg_right (hbA _ ⟨c, hct, rfl⟩) (hρ x)).trans
    (hbound c c.property x hxc)

/-- Local inequalities for one defining map and one rate construct a common
trapping neighborhood of a compact zero set. Local coordinate systems are
used only to prove the inequalities and need not agree on their overlaps. -/
theorem exists_compact_bilinear_trapping_neighborhood
    {M : Type*} [TopologicalSpace M]
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, G v w = G w v) (hmetric : ∀ v, v ≠ 0 → 0 < G v v)
    (C : Set M) (hC : IsCompact C) (δ R : M → E)
    (hδ : ∀ c ∈ C, ContinuousAt δ c) (hzero : ∀ c ∈ C, δ c = 0)
    (hlocal : ∀ c ∈ C, ∃ a : ℝ, 0 < a ∧ ∃ U : Set M,
      IsOpen U ∧ c ∈ U ∧ ∀ x ∈ U, a * ‖δ x‖ ^ 2 ≤ G (R x) (δ x)) :
    ∃ U : Set M, IsOpen U ∧ C ⊆ U ∧
      ∀ γ : ℝ → M, (∀ t, 0 ≤ t → γ t ∈ U) →
        (∀ t, 0 ≤ t → HasDerivAt (δ ∘ γ) (R (γ t)) t) → δ (γ 0) = 0 := by
  obtain ⟨a, ha, V, hV, hCV, he⟩ := compact_uniform_local_expansion C hC
    (fun x => ‖δ x‖ ^ 2) (fun x => G (R x) (δ x))
    (fun x => sq_nonneg _) hlocal
  let O : Set M := interior (δ ⁻¹' Metric.ball 0 1)
  have hCO : C ⊆ O := by
    intro c hc
    apply mem_interior_iff_mem_nhds.mpr
    apply (hδ c hc).preimage_mem_nhds
    rw [hzero c hc]
    exact Metric.ball_mem_nhds _ (by norm_num)
  refine ⟨V ∩ O, hV.inter isOpen_interior, fun c hc => ⟨hCV hc, hCO hc⟩, ?_⟩
  intro γ hγ hd
  exact eq_zero_of_bounded_bilinear_expansion G hsym hmetric (δ ∘ γ)
    (fun t => R (γ t)) ha hd (fun t ht => by
      have hm : δ (γ t) ∈ Metric.ball 0 1 := (interior_subset (s := δ ⁻¹' Metric.ball 0 1)) (hγ t ht).2
      simpa only [Metric.mem_ball, dist_zero_right, Function.comp_apply] using hm)
    (fun t ht => he _ (hγ t ht).1)

end FsFltz.Geometry
