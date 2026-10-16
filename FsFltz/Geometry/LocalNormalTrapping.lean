import FsFltz.Geometry.NormalExpansionTrapping

/-!
# Normal trapping inside local coordinates

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1661–1701.
The normal field and its derivative are required only on an open coordinate
neighborhood. Curves need satisfy the normal equation only at nonnegative
times, so no globally conjugated product flow is assumed. The construction
of normal coordinates for the actual critical tori is a separate producer.
-/

noncomputable section
open Set Topology
namespace FsFltz.Geometry

/-- The scalar expansion argument only uses derivatives at forward times. -/
theorem scalar_eq_zero_of_bounded_forward_expansion {r q : ℝ → ℝ} {a B : ℝ}
    (ha : 0 < a) (hderiv : ∀ t, 0 ≤ t → HasDerivAt r (q t) t)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hbounded : ∀ t, 0 ≤ t → r t ≤ B)
    (hexpand : ∀ t, 0 ≤ t → a * r t ≤ q t) : r 0 = 0 := by
  have hd : DifferentiableOn ℝ r (Ici 0) := fun t ht =>
    (hderiv t ht).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn r (Ici 0) := hd.continuousOn
  have hm : MonotoneOn r (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont (hd.mono interior_subset) fun t ht => by
      have ht' : 0 ≤ t := interior_subset ht
      rw [(hderiv t ht').deriv]
      exact (mul_nonneg ha.le (hnonneg t ht')).trans (hexpand t ht')
  apply le_antisymm _ (hnonneg 0 le_rfl)
  by_contra hzero
  have hr : 0 < r 0 := lt_of_not_ge hzero
  have hc : 0 < a * r 0 := mul_pos ha hr
  let T : ℝ := (B - r 0 + 1) / (a * r 0)
  have hT : 0 < T := div_pos (by have := hbounded 0 le_rfl; linarith) hc
  have hlow : ∀ t ∈ interior (Ici (0 : ℝ)), a * r 0 ≤ deriv r t := by
    intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    rw [(hderiv t ht').deriv]
    exact (mul_le_mul_of_nonneg_left (hm (by simp) ht' ht') ha.le).trans
      (hexpand t ht')
  have hslope := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hcont (hd.mono interior_subset) hlow 0 (by simp) T hT.le hT.le
  have hmul : (a * r 0) * T = B - r 0 + 1 := by
    dsimp only [T]
    exact mul_div_cancel₀ _ hc.ne'
  simp only [sub_zero] at hslope
  rw [hmul] at hslope
  have := hbounded T hT.le
  linarith

section NormalCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrate the normal derivative along the one segment where it is needed. -/
theorem inner_normal_ge_of_segment_derivative_ge (w : E → E) (D : E → E →L[ℝ] E)
    (v : E) (a : ℝ) (hzero : w 0 = 0)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt w (D (t • v)) (t • v))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, a * ‖v‖ ^ 2 ≤ inner ℝ (D (t • v) v) v) :
    a * ‖v‖ ^ 2 ≤ inner ℝ (w v) v := by
  let f : ℝ → ℝ := fun t => inner ℝ (w (t • v)) v
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (inner ℝ (D (t • v) v) v) t := by
    intro t ht
    have hw := (hderiv t ht).comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
    simpa only [Function.comp_def, id_eq, one_smul, f, inner_zero_right, zero_add]
      using hw.inner ℝ (hasDerivAt_const t v)
  have hd : DifferentiableOn ℝ f (Icc 0 1) := fun t ht =>
    (hf t ht).differentiableAt.differentiableWithinAt
  have hslope := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    hd.continuousOn (hd.mono interior_subset)
    (fun t ht => by rw [(hf t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [f, one_smul, zero_smul, hzero, inner_zero_left,
    sub_zero, mul_one] using hslope

/-- A compact zero section has an expanding tube inside any supplied local
coordinate domain; the derivative is assumed continuous only at that section. -/
theorem exists_local_normal_expansion_tube {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (C : Set X) (hC : IsCompact C)
    (O : Set (X × E)) (hO : IsOpen O) (hCO : C ×ˢ ({0} : Set E) ⊆ O)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, (s, y) ∈ O → HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : ∀ c ∈ C, ContinuousAt D (c, 0))
    (hzero : ∀ s, (s, 0) ∈ O → w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < inner ℝ (D (c, 0) v) v) :
    ∃ a : ℝ, 0 < a ∧ ∃ U : Set (X × E), IsOpen U ∧
      C ×ˢ ({0} : Set E) ⊆ U ∧ U ⊆ O ∧
      (∀ p ∈ U, ‖p.2‖ < 1) ∧
      (∀ p ∈ U, a * ‖p.2‖ ^ 2 ≤ inner ℝ (w p) p.2) := by
  let sphere : Set E := Metric.sphere (0 : E) 1
  have hsphere : IsCompact sphere := isCompact_sphere 0 1
  have hcenter : ContinuousOn (fun p : X × E => inner ℝ (D (p.1, 0) p.2) p.2)
      (C ×ˢ sphere) := by
    intro p hp
    exact (((hD p.1 hp.1).comp (f := fun q : X × E => (q.1, (0 : E))) (continuousAt_fst.prodMk continuousAt_const)).clm_apply
      continuousAt_snd |>.inner continuousAt_snd).continuousWithinAt
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
          b / 2 ≤ inner ℝ (D (s, y) u) u := by
    intro c hc
    have hevent : ∀ᶠ p : X × E in 𝓝 (c, 0),
        ∀ u ∈ sphere, b / 2 < inner ℝ (D p u) u := by
      apply hsphere.eventually_forall_of_forall_eventually
      intro u hu
      have hquad : ContinuousAt (fun p : (X × E) × E => inner ℝ (D p.1 p.2) p.2)
          ((c, 0), u) :=
        ((hD c hc).comp (f := fun q : (X × E) × E => q.1) continuousAt_fst |>.clm_apply continuousAt_snd).inner continuousAt_snd
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
    apply inner_normal_ge_of_segment_derivative_ge (fun v => w (p.1, v))
      (fun v => D (p.1, v)) p.2 (b / 2)
      (hzero p.1 (hVO c c.property ⟨hcp.1, Metric.mem_ball_self (hr c c.property)⟩))
      (fun t ht => hderiv p.1 (t • p.2) (hVO c c.property ⟨hcp.1, htv t ht⟩))
    intro t ht
    exact inner_apply_ge_of_unit_sphere (D (p.1, t • p.2))
      (hbound c c.property p.1 hcp.1 (t • p.2) (htv t ht)) p.2

/-- The local derivative produces a trapping neighborhood for every forward
curve satisfying the normal equation there. No field, derivative, or flow
equation is required outside the coordinate domain. -/
theorem exists_local_normal_trapping_tube {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (C : Set X) (hC : IsCompact C)
    (O : Set (X × E)) (hO : IsOpen O) (hCO : C ×ˢ ({0} : Set E) ⊆ O)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, (s, y) ∈ O → HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : ∀ c ∈ C, ContinuousAt D (c, 0))
    (hzero : ∀ s, (s, 0) ∈ O → w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < inner ℝ (D (c, 0) v) v) :
    ∃ U : Set (X × E), IsOpen U ∧ C ×ˢ ({0} : Set E) ⊆ U ∧ U ⊆ O ∧
      ∀ γ : ℝ → X × E, (∀ t, 0 ≤ t → γ t ∈ U) →
        (∀ t, 0 ≤ t → HasDerivAt (fun s => (γ s).2) (w (γ t)) t) →
        (γ 0).2 = 0 := by
  obtain ⟨a, ha, U, hU, hCU, hUO, hbounded, hexpand⟩ :=
    exists_local_normal_expansion_tube C hC O hO hCO w D hderiv hD hzero hpos
  refine ⟨U, hU, hCU, hUO, ?_⟩
  intro γ hγ hsolves
  have hz := scalar_eq_zero_of_bounded_forward_expansion
    (a := 2 * a) (B := 1) (by positivity)
    (fun t ht => (hsolves t ht).norm_sq)
    (fun t _ => sq_nonneg ‖(γ t).2‖)
    (fun t ht => by have := hbounded _ (hγ t ht); nlinarith [norm_nonneg (γ t).2])
    (fun t ht => by
      have he := hexpand _ (hγ t ht)
      have hic : inner ℝ (w (γ t)) (γ t).2 = inner ℝ (γ t).2 (w (γ t)) :=
        real_inner_comm _ _
      rw [hic] at he
      linarith)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (γ 0).2])

/-- Application to local coordinates of a native flow. Only the normal
coordinate needs a derivative, at the times when the orbit is in the tube. -/
theorem flowCore_preimage_subset_zero_of_local_normal_trapping
    {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    (F : Flow ℝ M) (κ : M → X × E) (w : X × E → E) (U : Set (X × E))
    (htrap : ∀ γ : ℝ → X × E, (∀ t, 0 ≤ t → γ t ∈ U) →
      (∀ t, 0 ≤ t → HasDerivAt (fun s => (γ s).2) (w (γ t)) t) → (γ 0).2 = 0)
    (hsolves : ∀ x t, κ (F t x) ∈ U →
      HasDerivAt (fun s => (κ (F s x)).2) (w (κ (F t x))) t) :
    flowCore F (κ ⁻¹' U) ⊆ {x | (κ x).2 = 0} := by
  intro x hx
  have hz := htrap (fun t => κ (F t x)) (fun t ht => hx t ht)
    (fun t ht => hsolves x t (hx t ht))
  simpa only [Flow.map_zero_apply, mem_ofPred_eq] using hz

end NormalCoordinates
end FsFltz.Geometry
