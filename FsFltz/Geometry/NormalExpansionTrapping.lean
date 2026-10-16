import FsFltz.Core
import FsFltz.Geometry.FlowAbsorption
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Normal expansion and forward trapping

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1661–1694.
The scalar and radial estimates below use actual derivatives, and their
consumers use the all-forward-real-time core of the same complete flow.
The normal-coordinate result uses a fixed inner product on a trivial normal
bundle. Construction of tubular coordinates for an embedded invariant branch
and control of varying-metric terms remain separate geometric obligations;
this module does not assert `lem:stable` or the full endpoint core equality.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- A bounded nonnegative scalar with a strictly expanding differential
inequality must start at zero. The lower bound follows from mean-value
inequalities, so no exponential comparison is assumed. -/
theorem scalar_eq_zero_of_bounded_expansion {r q : ℝ → ℝ} {a B : ℝ}
    (ha : 0 < a) (hderiv : ∀ t, HasDerivAt r (q t) t)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hbounded : ∀ t, 0 ≤ t → r t ≤ B)
    (hexpand : ∀ t, 0 ≤ t → a * r t ≤ q t) : r 0 = 0 := by
  have hd : Differentiable ℝ r := fun t => (hderiv t).differentiableAt
  have hm : MonotoneOn r (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hd.continuous.continuousOn
      hd.differentiableOn fun t ht => by
        rw [(hderiv t).deriv]
        have ht' : 0 ≤ t := interior_subset ht
        exact (mul_nonneg ha.le (hnonneg t ht')).trans (hexpand t ht')
  apply le_antisymm _ (hnonneg 0 le_rfl)
  by_contra hzero
  have hr : 0 < r 0 := lt_of_not_ge hzero
  have hc : 0 < a * r 0 := mul_pos ha hr
  let T : ℝ := (B - r 0 + 1) / (a * r 0)
  have hT : 0 < T := div_pos (by have := hbounded 0 le_rfl; linarith) hc
  have hlow : ∀ t ∈ interior (Ici (0 : ℝ)), a * r 0 ≤ deriv r t := by
    intro t ht
    rw [(hderiv t).deriv]
    have ht' : 0 ≤ t := interior_subset ht
    exact (mul_le_mul_of_nonneg_left (hm (by simp) ht' ht') ha.le).trans
      (hexpand t ht')
  have hslope := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hlow
    0 (by simp) T hT.le hT.le
  have hmul : (a * r 0) * T = B - r 0 + 1 := by
    dsimp only [T]
    exact mul_div_cancel₀ _ hc.ne'
  simp only [sub_zero] at hslope
  rw [hmul] at hslope
  have := hbounded T hT.le
  linarith

namespace CompleteLiouvilleFlow

/-- The intrinsic scalar derivative along the actual complete flow forces
the all-real-forward core into its zero set. -/
theorem flowCore_subset_zero_of_expansion {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    {U : Set M.Point} {a B : ℝ} (ha : 0 < a)
    (hnonneg : ∀ x ∈ U, 0 ≤ ρ x) (hbounded : ∀ x ∈ U, ρ x ≤ B)
    (hexpand : ∀ x ∈ U, a * ρ x ≤ M.scalarDerivative ρ x (Z x)) :
    flowCore F.flow U ⊆ {x | ρ x = 0} := by
  intro x hx
  have hzero := scalar_eq_zero_of_bounded_expansion ha
    (F.hasDerivAt_scalar_orbit ρ hρ x)
    (fun t ht => hnonneg _ (hx t ht))
    (fun t ht => hbounded _ (hx t ht))
    (fun t ht => hexpand _ (hx t ht))
  simpa only [Flow.map_zero_apply, mem_ofPred_eq] using hzero

end CompleteLiouvilleFlow

section NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A lower bound on the actual normal derivative, integrated along the
radial segment using the mean-value inequality. -/
theorem inner_normal_ge_of_derivative_ge (w : E → E) (D : E → E →L[ℝ] E)
    (hderiv : ∀ y, HasFDerivAt w (D y) y) (hzero : w 0 = 0)
    (v : E) (a : ℝ)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, a * ‖v‖ ^ 2 ≤ inner ℝ (D (t • v) v) v) :
    a * ‖v‖ ^ 2 ≤ inner ℝ (w v) v := by
  let f : ℝ → ℝ := fun t => inner ℝ (w (t • v)) v
  have hf : ∀ t, HasDerivAt f (inner ℝ (D (t • v) v) v) t := by
    intro t
    have hw := (hderiv (t • v)).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const v)
    simpa only [Function.comp_def, id_eq, one_smul, f, inner_zero_right, zero_add]
      using hw.inner ℝ (hasDerivAt_const t v)
  have hd : Differentiable ℝ f := fun t => (hf t).differentiableAt
  have hslope := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn
    (fun t ht => by rw [(hf t).deriv]; exact hpos t (interior_subset ht))
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [f, one_smul, zero_smul, hzero, inner_zero_left,
    sub_zero, mul_one] using hslope

/-- Coercivity on the unit sphere extends to every normal vector, including
the zero-dimensional normal space. -/
theorem inner_apply_ge_of_unit_sphere (D : E →L[ℝ] E) {a : ℝ}
    (hunit : ∀ u : E, ‖u‖ = 1 → a ≤ inner ℝ (D u) u) (v : E) :
    a * ‖v‖ ^ 2 ≤ inner ℝ (D v) v := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
  have h := mul_le_mul_of_nonneg_right (hunit u hu) (sq_nonneg ‖v‖)
  have hvu : v = ‖v‖ • u := by
    simp [u, smul_smul, hn]
  calc
    a * ‖v‖ ^ 2 ≤ inner ℝ (D u) u * ‖v‖ ^ 2 := h
    _ = inner ℝ (D v) v := by
      have hpair : inner ℝ (D v) v =
          inner ℝ (D (‖v‖ • u)) (‖v‖ • u) := congrArg (fun z => inner ℝ (D z) z) hvu
      rw [hpair, D.map_smul ‖v‖ u,
        real_inner_smul_left (D u) (‖v‖ • u) ‖v‖,
        real_inner_smul_right (D u) u ‖v‖]
      ring

/-- Compact strict positivity of the true normal derivative constructs a
bounded open tube and its radial expansion estimate. The base is arbitrary;
only the normal fibers are finite-dimensional inner-product spaces. -/
theorem exists_normal_expansion_tube {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (C : Set X) (hC : IsCompact C)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : Continuous D) (hzero : ∀ s, w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < inner ℝ (D (c, 0) v) v) :
    ∃ a : ℝ, 0 < a ∧ ∃ U : Set (X × E), IsOpen U ∧
      C ×ˢ ({0} : Set E) ⊆ U ∧
      (∀ p ∈ U, ‖p.2‖ < 1) ∧
      (∀ p ∈ U, a * ‖p.2‖ ^ 2 ≤ inner ℝ (w p) p.2) := by
  let sphere : Set E := Metric.sphere (0 : E) 1
  have hsphere : IsCompact sphere := isCompact_sphere 0 1
  have hquad : Continuous (fun p : (X × E) × E => inner ℝ (D p.1 p.2) p.2) :=
    ((hD.comp continuous_fst).clm_apply continuous_snd).inner continuous_snd
  have hcenter : Continuous (fun p : X × E => inner ℝ (D (p.1, 0) p.2) p.2) :=
    (hD.comp (continuous_fst.prodMk continuous_const) |>.clm_apply continuous_snd).inner
      continuous_snd
  obtain ⟨b, hb, hmin⟩ := (hC.prod hsphere).exists_forall_le' hcenter.continuousOn
    (a := 0) (by
      rintro ⟨c, u⟩ ⟨hc, hu⟩
      apply hpos c hc u
      have hun : ‖u‖ = 1 := by simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hu
      intro heq
      simp [heq] at hun)
  have hlocal : ∀ c ∈ C, ∃ V : Set X, IsOpen V ∧ c ∈ V ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        ∀ s ∈ V, ∀ y ∈ Metric.ball (0 : E) r, ∀ u : E, ‖u‖ = 1 →
          b / 2 ≤ inner ℝ (D (s, y) u) u := by
    intro c hc
    have hevent : ∀ᶠ p : X × E in 𝓝 (c, 0),
        ∀ u ∈ sphere, b / 2 < inner ℝ (D p u) u := by
      apply hsphere.eventually_forall_of_forall_eventually
      intro u hu
      apply continuousAt_const.eventually_lt hquad.continuousAt
      have h := hmin (c, u) ⟨hc, hu⟩
      dsimp only at h ⊢
      linarith
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hevent
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
      min r 1, lt_min hr (by norm_num), min_le_right _ _, ?_⟩
    intro s hs y hy u hu
    exact (hVW ⟨interior_subset hs,
      hball (Metric.ball_subset_ball (min_le_left r 1) hy)⟩ u
        (by simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hu)).le
  choose V hV hcV r hr hrone hbound using hlocal
  let U : Set (X × E) := ⋃ c : C, V c c.property ×ˢ Metric.ball (0 : E) (r c c.property)
  refine ⟨b / 2, by linarith, U, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun c => (hV c c.property).prod Metric.isOpen_ball
  · rintro ⟨c, y⟩ ⟨hc, hy⟩
    have hy' : y = 0 := mem_singleton_iff.mp hy
    subst y
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hcV c hc,
      Metric.mem_ball_self (hr c hc)⟩
  · intro p hp
    obtain ⟨c, hcp⟩ := mem_iUnion.mp hp
    have hnorm : ‖p.2‖ < r c c.property := by
      simpa only [Metric.mem_ball, dist_zero_right] using hcp.2
    exact hnorm.trans_le (hrone c c.property)
  · intro p hp
    obtain ⟨c, hcp⟩ := mem_iUnion.mp hp
    apply inner_normal_ge_of_derivative_ge (fun v => w (p.1, v))
      (fun v => D (p.1, v)) (hderiv p.1) (hzero p.1) p.2 (b / 2)
    intro t ht
    have htv : t • p.2 ∈ Metric.ball (0 : E) (r c c.property) := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg p.2) ht.2).trans_lt
        (by simpa only [Metric.mem_ball, dist_zero_right] using hcp.2)
    exact inner_apply_ge_of_unit_sphere (D (p.1, t • p.2))
      (hbound c c.property p.1 hcp.1 (t • p.2) htv) p.2

/-- The constructed tube traps every full forward orbit of a flow whose
normal coordinate solves the specified normal field. Positivity and the
tube are both supplied by the actual normal derivative, rather than by a
trapping hypothesis. -/
theorem exists_normal_trapping_neighborhood {X : Type*} [TopologicalSpace X]
    [FiniteDimensional ℝ E] (C : Set X) (hC : IsCompact C)
    (w : X × E → E) (D : X × E → E →L[ℝ] E)
    (hderiv : ∀ s y, HasFDerivAt (fun v => w (s, v)) (D (s, y)) y)
    (hD : Continuous D) (hzero : ∀ s, w (s, 0) = 0)
    (hpos : ∀ c ∈ C, ∀ v : E, v ≠ 0 → 0 < inner ℝ (D (c, 0) v) v)
    (F : Flow ℝ (X × E))
    (hsolves : ∀ p t, HasDerivAt (fun s => (F s p).2) (w (F t p)) t) :
    ∃ U : Set (X × E), IsOpen U ∧ C ×ˢ ({0} : Set E) ⊆ U ∧
      flowCore F U ⊆ (univ : Set X) ×ˢ ({0} : Set E) := by
  obtain ⟨a, ha, U, hU, hCU, hbounded, hexpand⟩ :=
    exists_normal_expansion_tube C hC w D hderiv hD hzero hpos
  refine ⟨U, hU, hCU, ?_⟩
  intro p hp
  have hzero := scalar_eq_zero_of_bounded_expansion (a := 2 * a) (by positivity)
    (fun t => (hsolves p t).norm_sq)
    (fun t _ => sq_nonneg ‖(F t p).2‖)
    (B := 1) (fun t ht => by
      have hb := hbounded _ (hp t ht)
      nlinarith [norm_nonneg (F t p).2])
    (fun t ht => by
      have he := hexpand _ (hp t ht)
      have hic : inner ℝ (w (F t p)) (F t p).2 =
          inner ℝ (F t p).2 (w (F t p)) := real_inner_comm _ _
      rw [hic] at he
      linarith)
  have hnorm : ‖p.2‖ = 0 := by
    have he : ‖p.2‖ ^ 2 = 0 := by simpa only [Flow.map_zero_apply] using hzero
    nlinarith [norm_nonneg p.2]
  exact ⟨mem_univ _, mem_singleton_iff.mpr (norm_eq_zero.mp hnorm)⟩

end NormalCoordinates

end FsFltz.Geometry
