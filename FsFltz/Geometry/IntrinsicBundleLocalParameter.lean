import FsFltz.Geometry.IntrinsicBundleGauge
import FsFltz.Geometry.IntrinsicBundleFormTransport

/-!
# Local parameter cutoffs retaining both interval endpoints

Source: `geoemtric-part-fsf.tex`, smooth endpoint convention, lines 119–122;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
A cutoff on the actual parameter interval has a smooth real extension and
stays in a prescribed original chart. Its extension need not take off-interval
values in the interval. This distinction retains the identity near endpoints.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle
open IntrinsicLiouville

/-- Every point of an open interval chart, including either endpoint, has
a smooth interval-valued cutoff which is the identity on a relative open
neighborhood. Only its actual interval values must remain in the chart. -/
theorem exists_smooth_interval_cutoff {S : Set Parameter} (hS : IsOpen S)
    (t : Parameter) (ht : t ∈ S) :
    ∃ (σ : Parameter → Parameter) (f : ℝ → ℝ) (U : Set Parameter),
      ContDiff ℝ ∞ f ∧ (∀ s, (σ s).val = f s.val) ∧
      (∀ s, σ s ∈ S) ∧ IsOpen U ∧ t ∈ U ∧ U ⊆ S ∧
      ∀ s ∈ U, σ s = s := by
  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp hS
  have htO : t.val ∈ O := by
    change t ∈ Subtype.val ⁻¹' O
    rwa [hOS]
  obtain ⟨u, v, htv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds htO)
  let r := min (t.val - u) (v - t.val) / 2
  have hr : 0 < r := half_pos (lt_min (sub_pos.mpr htv.1) (sub_pos.mpr htv.2))
  have hru : r < t.val - u := by
    have hm := min_le_left (t.val - u) (v - t.val)
    dsimp [r] at *
    linarith
  have hrv : r < v - t.val := by
    have hm := min_le_right (t.val - u) (v - t.val)
    dsimp [r] at *
    linarith
  let b : ContDiffBump t.val := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let f : ℝ → ℝ := fun s => t.val + (s - t.val) * b s
  have hf : ContDiff ℝ ∞ f :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul b.contDiff)
  have hfI (s : Parameter) : f s.val ∈ parameterInterval := by
    have hb0 := b.nonneg (x := s.val)
    have hb1 := b.le_one (x := s.val)
    have hs0 := s.property.1
    have hs1 := s.property.2
    have ht0 := t.property.1
    have ht1 := t.property.2
    dsimp [f]
    constructor <;> nlinarith
  let σ : Parameter → Parameter := fun s => ⟨f s.val, hfI s⟩
  have hfO (s : ℝ) : f s ∈ O := by
    have hbound : |f s - t.val| < r := by
      by_cases hs : |s - t.val| < r
      · have hb0 := b.nonneg (x := s)
        have hb1 := b.le_one (x := s)
        have habs : |(s - t.val) * b s| ≤ |s - t.val| := by
          rw [abs_mul, abs_of_nonneg hb0]
          nlinarith [abs_nonneg (s - t.val)]
        simpa only [f, add_sub_cancel_left] using habs.trans_lt hs
      · have hb : b s = 0 := b.zero_of_le_dist
          (by simpa only [Real.dist_eq] using le_of_not_gt hs)
        simpa only [f, hb, mul_zero, add_zero, sub_self, abs_zero] using hr
    obtain ⟨hl, hr'⟩ := abs_lt.mp hbound
    apply hsub
    constructor <;> linarith
  let U : Set Parameter := {s | |s.val - t.val| < r / 2}
  have hU : IsOpen U := isOpen_lt
    ((continuous_subtype_val.sub continuous_const).abs) continuous_const
  have hid (s : Parameter) (hs : s ∈ U) : σ s = s := by
    have hb : b s.val = 1 := b.one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall, Real.dist_eq] using hs.le)
    apply Subtype.ext
    change t.val + (s.val - t.val) * b s.val = s.val
    rw [hb]
    ring
  have hσS (s : Parameter) : σ s ∈ S := by
    rw [← hOS]
    exact hfO s.val
  refine ⟨σ, f, U, hf, fun _ => rfl, hσS, hU, ?_, ?_, hid⟩
  · change |t.val - t.val| < r / 2
    simpa only [sub_self, abs_zero] using half_pos hr
  · intro s hs
    rw [← hid s hs]
    exact hσS s

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Reparametrize native form germs with an actual interval map and an
independent smooth real extension. No range condition is imposed on the
extension off the parameter interval. -/
theorem HasSmoothFormFamilyOn.reparam_interval {r : ℕ} {S : Set Parameter}
    {α : Parameter → IntrinsicLiouville.Form k M r} (h : HasSmoothFormFamilyOn S α)
    (σ : Parameter → Parameter) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hσ : ∀ s, (σ s).val = f s.val) (hmem : ∀ s, σ s ∈ S) :
    IntrinsicLiouville.IsLocallyExtendibleFormFamily (fun t => α (σ t)) := by
  intro e he t x hx
  obtain ⟨V, β, hV, hp, hβ, heq⟩ := h e he (σ t) (hmem t) x hx
  let q : ℝ × Model (k + 1) → ℝ × Model (k + 1) := fun z => (f z.1, z.2)
  have hq : ContDiff ℝ ∞ q := (hf.comp contDiff_fst).prodMk contDiff_snd
  refine ⟨q ⁻¹' V, β ∘ q, hV.preimage hq.continuous, ?_,
    hβ.comp hq.contDiffOn (fun _ hz => hz), ?_⟩
  · change (f t.val, e.extend (𝓡∂ (k + 1)) x) ∈ V
    rwa [← hσ t]
  · intro s y hy hsy
    change β (f s.val, y) = _
    rw [← hσ s]
    apply heq (σ s) (hmem s) y hy
    change (f s.val, y) ∈ V at hsy
    rwa [← hσ s] at hsy

end FsFltz.Geometry.IntrinsicSmoothBundle
