import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth stretching of a finite Liouville collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 783–814. This scalar construction supplies the radial
reparameterization needed to realize the infinite exponential end on an
open finite collar. It asserts no completion or geometric comparison.

The formula is the identity on `(-∞, δ / 3]` and agrees with
`r + 1 / (δ - r)` on `[2 * δ / 3, δ)`. Its derivative is strictly
positive throughout `(-∞, δ)`.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace FsFltz.Geometry.CollarStretch

/-- A monotone smooth cutoff supported away from the seam. -/
def cutoff (δ r : ℝ) : ℝ := Real.smoothTransition (3 * r / δ - 1)

/-- The explicit radial stretch; only its restriction to `r < δ` is used. -/
def stretch (δ r : ℝ) : ℝ := r + cutoff δ r / (δ - r)

theorem cutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (cutoff δ) := by
  unfold cutoff
  fun_prop

theorem cutoff_nonneg (δ r : ℝ) : 0 ≤ cutoff δ r :=
  Real.smoothTransition.nonneg _

theorem cutoff_monotone {δ : ℝ} (hδ : 0 < δ) : Monotone (cutoff δ) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith) hδ.le) 1

theorem stretch_eq_self {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ / 3) :
    stretch δ r = r := by
  have h : 3 * r / δ - 1 ≤ 0 := by
    have : 3 * r ≤ δ := by linarith
    have := (div_le_one hδ).mpr this
    linarith
  simp [stretch, cutoff, Real.smoothTransition.zero_of_nonpos h]

theorem stretch_eq_reciprocal {δ r : ℝ} (hδ : 0 < δ) (hr : 2 * δ / 3 ≤ r) :
    stretch δ r = r + 1 / (δ - r) := by
  have h : 1 ≤ 3 * r / δ - 1 := by
    have : 2 * δ ≤ 3 * r := by linarith
    have := (le_div_iff₀ hδ).mpr this
    linarith
  simp [stretch, cutoff, Real.smoothTransition.one_of_one_le h]

theorem stretch_contDiffAt {δ r : ℝ} (hr : r < δ) :
    ContDiffAt ℝ ∞ (stretch δ) r := by
  unfold stretch
  exact contDiffAt_id.add ((cutoff_contDiff δ).contDiffAt.div
    (contDiffAt_const.sub contDiffAt_id) (sub_pos.mpr hr).ne')

theorem stretch_contDiffOn (δ : ℝ) :
    ContDiffOn ℝ ∞ (stretch δ) (Iio δ) :=
  fun _ hr => (stretch_contDiffAt hr).contDiffWithinAt

theorem stretch_hasDerivAt {δ r : ℝ} (hr : r < δ) :
    HasDerivAt (stretch δ)
      (1 + (deriv (cutoff δ) r * (δ - r) + cutoff δ r) / (δ - r) ^ 2) r := by
  have hc : HasDerivAt (cutoff δ) (deriv (cutoff δ) r) r :=
    ((cutoff_contDiff δ).differentiable (by simp)).differentiableAt.hasDerivAt
  convert (hasDerivAt_id r).add
    (hc.div ((hasDerivAt_const r δ).sub (hasDerivAt_id r)) (sub_pos.mpr hr).ne') using 1
  · rfl
  · simp [sub_neg_eq_add]

theorem stretch_deriv_pos {δ r : ℝ} (hδ : 0 < δ) (hr : r < δ) :
    0 < deriv (stretch δ) r := by
  rw [(stretch_hasDerivAt hr).deriv]
  have hc : 0 ≤ deriv (cutoff δ) r := (cutoff_monotone hδ).deriv_nonneg
  have hn : 0 ≤ deriv (cutoff δ) r * (δ - r) + cutoff δ r :=
    add_nonneg (mul_nonneg hc (sub_pos.mpr hr).le) (cutoff_nonneg δ r)
  have := div_nonneg hn (sq_nonneg (δ - r))
  linarith

theorem stretch_strictMonoOn {δ : ℝ} (hδ : 0 < δ) :
    StrictMonoOn (stretch δ) (Iio δ) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio δ) (stretch_contDiffOn δ).continuousOn
  intro r hr
  exact stretch_deriv_pos hδ (show r ∈ Iio δ from interior_subset hr)

theorem le_stretch {δ r : ℝ} (hr : r < δ) : r ≤ stretch δ r := by
  exact le_add_of_nonneg_right (div_nonneg (cutoff_nonneg δ r) (sub_pos.mpr hr).le)

/-- The finite outer endpoint is sent to positive infinity. -/
theorem stretch_tendsto_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (stretch δ) (𝓝[<] δ) atTop := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] δ) (𝓝 δ) := nhdsWithin_le_nhds
  have hsub : Tendsto (fun r : ℝ => δ - r) (𝓝[<] δ) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := δ)).sub hid
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show r < δ from hr)
  have hrec := hid.add_atTop hsub.inv_tendsto_nhdsGT_zero
  apply hrec.congr'
  filter_upwards [Ioo_mem_nhdsLT (show 2 * δ / 3 < δ by linarith)] with r hr
  simpa [one_div] using (stretch_eq_reciprocal hδ hr.1.le).symm

/-- Every real radial coordinate has a unique preimage below the finite endpoint. -/
theorem stretch_surjOn {δ : ℝ} (hδ : 0 < δ) :
    SurjOn (stretch δ) (Iio δ) univ := by
  intro y _
  have hhigh : ∀ᶠ r : ℝ in 𝓝[<] δ, y ≤ stretch δ r :=
    (stretch_tendsto_atTop hδ).eventually (eventually_ge_atTop y)
  obtain ⟨b, hb, hby⟩ := (hhigh.and self_mem_nhdsWithin).exists
  let a := min y 0
  have ha : a < δ := lt_of_le_of_lt (min_le_right y 0) hδ
  have hay : stretch δ a ≤ y := by
    rw [stretch_eq_self hδ (show a ≤ δ / 3 by dsimp [a]; linarith [min_le_right y 0])]
    exact min_le_left y 0
  exact (stretch_contDiffOn δ).continuousOn.surjOn_Icc ha hby ⟨hay, hb⟩

/-- The inverse scalar coordinate, chosen from the proved surjectivity. -/
def inverse {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : ℝ :=
  ((stretch_surjOn hδ) (mem_univ s)).choose

theorem inverse_lt {δ : ℝ} (hδ : 0 < δ) (s : ℝ) : inverse hδ s < δ :=
  ((stretch_surjOn hδ) (mem_univ s)).choose_spec.1

@[simp] theorem stretch_inverse {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    stretch δ (inverse hδ s) = s :=
  ((stretch_surjOn hδ) (mem_univ s)).choose_spec.2

@[simp] theorem inverse_stretch {δ r : ℝ} (hδ : 0 < δ) (hr : r < δ) :
    inverse hδ (stretch δ r) = r :=
  (stretch_strictMonoOn hδ).injOn (inverse_lt hδ _) hr (stretch_inverse hδ _)

/-- Order equivalence between the whole finite half collar and all real coordinates. -/
def stretchOrderIso {δ : ℝ} (hδ : 0 < δ) : Iio δ ≃o ℝ :=
  (show StrictMono (fun r : Iio δ => stretch δ r) from
    fun x y hxy => stretch_strictMonoOn hδ x.property y.property hxy).orderIsoOfRightInverse
      (fun r : Iio δ => stretch δ r)
      (fun s => ⟨inverse hδ s, inverse_lt hδ s⟩) (stretch_inverse hδ)

theorem inverse_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (inverse hδ) :=
  continuous_subtype_val.comp (stretchOrderIso hδ).toHomeomorph.symm.continuous_toFun

/-- An actual open partial homeomorphism with the explicit forward formula. -/
def stretchPartialHomeomorph {δ : ℝ} (hδ : 0 < δ) : OpenPartialHomeomorph ℝ ℝ where
  toFun := stretch δ
  invFun := inverse hδ
  source := Iio δ
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun s _ => inverse_lt hδ s
  left_inv' := fun _ hr => inverse_stretch hδ hr
  right_inv' := fun s _ => stretch_inverse hδ s
  open_source := isOpen_Iio
  open_target := isOpen_univ
  continuousOn_toFun := (stretch_contDiffOn δ).continuousOn
  continuousOn_invFun := (inverse_continuous hδ).continuousOn

/-- Smoothness of the globally defined inverse follows from the nonzero derivative. -/
theorem inverse_contDiff {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (inverse hδ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  exact (stretchPartialHomeomorph hδ).contDiffAt_symm_deriv
    (stretch_deriv_pos hδ (inverse_lt hδ s)).ne'
    (mem_univ s)
    ((stretch_contDiffAt (inverse_lt hδ s)).differentiableAt (by simp)).hasDerivAt
    (stretch_contDiffAt (inverse_lt hδ s))

theorem inverse_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (inverse hδ) (deriv (stretch δ) (inverse hδ s))⁻¹ s :=
  (stretchPartialHomeomorph hδ).hasDerivAt_symm (mem_univ s)
    (stretch_deriv_pos hδ (inverse_lt hδ s)).ne'
    ((stretch_contDiffAt (inverse_lt hδ s)).differentiableAt (by simp)).hasDerivAt

theorem inverse_deriv_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 < deriv (inverse hδ) s := by
  rw [(inverse_hasDerivAt hδ s).deriv]
  exact inv_pos.mpr (stretch_deriv_pos hδ (inverse_lt hδ s))

theorem inverse_strictMono {δ : ℝ} (hδ : 0 < δ) : StrictMono (inverse hδ) :=
  fun _ _ hxy => (stretchOrderIso hδ).symm.strictMono hxy

theorem inverse_eq_self {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ δ / 3) :
    inverse hδ s = s := by
  have hlt : s < δ := by linarith
  simpa [stretch_eq_self hδ hs] using inverse_stretch hδ hlt

@[simp] theorem inverse_zero {δ : ℝ} (hδ : 0 < δ) : inverse hδ 0 = 0 :=
  inverse_eq_self hδ (by positivity)

theorem inverse_nonneg_iff {δ s : ℝ} (hδ : 0 < δ) : 0 ≤ inverse hδ s ↔ 0 ≤ s := by
  simpa only [inverse_zero hδ] using (inverse_strictMono hδ).le_iff_le (a := 0) (b := s)

theorem inverse_pos_iff {δ s : ℝ} (hδ : 0 < δ) : 0 < inverse hδ s ↔ 0 < s := by
  simpa only [inverse_zero hδ] using (inverse_strictMono hδ).lt_iff_lt (a := 0) (b := s)

theorem inverse_mem_collar {δ s : ℝ} (hδ : 0 < δ) (hs : -δ < s) :
    inverse hδ s ∈ Ioo (-δ) δ := by
  refine ⟨?_, inverse_lt hδ s⟩
  have hbase : inverse hδ (-δ) = -δ := inverse_eq_self hδ (by linarith)
  simpa only [hbase] using inverse_strictMono hδ hs

/-- The restriction is a bijection from the two-sided finite collar to
the two-sided collar with an infinite positive end. -/
theorem stretch_bijOn_collar {δ : ℝ} (hδ : 0 < δ) :
    BijOn (stretch δ) (Ioo (-δ) δ) (Ioi (-δ)) := by
  refine ⟨?_, (stretch_strictMonoOn hδ).injOn.mono Ioo_subset_Iio_self, ?_⟩
  · intro r hr
    exact lt_of_lt_of_le hr.1 (le_stretch hr.2)
  · intro s hs
    exact ⟨inverse hδ s, inverse_mem_collar hδ hs, stretch_inverse hδ s⟩

end FsFltz.Geometry.CollarStretch
