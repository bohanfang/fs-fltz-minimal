import FsFltz.Geometry.IntrinsicCylinder

/-!
# The regular time coordinate on the intrinsic two-sided cylinder

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The recharted cylinder's actual time coordinate is smooth
and has nonzero differential at every point. This supplies the regular
defining function in the constructed collar attachment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model k) B]
  [IsManifold 𝓘(ℝ, Model k) ∞ B]

/-- The actual time coordinate of the attached two-sided cylinder. -/
def bandTime {δ : ℝ} (p : Band δ B) : ℝ := p.val.1

/-- The actual time coordinate is smooth in the recharted ambient model. -/
theorem contMDiff_bandTime (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := B) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ (bandTime : Band δ B → ℝ) := by
  have hv := contMDiff_band_val (k := k) (B := B) δ
  let := bandChartedSpace (k := k) (B := B) δ
  exact contMDiff_fst.comp hv

/-- Varying only time gives a local smooth curve with derivative one for the
time coordinate. Hence that coordinate's differential cannot vanish. -/
theorem mfderiv_bandTime_ne_zero {δ : ℝ} (p : Band δ B) :
    letI := bandChartedSpace (k := k) (B := B) δ
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) (bandTime : Band δ B → ℝ) p ≠ 0 := by
  classical
  let := bandChartedSpace (k := k) (B := B) δ
  let q : ℝ → Band δ B := fun t =>
    if ht : t ∈ Ioo (-δ) δ then ⟨(t, p.val.2), ht, mem_univ _⟩ else p
  have heq : ∀ᶠ t in 𝓝 p.val.1, (q t).val = (t, p.val.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds p.property.1] with t ht
    simp only [q, dite_eq_left ht]
  have hq : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (k + 1)) ∞ q p.val.1 := by
    apply (contMDiffAt_band_iff_val (f := q)).mpr
    exact (contMDiff_id.prodMk (contMDiff_const (c := p.val.2))).contMDiffAt
      |>.congr_of_eventuallyEq heq
  have hqp : q p.val.1 = p := by
    apply Subtype.ext
    exact heq.self_of_nhds
  have htime : (bandTime ∘ q) =ᶠ[𝓝 p.val.1] id := by
    filter_upwards [heq] with t ht
    exact congrArg Prod.fst ht
  have hd := mfderiv_comp (f := q) (g := (bandTime : Band δ B → ℝ)) p.val.1
    ((contMDiff_bandTime δ).mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp))
  rw [htime.mfderiv_eq, mfderiv_id, hqp] at hd
  intro hz
  rw [hz] at hd
  have h := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hd
  change (1 : ℝ) = 0 at h
  exact one_ne_zero h

end FsFltz.Geometry.IntrinsicCollarGluing
