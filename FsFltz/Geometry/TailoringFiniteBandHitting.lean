import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite crossing from a lower speed on a scalar band

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1805–1816.
The bound is needed only until the scalar reaches the target. No hitting
time, completion, or crossing map is assumed. The source target remains
`geoemtric-part-fsf.tex`, `thm:target`, lines 352–435 and `sec:lean`,
lines 764–829. Native flow and positive-cone retention are separate inputs
when applying this elementary producer to the actual ambient field.
-/

noncomputable section
open Set

namespace FsFltz.Geometry

/-- A positive lower speed before the target constructs a finite positive
crossing, with an explicit upper bound. No lower scalar barrier is needed. -/
theorem exists_pos_time_scalar_eq_of_lower_speed
    {g : ℝ → ℝ} (hg : Differentiable ℝ g) {b ε : ℝ}
    (hε : 0 < ε) (hzero : g 0 < b)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) ((b - g 0 + 1) / ε),
      g t ≤ b → ε ≤ deriv g t) :
    ∃ t ∈ Ioc (0 : ℝ) ((b - g 0 + 1) / ε), g t = b := by
  let T : ℝ := (b - g 0 + 1) / ε
  have hT : 0 < T := div_pos (by linarith) hε
  by_contra hn
  have hbelow : ∀ t ∈ Icc (0 : ℝ) T, g t < b := by
    intro t ht
    by_contra hb
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht.1
      hg.continuous.continuousOn (show b ∈ Icc (g 0) (g t) from ⟨hzero.le, le_of_not_gt hb⟩)
    have hspos : 0 < s := by
      have hsne : s ≠ 0 := by intro h; subst s; linarith
      exact lt_of_le_of_ne hs.1 hsne.symm
    exact hn ⟨s, ⟨hspos, hs.2.trans ht.2⟩, he⟩
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) T), ε ≤ deriv g t := by
    intro t ht
    have hti : t ∈ Ioo (0 : ℝ) T := by simpa only [interior_Icc] using ht
    exact hspeed t hti (hbelow t ⟨hti.1.le, hti.2.le⟩).le
  have hslope := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv
    hg.continuous.continuousOn hg.differentiableOn hbound
    0 ⟨le_rfl, hT.le⟩ T ⟨hT.le, le_rfl⟩ hT.le
  have hmul : ε * T = b - g 0 + 1 := by
    dsimp only [T]
    exact mul_div_cancel₀ _ hε.ne'
  have hb := hbelow T ⟨hT.le, le_rfl⟩
  simp only [sub_zero] at hslope
  rw [hmul] at hslope
  linarith

/-- Nondecreasing scalar orbits have exactly one crossing in the finite
time interval constructed by the lower speed bound. -/
theorem existsUnique_pos_time_scalar_eq_of_lower_speed
    {g : ℝ → ℝ} (hg : Differentiable ℝ g) {b ε : ℝ}
    (hε : 0 < ε) (hzero : g 0 < b)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) ((b - g 0 + 1) / ε),
      g t ≤ b → ε ≤ deriv g t)
    (hmono : MonotoneOn g (Icc (0 : ℝ) ((b - g 0 + 1) / ε))) :
    ∃! t, t ∈ Ioc (0 : ℝ) ((b - g 0 + 1) / ε) ∧ g t = b := by
  obtain ⟨t, ht, he⟩ := exists_pos_time_scalar_eq_of_lower_speed hg hε hzero hspeed
  refine ⟨t, ⟨ht, he⟩, ?_⟩
  intro s hs
  have hnotlt (u v : ℝ)
      (hu : u ∈ Ioc (0 : ℝ) ((b - g 0 + 1) / ε))
      (hv : v ∈ Ioc (0 : ℝ) ((b - g 0 + 1) / ε))
      (heu : g u = b) (hev : g v = b) : ¬ u < v := by
    intro huv
    have hbound : ∀ r ∈ interior (Icc u v), ε ≤ deriv g r := by
      intro r hr
      have hri : r ∈ Ioo u v := by simpa only [interior_Icc] using hr
      have hr0 : r ∈ Icc (0 : ℝ) ((b - g 0 + 1) / ε) :=
        ⟨(hu.1.trans hri.1).le, hri.2.le.trans hv.2⟩
      apply hspeed r ⟨hu.1.trans hri.1, hri.2.trans_le hv.2⟩
      exact (hmono hr0 ⟨hv.1.le, hv.2⟩ hri.2.le).trans hev.le
    have hsl := (convex_Icc u v).mul_sub_le_image_sub_of_le_deriv
      hg.continuous.continuousOn hg.differentiableOn hbound
      u ⟨le_rfl, huv.le⟩ v ⟨huv.le, le_rfl⟩ huv.le
    rw [heu, hev, sub_self] at hsl
    exact (not_le_of_gt (mul_pos hε (sub_pos.mpr huv))) hsl
  exact le_antisymm (le_of_not_gt (hnotlt t s ht hs.1 he hs.2))
    (le_of_not_gt (hnotlt s t hs.1 ht hs.2 he))

end FsFltz.Geometry
