import FsFltz.Geometry.BoundaryNondegeneracy
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The interior side of an outward trajectory

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–158,
and `sec:lean`, lines 783–814. A local defining function composed with an
outward trajectory has positive derivative and value zero at time zero.
Its difference quotient is therefore positive for all sufficiently small
nonzero times. The sublevel equation then identifies membership in the
compact domain with nonpositive time. This is a local side calculation;
it assumes neither a completion nor its cylindrical overlap equation.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

private theorem eventually_nonpos_iff_of_hasDerivAt_pos
    {f : ℝ → ℝ} {a : ℝ} (hf : HasDerivAt f a 0) (hzero : f 0 = 0)
    (ha : 0 < a) : ∀ᶠ t in 𝓝 (0 : ℝ), f t ≤ 0 ↔ t ≤ 0 := by
  have hp : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < t⁻¹ * f t := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using
      hf.tendsto_slope_zero.eventually (eventually_gt_nhds ha)
  filter_upwards [eventually_nhdsWithin_iff.mp hp] with t ht
  by_cases hz : t = 0
  · simp [hz, hzero]
  have hpos := ht hz
  rcases lt_or_gt_of_ne hz with hn | hn
  · have hfneg : f t < 0 := by
      rcases mul_pos_iff.mp hpos with h | h
      · exact False.elim ((not_lt_of_ge (le_of_lt (inv_lt_zero.mpr hn))) h.1)
      · exact h.2
    exact iff_of_true (le_of_lt hfneg) (le_of_lt hn)
  · have hfpos : 0 < f t := (mul_pos_iff.mp hpos).resolve_right
      (fun h => (not_lt_of_ge (le_of_lt (inv_pos.mpr hn))) h.1) |>.2
    exact iff_of_false (not_le_of_gt hfpos) (not_le_of_gt hn)

namespace LiouvilleStructure

set_option backward.isDefEq.respectTransparency false in
/-- Outwardness determines the domain side of any differentiable trajectory
with the prescribed initial velocity. The local lifetime may depend on the
boundary point; no uniform collar width is asserted here. -/
theorem eventually_mem_carrier_iff_nonpos {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point)
    {γ : ℝ → D.extension.Point}
    (hzero : γ 0 = D.boundaryInclusion.map x)
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (L.field (γ 0)))) :
    ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ D.carrier ↔ t ≤ 0 := by
  let ρ := D.defining _ (D.boundaryInclusion_mem_frontier x)
  have hρ := (ρ.smooth_rho.contMDiffAt
    (ρ.open_neighbourhood.mem_nhds ρ.mem_neighbourhood)).mdifferentiableAt (by simp)
  have hρ' : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho (γ 0) := by
    simpa only [hzero] using hρ
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp (hρ'.hasMFDerivAt.comp 0 hγ)).hasDerivAt
  have hdz : HasDerivAt (fun t => ρ.rho (γ t))
      (D.extension.scalarDerivative ρ.rho (D.boundaryInclusion.map x)
        (L.field (D.boundaryInclusion.map x))) 0 := by
    apply hd.congr_deriv
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho (γ 0)
      ((1 : ℝ) • L.field (γ 0)) = _
    simp only [one_smul, scalarDerivative]
    exact congrArg (fun y => D.extension.scalarDerivative ρ.rho y (L.field y)) hzero
  have hv : ρ.rho (γ 0) = 0 := by
    rw [hzero]
    exact (ρ.zero_level _ ρ.mem_neighbourhood).mp (D.boundaryInclusion_mem_frontier x)
  have hs := eventually_nonpos_iff_of_hasDerivAt_pos hdz hv
    (L.outward _ (D.boundaryInclusion_mem_frontier x))
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ρ.neighbourhood :=
    hγ.continuousAt.preimage_mem_nhds
      (by simpa only [hzero] using ρ.open_neighbourhood.mem_nhds ρ.mem_neighbourhood)
  filter_upwards [hs, hn] with t ht htn
  exact (ρ.sublevel _ htn).trans ht

end LiouvilleStructure
end FsFltz.Geometry
