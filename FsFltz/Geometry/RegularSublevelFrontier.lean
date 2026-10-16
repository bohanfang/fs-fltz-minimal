import FsFltz.Geometry.FormScalarDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Frontier of a regular smooth scalar sublevel

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 915–919.
This general producer identifies the frontier and interior of a literal
closed scalar sublevel on a native boundaryless smooth manifold. A zero
in the interior would be a local maximum, so Fermat's theorem would make
the actual native differential vanish.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry

namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Fermat's theorem for the actual native differential on a boundaryless
smooth manifold, obtained in a genuine native chart. -/
theorem mfderiv_eq_zero_of_isLocalMax {d : ℕ} {M : SmoothManifold d}
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    {x : M.Point} (hmax : IsLocalMax ρ x) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x = 0 := by
  let c := chartAt (Model d) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy : c x ∈ c.target := c.map_source hx
  have hmax' : IsLocalMax ρ (c.symm (c x)) := by
    simpa only [c.left_inv hx] using hmax
  have hchart : IsLocalMax (ρ ∘ c.symm) (c x) :=
    hmax'.comp_continuous (c.continuousAt_symm hy)
  have hzero := hchart.fderiv_eq_zero
  ext v
  have hnative := M.fderiv_scalar_in_chart ρ hρ x x hx v
  rw [hzero, zero_apply] at hnative
  exact hnative.symm

/-- A regular zero is excluded from the interior of the literal closed
sublevel. All strictly negative points are interior by continuity. -/
theorem interior_scalar_sublevel_of_regular_zero {d : ℕ} {M : SmoothManifold d}
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    interior {x : M.Point | ρ x ≤ 0} = {x : M.Point | ρ x < 0} := by
  ext x
  constructor
  · intro hx
    have hmem : x ∈ {y : M.Point | ρ y ≤ 0} := interior_subset hx
    have hle : ρ x ≤ 0 := hmem
    apply lt_of_le_of_ne hle
    intro hz
    have hmax : IsLocalMax ρ x := by
      have hnhds : {y : M.Point | ρ y ≤ 0} ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
      filter_upwards [hnhds] with y hy
      change ρ y ≤ ρ x
      rwa [hz]
    exact hregular x hz (mfderiv_eq_zero_of_isLocalMax ρ hρ hmax)
  · intro hx
    have hopen : IsOpen {y : M.Point | ρ y < 0} := isOpen_lt hρ.continuous continuous_const
    have hsubset : {y : M.Point | ρ y < 0} ⊆ {y : M.Point | ρ y ≤ 0} := by
      intro y hy
      change ρ y < 0 at hy
      change ρ y ≤ 0
      exact hy.le
    apply interior_mono hsubset
    rwa [hopen.interior_eq]

/-- The literal closed sublevel of a smooth scalar with regular zero level
has exactly that zero level as its topological frontier. -/
theorem frontier_scalar_sublevel_of_regular_zero {d : ℕ} {M : SmoothManifold d}
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    frontier {x : M.Point | ρ x ≤ 0} = {x : M.Point | ρ x = 0} := by
  have hclosed : IsClosed {x : M.Point | ρ x ≤ 0} := isClosed_le hρ.continuous continuous_const
  rw [hclosed.frontier_eq, interior_scalar_sublevel_of_regular_zero ρ hρ hregular]
  ext x
  change (ρ x ≤ 0 ∧ ¬ ρ x < 0) ↔ ρ x = 0
  exact ⟨fun hx => le_antisymm hx.1 (le_of_not_gt hx.2), fun hx => by simp [hx]⟩

end SmoothManifold

end FsFltz.Geometry
