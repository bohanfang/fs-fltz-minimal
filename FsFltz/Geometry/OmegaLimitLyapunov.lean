import FsFltz.Analysis.OmegaLimitLyapunov
import FsFltz.Geometry.FlowAbsorption

/-!
# Critical forward limits for an actual smooth complete flow

Source: `geometric-part-fsf-proof.tex`, `thm:core`, lines 1738–1744.
The differential is evaluated on the vector field generating this very flow.
-/

namespace FsFltz.Geometry

open Set Filter
open scoped Manifold ContDiff

variable {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x}

/-- Strict positivity of a smooth function along a complete field forces
every relatively compact forward orbit to accumulate only at field zeros. -/
theorem CompleteLiouvilleFlow.omegaLimit_nonempty_subset_zero
    (F : CompleteLiouvilleFlow M Z) (V : M.Point → ℝ)
    (hV : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ V)
    (hstrict : ∀ y, Z y ≠ 0 → 0 < M.scalarDerivative V y (Z y))
    {x : M.Point} (hcompact : IsCompact (closure (F.flow.forwardOrbit x))) :
    (omegaLimit atTop F.flow {x}).Nonempty ∧
      omegaLimit atTop F.flow {x} ⊆ {y | Z y = 0} := by
  have hn : ∀ y, 0 ≤ M.scalarDerivative V y (Z y) := by
    intro y
    by_cases hz : Z y = 0
    · simp only [hz, SmoothManifold.scalarDerivative, map_zero]
      exact le_rfl
    · exact (hstrict y hz).le
  obtain ⟨hne, hzero⟩ := FsFltz.omegaLimit_nonempty_subset_lyapunov_zero F.flow
    hV.continuous (F.hasDerivAt_scalar_orbit V hV) hn hcompact
  refine ⟨hne, ?_⟩
  intro y hy
  by_contra hz
  exact (ne_of_gt (hstrict y hz)) (hzero hy)

end FsFltz.Geometry
