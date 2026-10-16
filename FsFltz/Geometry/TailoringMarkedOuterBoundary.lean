import FsFltz.Geometry.PotentialTailoringMarkedChain
import FsFltz.Geometry.IntrinsicCompletionDomain
import FsFltz.Geometry.RegularSublevelFrontier

/-!
# The literal boundary of the retained outer completion

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1784–1817,
and `subsec:junction`, lines 1894–1905. The marking family's compact
carrier equation determines the image of its actual native boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

local instance markedOuterBoundaryChartedSpace {n : ℕ} :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance markedOuterBoundaryIsManifold {n : ℕ} :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- The actual boundary of the retained outer compact domain maps to the
literal regular level, by the carrier equation and the open embedding. -/
theorem OuterAmbientInclusionMarkingFamily.native_boundary_image {n : ℕ}
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {ρ : LGSpace n → ℝ} {α : Parameter → (lgManifold n).Form 1}
    (M : OuterAmbientInclusionMarkingFamily Q J ρ α)
    (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    (hreg : ∀ y, ρ y = 0 →
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ρ y ≠ 0) :
    range (M.nativeEmbedding.comp M.domain.boundaryInclusion).map = {y | ρ y = 0} := by
  have hopen : Topology.IsOpenEmbedding M.nativeEmbedding.map :=
    ⟨M.nativeEmbedding.embedding, M.nativeEmbedding.isOpenMap.isOpen_range⟩
  calc
    _ = M.nativeEmbedding.map '' range M.domain.boundaryInclusion.map := by
      change range (M.nativeEmbedding.map ∘ M.domain.boundaryInclusion.map) = _
      exact Set.range_comp _ _
    _ = M.nativeEmbedding.map '' frontier M.domain.carrier := by rw [M.domain.boundary_range]
    _ = frontier (M.nativeEmbedding.map '' M.domain.carrier) :=
      M.domain.image_frontier_of_openEmbedding (lgManifold n) M.nativeEmbedding hopen
    _ = frontier {y | ρ y ≤ 0} := by rw [M.native_image]
    _ = {y | ρ y = 0} :=
      (lgManifold n).frontier_scalar_sublevel_of_regular_zero ρ hρ hreg

end FsFltz
