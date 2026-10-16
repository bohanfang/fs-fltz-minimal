import FsFltz.Geometry.IntrinsicCollarGluing
import Mathlib.Topology.Order.DenselyOrdered

/-!
# The original carrier and its actual frontier in the collar attachment

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The original carrier is the literal image of the native
manifold in the constructed attachment. Its frontier is proved to be the
same native boundary, using the two-sided collar coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

section General

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {δ : ℝ} (hδ : 0 < δ) (C : Half δ B → M)

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- The cylinder meets the original carrier in exactly its nonnegative half. -/
theorem preimage_cylinder_range_original :
    cylinder C ⁻¹' range (original C) = {p : Band δ B | 0 ≤ p.val.1} := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    exact ((original_eq_cylinder_iff C x p).mp hx).choose
  · intro hp
    exact ⟨C (halfOfNonneg p hp),
      (original_eq_cylinder_iff C _ p).mpr ⟨hp, rfl⟩⟩

/-- The strictly positive half of the cylinder is exactly the interior
of its intersection with the original carrier. -/
theorem interior_nonnegative_band :
    interior {p : Band δ B | 0 ≤ p.val.1} = {p : Band δ B | 0 < p.val.1} := by
  have ho : IsOpen (Band δ B) := isOpen_Ioo.prod isOpen_univ
  have he := ho.isOpenEmbedding_subtypeVal
  have h := he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous
    (Ici (0 : ℝ) ×ˢ (univ : Set B))
  have hpre : (Subtype.val : Band δ B → ℝ × B) ⁻¹'
      (Ici (0 : ℝ) ×ˢ (univ : Set B)) = {p | 0 ≤ p.val.1} := by
    ext p
    simp
  rw [interior_prod_eq, interior_Ici, interior_univ] at h
  rw [hpre] at h
  ext p
  simpa using Set.ext_iff.mp h.symm p

/-- The frontier of the nonnegative half in the actual two-sided band is its seam. -/
theorem frontier_nonnegative_band :
    frontier {p : Band δ B | 0 ≤ p.val.1} = {p : Band δ B | p.val.1 = 0} := by
  have ho : IsOpen (Band δ B) := isOpen_Ioo.prod isOpen_univ
  have he := ho.isOpenEmbedding_subtypeVal
  have h := he.isOpenMap.preimage_frontier_eq_frontier_preimage he.continuous
    (Ici (0 : ℝ) ×ˢ (univ : Set B))
  have hpre : (Subtype.val : Band δ B → ℝ × B) ⁻¹'
      (Ici (0 : ℝ) ×ˢ (univ : Set B)) = {p | 0 ≤ p.val.1} := by
    ext p
    simp
  rw [frontier_prod_univ_eq, frontier_Ici] at h
  rw [hpre] at h
  ext p
  simpa using Set.ext_iff.mp h.symm p

include hδ in
/-- The actual cylinder coordinates detect precisely the original carrier's interior. -/
theorem cylinder_mem_interior_range_original (hC : IsOpenEmbedding C) (p : Band δ B) :
    cylinder C p ∈ interior (range (original C)) ↔ 0 < p.val.1 := by
  have he := isOpenEmbedding_cylinder hδ C hC
  have h := he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous
    (range (original C))
  rw [preimage_cylinder_range_original, interior_nonnegative_band] at h
  exact Set.ext_iff.mp h p

include hδ in
/-- The actual cylinder coordinates detect precisely the original carrier's frontier. -/
theorem cylinder_mem_frontier_range_original (hC : IsOpenEmbedding C) (p : Band δ B) :
    cylinder C p ∈ frontier (range (original C)) ↔ p.val.1 = 0 := by
  have he := isOpenEmbedding_cylinder hδ C hC
  have h := he.isOpenMap.preimage_frontier_eq_frontier_preimage he.continuous
    (range (original C))
  rw [preimage_cylinder_range_original, frontier_nonnegative_band] at h
  exact Set.ext_iff.mp h p

include hδ in
/-- The original carrier is closed in the constructed Hausdorff attachment. -/
theorem isClosed_range_original [T2Space M] [T2Space B] (hC : IsOpenEmbedding C) :
    IsClosed (range (original C)) :=
  (isClosedEmbedding_original hδ C hC).isClosed_range

end General

section Native

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Half δ (IntrinsicBoundary.Point k M) → M)

include hδ in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The constructed extension has the original native boundary as its actual seam. -/
theorem original_mem_frontier_of_boundary (hC : IsOpenEmbedding C)
    (hzero : ∀ b : IntrinsicBoundary.Point k M,
      C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val)
    (b : IntrinsicBoundary.Point k M) : original C b.val ∈ frontier (range (original C)) := by
  let p : Half δ (IntrinsicBoundary.Point k M) :=
    ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
  have heq := original_collar_eq_cylinder hδ C p
  change original C (C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩) = _ at heq
  rw [hzero b] at heq
  rw [heq]
  exact (cylinder_mem_frontier_range_original hδ C hC _).mpr rfl

include hδ in
/-- The literal interior image is exactly the topological interior of the original carrier. -/
theorem interior_range_original (hC : IsOpenEmbedding C)
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p) ↔ p.val.1 = 0)
    (hzero : ∀ b : IntrinsicBoundary.Point k M,
      C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val) :
    interior (range (original C)) = range (interiorIn C) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := interior_subset hq
    have hx : (𝓡∂ (k + 1)).IsInteriorPoint x := by
      apply ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      intro hb
      have hf := original_mem_frontier_of_boundary hδ C hC hzero ⟨x, hb⟩
      exact (disjoint_interior_frontier.notMem_of_mem_left hq) hf
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    have hi := isOpenEmbedding_interiorIn hδ C hC hboundary
    apply interior_maximal (fun q hq => ?_) hi.isOpen_range (mem_range_self x)
    obtain ⟨y, rfl⟩ := hq
    exact mem_range_self y.val

include hδ in
/-- The full topological frontier is the embedded literal native boundary. -/
theorem frontier_range_original [T2Space M] (hC : IsOpenEmbedding C)
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p) ↔ p.val.1 = 0)
    (hzero : ∀ b : IntrinsicBoundary.Point k M,
      C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val) :
    frontier (range (original C)) = original C '' (𝓡∂ (k + 1)).boundary M := by
  ext q
  constructor
  · intro hq
    have hclosed := isClosed_range_original hδ C hC
    obtain ⟨x, rfl⟩ := hclosed.closure_eq ▸ frontier_subset_closure hq
    refine ⟨x, ?_, rfl⟩
    apply ((𝓡∂ (k + 1)).isBoundaryPoint_iff_not_isInteriorPoint x).mpr
    intro hx
    have hi : original C x ∈ interior (range (original C)) := by
      rw [interior_range_original hδ C hC hboundary hzero]
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (disjoint_interior_frontier.notMem_of_mem_left hi) hq
  · rintro ⟨x, hx, rfl⟩
    exact original_mem_frontier_of_boundary hδ C hC hzero ⟨x, hx⟩

end Native

end FsFltz.Geometry.IntrinsicCollarGluing
