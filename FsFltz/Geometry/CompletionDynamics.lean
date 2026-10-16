import FsFltz.Geometry.Liouville

/-!
# Negative invariance of the compact piece of an actual completion

The covering and end-flow equations imply negative invariance of the compact
piece: a negative-time image outside it would flow forward along a positive
end ray back into the compact piece, contradicting the end-overlap condition.
This supplies the dynamical consequence used by the full-core description in
`geoemtric-part-fsf.tex`, `def:pair`, lines 148–158. Construction of a completion
from a bare outward Liouville domain remains a separate foundation.
-/

noncomputable section
open Set

namespace FsFltz.Geometry.Completion

/-- The compact piece of a completion is invariant under negative time. -/
theorem negative_flow_mem {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    {x : C.ambient.manifold.Point} (hx : x ∈ C.inclusion.map '' D.domain.carrier)
    {t : ℝ} (ht : 0 ≤ t) :
    C.ambient.completeFlow.flow (-t) x ∈ C.inclusion.map '' D.domain.carrier := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hx
  by_contra hnot
  have hcover : C.ambient.completeFlow.flow (-t) x ∈
      C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [C.covering]
    exact mem_univ _
  obtain ⟨⟨y, r⟩, hr, he⟩ := hcover.resolve_left hnot
  have he' := congrArg (C.ambient.completeFlow.flow t) he
  rw [C.end_flow, ← Flow.map_add] at he'
  simp only [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply] at he'
  have hpos : 0 < t + r := add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht (Ne.symm ht0)) hr.2
  apply C.overlap y (t + r) hpos
  rw [C.end_flow, he']
  exact hx

/-- The negative images appearing in the full-core formula are nested. -/
theorem negative_image_antitone {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    Antitone (fun t : ℝ =>
      C.ambient.completeFlow.flow (-t) '' (C.inclusion.map '' D.domain.carrier)) := by
  intro r s hrs z hz
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨C.ambient.completeFlow.flow (-(s - r)) x,
    C.negative_flow_mem hx (sub_nonneg.mpr hrs), ?_⟩
  rw [← Flow.map_add]
  congr 1
  ring

end FsFltz.Geometry.Completion
