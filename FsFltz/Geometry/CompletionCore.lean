import FsFltz.Geometry.CompletionIntervalMapFamily
import FsFltz.Geometry.FlowBridge
import Mathlib.Topology.Order.Compact

/-!
# The full core and relatively compact forward orbits

Source: `geometric-part-fsf-proof.tex`, `sec:skeleton`, lines 1569–1575;
`geoemtric-part-fsf.tex`, `def:pair`, lines 148–158. The actual end embedding
and its closed image force an escaping orbit to have unbounded end radius.
The equivalence is transported through an actual primitive-preserving
inclusion marking, with its proved flow equivariance.
-/

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace FsFltz.Geometry
namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)

/-- The native embedded full core is compact in this very completion. -/
theorem isCompact_image_core : IsCompact (C.inclusion.map '' C.core) := by
  rw [C.image_core_eq_flowCore]
  exact FsFltz.isCompact_flowCore _
    (D.domain.compact.image C.inclusion.map.contMDiff.continuous)

/-- Compactness also holds on the native compact-domain presentation. -/
theorem isCompact_core : IsCompact C.core :=
  C.inclusion.embedding.isCompact_iff.mpr C.isCompact_image_core

/-- On an actual completion, relative compactness of the entire forward
orbit is exactly membership in the all-forward-time full core. -/
theorem image_core_eq_relativelyCompact_forwardOrbit :
    C.inclusion.map '' C.core =
      {x | IsCompact (closure (C.ambient.completeFlow.flow.forwardOrbit x))} := by
  rw [C.image_core_eq_flowCore]
  let F := C.ambient.completeFlow.flow
  let K := C.inclusion.map '' D.domain.carrier
  have hK : IsCompact K :=
    D.domain.compact.image C.inclusion.map.contMDiff.continuous
  let e : D.domain.boundary.Point × Ici (0 : ℝ) → C.ambient.manifold.Point :=
    fun p => C.endMap (p.1, p.2)
  have herange : range e = C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    ext z
    constructor
    · rintro ⟨⟨b, r⟩, rfl⟩
      exact ⟨(b, r.val), ⟨mem_univ _, r.property⟩, rfl⟩
    · rintro ⟨⟨b, r⟩, ⟨_, hr⟩, rfl⟩
      exact ⟨(b, ⟨r, hr⟩), rfl⟩
  have he : Topology.IsClosedEmbedding e :=
    ⟨C.end_embedding, herange ▸ C.isClosed_endMap_image_Ici 0⟩
  ext x
  constructor
  · intro hx
    exact hK.of_isClosed_subset isClosed_closure (closure_minimal (by
      rintro z ⟨t, rfl⟩
      exact hx t.val t.property) hK.isClosed)
  · intro hx t ht
    by_contra hnot
    have hc : F t x ∈ K ∪ C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
      rw [show K ∪ C.endMap '' (univ ×ˢ Ici (0 : ℝ)) = univ from C.covering]
      exact mem_univ _
    obtain ⟨⟨b, r⟩, ⟨_, hr⟩, hbr⟩ := hc.resolve_left hnot
    have hpre : IsCompact (e ⁻¹' closure (F.forwardOrbit x)) := he.isCompact_preimage hx
    obtain ⟨V, hV⟩ := hpre.bddAbove_image
      ((continuous_subtype_val.comp continuous_snd).continuousOn)
    let s : ℝ := max 0 (V - r + 1)
    have hs : 0 ≤ s := le_max_left _ _
    have hmem : (b, ⟨s + r, add_nonneg hs hr⟩) ∈
        e ⁻¹' closure (F.forwardOrbit x) := by
      apply subset_closure
      refine ⟨⟨s + t, add_nonneg hs ht⟩, ?_⟩
      change F (s + t) x = C.endMap (b, s + r)
      rw [F.map_add, ← hbr, C.flow_endMap]
    have hb := hV (mem_image_of_mem (fun p : D.domain.boundary.Point × Ici (0 : ℝ) =>
      p.2.val) hmem)
    change s + r ≤ V at hb
    have hs' : V - r + 1 ≤ s := le_max_right _ _
    linarith

end Completion

/-- Under the prescribed inclusion marking the full core is exactly the
set of relatively compact forward orbits in the named complete ambient. -/
theorem InclusionMarking.image_core_eq_relativelyCompact_forwardOrbit
    {d : ℕ} {D : LiouvilleDomain d} {C : Completion D}
    {X : CompleteLiouvilleManifold d} {i : D.domain.Point → X.manifold.Point}
    (q : InclusionMarking C X i) :
    i '' {x : D.domain.Point | x.val ∈ C.core} =
      {x | IsCompact (closure (X.completeFlow.flow.forwardOrbit x))} := by
  have hconj (t : ℝ) : Function.Semiconj q.equiv
      (C.ambient.completeFlow.flow t) (X.completeFlow.flow t) :=
    fun x => C.ambient.map_flow X q.equiv q.primitive x t
  have hcore : i '' {x : D.domain.Point | x.val ∈ C.core} =
      q.equiv '' (C.inclusion.map '' C.core) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨C.inclusion.map x.val, ⟨x.val, hx, rfl⟩, q.inclusion x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx.1⟩, hx, (q.inclusion ⟨x, hx.1⟩).symm⟩
  rw [hcore, C.image_core_eq_relativelyCompact_forwardOrbit]
  have horbit (y : C.ambient.manifold.Point) :
      q.equiv '' C.ambient.completeFlow.flow.forwardOrbit y =
      X.completeFlow.flow.forwardOrbit (q.equiv y) := by
    ext y
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hconj t y).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨C.ambient.completeFlow.flow t y, ⟨t, rfl⟩, hconj t y⟩
  have hclosure (y : C.ambient.manifold.Point) :
      q.equiv '' closure (C.ambient.completeFlow.flow.forwardOrbit y) =
      closure (X.completeFlow.flow.forwardOrbit (q.equiv y)) := by
    simpa only [Diffeomorph.coe_toHomeomorph, horbit] using
      q.equiv.toHomeomorph.image_closure (C.ambient.completeFlow.flow.forwardOrbit y)
  ext x
  change (∃ y, IsCompact (closure (C.ambient.completeFlow.flow.forwardOrbit y)) ∧
    q.equiv y = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    change IsCompact (closure (X.completeFlow.flow.forwardOrbit (q.equiv y)))
    rw [← hclosure]
    exact hy.image q.equiv.contMDiff.continuous
  · intro hx
    change IsCompact (closure (X.completeFlow.flow.forwardOrbit x)) at hx
    refine ⟨q.equiv.symm x, ?_, q.equiv.apply_symm_apply x⟩
    rw [← q.equiv.apply_symm_apply x, ← hclosure] at hx
    exact (q.equiv.toHomeomorph.isCompact_image).mp hx

end FsFltz.Geometry
