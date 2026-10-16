import FsFltz.Geometry.CompletionComparison
import FsFltz.Geometry.ScaledLiouvilleFlowTransport

/-!
# Uniqueness of prescribed completed maps from the compact map

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 171–189; `g:initial`, lines 371–393; and
`sec:lean`, lines 803–814.
Constant primitive scaling transports the actual complete Liouville flow.
Consequently the compact formula determines the map on every end trajectory,
including negative times. Compact/end coverage then determines the entire
completed map. Applied to the constructed extension, this gives existence
and uniqueness without assuming an end formula. It also proves uniqueness
of supplied inclusion markings from their primitive and inclusion equations.

All statements allow dimension zero and empty boundary. Construction of the
target-specific full-fiber markings and the geometric target remain pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d}

/-- Primitive scaling forces the same-radius end formula at every real
time from the prescribed compact square, using the actual completed flows. -/
theorem end_square_of_scaled_primitive
    (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold) (c : ℝ)
    (hp : C.ambient.manifold.pullback C'.ambient.manifold f C'.ambient.primitive =
      c • C.ambient.primitive)
    (hsquare : ∀ x ∈ D.domain.carrier,
      f (C.inclusion.map x) = C'.inclusion.map (h.extensionEquiv x))
    (x : D.domain.boundary.Point) (r : ℝ) :
    f (C.endMap (x, r)) = C'.endMap (h.boundaryEquiv x, r) := by
  rw [C.end_flow, C'.end_flow,
    C.ambient.map_flow_of_scaled_primitive C'.ambient f c hp,
    hsquare _ (D.domain.boundaryInclusion_mem_carrier x), h.boundary_square]

/-- Two constant-scaled primitive maps to the same complete ambient are
equal if they agree on the compact piece. Their end agreement is derived,
and coverage accounts for every point of the completion. -/
theorem equiv_eq_of_scaled_primitive_on_compact
    {e : ℕ} (C : Completion D) (X : CompleteLiouvilleManifold e)
    (f g : C.ambient.manifold.SmoothEquiv X.manifold) (cf cg : ℝ)
    (hf : C.ambient.manifold.pullback X.manifold f X.primitive =
      cf • C.ambient.primitive)
    (hg : C.ambient.manifold.pullback X.manifold g X.primitive =
      cg • C.ambient.primitive)
    (hcompact : ∀ x ∈ D.domain.carrier,
      f (C.inclusion.map x) = g (C.inclusion.map x)) : f = g := by
  apply Diffeomorph.ext
  intro z
  have hz : z ∈ C.inclusion.map '' D.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [C.covering]
    exact mem_univ z
  rcases hz with ⟨x, hx, rfl⟩ | ⟨⟨x, r⟩, _, rfl⟩
  · exact hcompact x hx
  · rw [C.end_flow,
      C.ambient.map_flow_of_scaled_primitive X f cf hf,
      C.ambient.map_flow_of_scaled_primitive X g cg hg,
      hcompact _ (D.domain.boundaryInclusion_mem_carrier x)]

/-- A prescribed compact map with positive constant primitive scale has a
unique completed diffeomorphism with that scale and compact formula. The
construction supplies existence; flow transport supplies uniqueness. -/
theorem existsUnique_scaledEquiv_of_compact_primitive
    (C : Completion D) (C' : Completion E)
    (h : DomainPresentationEquiv D.domain E.domain) (c : ℝ) (hc : 0 < c)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x) :
    ∃! f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold,
      C.ambient.manifold.pullback C'.ambient.manifold f C'.ambient.primitive =
        c • C.ambient.primitive ∧
      ∀ x ∈ D.domain.carrier,
        f (C.inclusion.map x) = C'.inclusion.map (h.extensionEquiv x) := by
  obtain ⟨p, hp'⟩ := C.exists_scaledPresentation_of_compact_primitive C' h c hc hp
  refine ⟨p.equiv, ⟨hp', p.compact_square⟩, ?_⟩
  intro f hf
  exact C.equiv_eq_of_scaled_primitive_on_compact C'.ambient f p.equiv c c hf.1 hp'
    (fun x hx => (hf.2 x hx).trans (p.compact_square x hx).symm)

/-- Every strict map retaining the original compact inclusion is the
already constructed strict comparison, regardless of its chosen proof or
end presentation. -/
theorem eq_comparison_of_primitive
    (C C' : Completion D)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hp : C.ambient.manifold.pullback C'.ambient.manifold f C'.ambient.primitive =
      C.ambient.primitive)
    (hsquare : ∀ x ∈ D.domain.carrier,
      f (C.inclusion.map x) = C'.inclusion.map x) :
    f = (C.comparisonPresentation C').equiv := by
  apply C.equiv_eq_of_scaled_primitive_on_compact C'.ambient f
    (C.comparisonPresentation C').equiv 1 1
  · simpa only [one_smul] using hp
  · simpa only [one_smul] using C.comparison_primitive C'
  · intro x hx
    exact (hsquare x hx).trans (C.comparison_compact C' x hx).symm

end Completion

/-- Inclusion markings with the same specified compact inclusion have the
same actual diffeomorphism. Their recorded flow equations are consequences
of primitive preservation and are unnecessary as uniqueness hypotheses. -/
theorem InclusionMarking.equiv_unique {d : ℕ} {D : LiouvilleDomain d}
    {C : Completion D} {X : CompleteLiouvilleManifold d}
    {i : D.domain.Point → X.manifold.Point} (q q' : InclusionMarking C X i) :
    q.equiv = q'.equiv := by
  apply C.equiv_eq_of_scaled_primitive_on_compact X q.equiv q'.equiv 1 1
  · simpa only [one_smul] using q.primitive
  · simpa only [one_smul] using q'.primitive
  · intro x hx
    exact (q.inclusion ⟨x, hx⟩).trans (q'.inclusion ⟨x, hx⟩).symm

end FsFltz.Geometry
