import FsFltz.Geometry.CompletionScaledPresentation
import FsFltz.Geometry.FlowBridge

/-!
# Comparing arbitrary chosen completions of one compact domain

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 171–189; and `sec:lean`, lines 783–814.
The constant-scale extension theorem at scale one constructs a strict
comparison with identity compact and boundary maps. Its actual completed
flow transports the full intrinsic core and inclusion markings, including
the flow-induced equation at all real radii.

This concerns supplied completions of the same represented domain. Native
compact-map presentation correspondence and target-specific markings remain
separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The identity compact and boundary presentation. -/
def DomainPresentationEquiv.refl {d : ℕ} (D : CompactDomain d) :
    DomainPresentationEquiv D D where
  extensionEquiv := Diffeomorph.refl 𝓘(ℝ, Model d) D.extension.Point ∞
  carrier := by simp
  boundaryEquiv := Diffeomorph.refl 𝓘(ℝ, Model (d - 1)) D.boundary.Point ∞
  boundary_square := fun _ => rfl

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d}

/-- The original identity compact presentation extends strictly between
any two chosen completions. -/
theorem exists_strict_comparison (C C' : Completion D) :
    ∃ p : CompletionPresentationEquiv C C' (DomainPresentationEquiv.refl D.domain),
      C.ambient.manifold.pullback C'.ambient.manifold p.equiv C'.ambient.primitive =
        C.ambient.primitive := by
  obtain ⟨p, hp⟩ := C.exists_scaledPresentation_of_compact_primitive C'
    (DomainPresentationEquiv.refl D.domain) 1 (by norm_num) (by
      intro x _
      change D.domain.extension.pullback D.domain.extension id D.liouville.primitive x =
        (1 : ℝ) • D.liouville.primitive x
      rw [D.domain.extension.pullback_id, one_smul])
  exact ⟨p, by simpa only [one_smul] using hp⟩

/-- A strict comparison produced from the identity compact presentation. -/
def comparisonPresentation (C C' : Completion D) :
    CompletionPresentationEquiv C C' (DomainPresentationEquiv.refl D.domain) :=
  (C.exists_strict_comparison C').choose

theorem comparison_primitive (C C' : Completion D) :
    C.ambient.manifold.pullback C'.ambient.manifold (C.comparisonPresentation C').equiv
      C'.ambient.primitive = C.ambient.primitive :=
  (C.exists_strict_comparison C').choose_spec

/-- The strict comparison preserves the compact inclusion pointwise. -/
theorem comparison_compact (C C' : Completion D) (x : D.domain.extension.Point)
    (hx : x ∈ D.domain.carrier) :
    (C.comparisonPresentation C').equiv (C.inclusion.map x) = C'.inclusion.map x :=
  (C.comparisonPresentation C').compact_square x hx

/-- Strict field transport preserves the actual end flow at every real
radius, including the negative part of the compact collar. -/
theorem comparison_end (C C' : Completion D) (x : D.domain.boundary.Point) (r : ℝ) :
    (C.comparisonPresentation C').equiv (C.endMap (x, r)) = C'.endMap (x, r) := by
  rw [C.end_flow, C'.end_flow,
    C.ambient.map_flow C'.ambient (C.comparisonPresentation C').equiv
      (C.comparison_primitive C'),
    C.comparison_compact C' _ (D.domain.boundaryInclusion_mem_carrier x)]

/-- The full all-forward-time core is independent of the chosen completion,
via the constructed strict comparison and its compact square. -/
theorem core_eq_of_same_domain (C C' : Completion D) : C.core = C'.core := by
  ext x
  have hflow (hx : x ∈ D.domain.carrier) (t : ℝ) :
      (C.comparisonPresentation C').equiv
        (C.ambient.completeFlow.flow t (C.inclusion.map x)) =
      C'.ambient.completeFlow.flow t (C'.inclusion.map x) := by
    rw [C.ambient.map_flow C'.ambient (C.comparisonPresentation C').equiv
      (C.comparison_primitive C'), C.comparison_compact C' x hx]
  constructor
  · rintro ⟨hx, hf⟩
    refine ⟨hx, ?_⟩
    intro t ht
    obtain ⟨y, hy, he⟩ := hf t ht
    refine ⟨y, hy, ?_⟩
    have he' := congrArg (C.comparisonPresentation C').equiv he
    rwa [C.comparison_compact C' y hy, hflow hx t] at he'
  · rintro ⟨hx, hf⟩
    refine ⟨hx, ?_⟩
    intro t ht
    obtain ⟨y, hy, he⟩ := hf t ht
    refine ⟨y, hy, ?_⟩
    apply (C.comparisonPresentation C').equiv.injective
    exact (C.comparison_compact C' y hy).trans (he.trans (hflow hx t).symm)

/-- Transport an actual inclusion marking to another chosen completion of
the same domain, retaining its prescribed compact inclusion and all-real
flow-induced equation. -/
def transportInclusionMarking (C C' : Completion D)
    (X : CompleteLiouvilleManifold d) (i : D.domain.Point → X.manifold.Point)
    (q : InclusionMarking C' X i) : InclusionMarking C X i where
  equiv := (C.comparisonPresentation C').equiv.trans q.equiv
  primitive := by
    change C.ambient.manifold.pullback X.manifold
      (q.equiv ∘ (C.comparisonPresentation C').equiv) X.primitive = _
    rw [C.ambient.manifold.pullback_comp C'.ambient.manifold X.manifold
      ((C.comparisonPresentation C').equiv.contMDiff.mdifferentiable (by simp))
      (q.equiv.contMDiff.mdifferentiable (by simp)), q.primitive, C.comparison_primitive]
  inclusion := by
    intro x
    change q.equiv ((C.comparisonPresentation C').equiv (C.inclusion.map x.val)) = i x
    rw [C.comparison_compact C' x.val x.property, q.inclusion]
  flow_induced := by
    intro x r
    change q.equiv ((C.comparisonPresentation C').equiv (C.endMap (x, r))) =
      X.completeFlow.flow r
        (q.equiv ((C.comparisonPresentation C').equiv
          (C.inclusion.map (D.domain.boundaryInclusion.map x))))
    rw [C.comparison_end C',
      C.comparison_compact C' _ (D.domain.boundaryInclusion_mem_carrier x)]
    exact q.flow_induced x r

end Completion
end FsFltz.Geometry
