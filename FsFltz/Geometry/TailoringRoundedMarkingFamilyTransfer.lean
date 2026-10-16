import FsFltz.Geometry.TailoringRoundedPairFamily
import FsFltz.Geometry.NativeCompactMapCompletion

/-!
# Inclusion markings on a prescribed rounded compact presentation

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468,
and the actual common marking, lines 1270–1303; `geoemtric-part-fsf.tex`,
`def:pair`, lines 132–160, and `def:chain`, lines 163–200.
Absorption constructs the marking on a regular sublevel of the named
complete ambient. A represented compact diffeomorphism transfers it to
the already prescribed source completion, retaining its compact map.
No completion equivalence is an input to this construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace Completion

/-- Construct an actual inclusion marking on a prescribed source completion
by identifying its compact carrier with an absorbing regular sublevel.
The map, its smooth inverse, and its primitive equality are outputs. -/
theorem exists_inclusionMarking_of_absorbing_sublevel
    {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (P : CompleteLiouvilleManifold d) (ρ : P.manifold.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : P.manifold.Point | ρ x ≤ 0})
    (hout : ∀ x, ρ x = 0 →
      0 < P.manifold.scalarDerivative ρ x (P.manifold.liouvilleVector P.primitive x))
    (habsorb : ∀ x : P.manifold.Point, ∃ T : ℝ, 0 ≤ T ∧
      ρ (P.completeFlow.flow (-T) x) ≤ 0)
    (h : CompactDomainDiffeomorph D.domain
      (regularSublevelLiouvilleDomain P.manifold ρ hρ hcompact P.primitive
        P.smooth_primitive P.symplectic hout).domain)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback P.manifold h.map P.primitive x = D.liouville.primitive x) :
    ∃ q : InclusionMarking C P (fun x => h.map x.val),
      ∀ b r, q.equiv (C.endMap (b, r)) = P.completeFlow.flow r
        (h.map (D.domain.boundaryInclusion.map b)) := by
  let B := regularSublevelLiouvilleDomain P.manifold ρ hρ hcompact P.primitive
    P.smooth_primitive P.symplectic hout
  let K := BoundaryOutwardAbsorptionMarking.completionOfBoundaryOutwardAbsorption
    B P.completePrimitive ρ hρ
    (regularSublevelLiouvilleDomain_frontier P.manifold ρ hρ hcompact
      P.primitive P.smooth_primitive P.symplectic hout) hout rfl habsorb
  obtain ⟨e, _b, he, hc, _hb, _hend⟩ := C.exists_strictEquiv_of_compactDiffeomorph K h hp
  let q : InclusionMarking C P (fun x => h.map x.val) :=
    { equiv := e
      primitive := he
      inclusion := fun x => hc x.val x.property
      flow_induced := fun b r => by
        rw [C.end_flow, C.ambient.map_flow P e he] }
  refine ⟨q, ?_⟩
  intro b r
  rw [q.flow_induced, q.inclusion
    ⟨D.domain.boundaryInclusion.map b, D.domain.boundaryInclusion_mem_carrier b⟩]

end Completion
end FsFltz.Geometry
