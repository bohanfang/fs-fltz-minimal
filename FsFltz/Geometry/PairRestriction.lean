import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.Chain

/-!
# Ambient extension restriction as a permitted pair comparison

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160; `def:chain`,
lines 171–199; the relabeling clause in `lem:choices`, lines 470–472; and
`sec:lean`, lines 783–814. Restricting the ambient extension to an open
neighborhood of its whole compact carrier retains the boundary presentation,
the ribbon, its embedding and its positive witness literally. The supplied
completion keeps the same completed manifold and cylindrical end.

The resulting presentation change is recorded by an actual completion
identification, with identity ambient, boundary and ribbon maps and scale one,
and then by a one-step finite comparison chain. This is a foundation lemma;
it neither constructs a completion nor proves the target geometric chain.

Ribbon extension restriction is a separate issue: the current
`CompactDomainDiffeomorph` requires total maps on both extension manifolds
(`Identification.lean`, lines 24–25). An empty restricted extension cannot be
the codomain of a total inverse from a nonempty original extension. The
construction here retains the ribbon extension and needs no nonemptiness
assumption, including for zero-dimensional or empty ribbons.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomainDiffeomorph

/-- The identity relabeling, including its actual smooth extension maps. -/
def refl {d : ℕ} (D : CompactDomain d) : CompactDomainDiffeomorph D D where
  map := id
  inverse := id
  sourceNeighbourhood := univ
  targetNeighbourhood := univ
  open_source := isOpen_univ
  open_target := isOpen_univ
  contains_source := subset_univ _
  contains_target := subset_univ _
  smooth_map := contMDiff_id.contMDiffOn
  smooth_inverse := contMDiff_id.contMDiffOn
  maps_source := fun _ hx => hx
  maps_target := fun _ hx => hx
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  immersion := by
    intro x _
    rw [mfderiv_id]
    exact Function.injective_id

end CompactDomainDiffeomorph

namespace WitnessedPair

variable {n : ℕ} (P : WitnessedPair n)
    (U : TopologicalSpace.Opens P.ambientDomain.domain.extension.Point)
    (hU : P.ambientDomain.domain.carrier ⊆ U)

/-- Restrict the ambient extension around the whole compact domain, retaining
the boundary and all ribbon data. Both completions remain the supplied ones. -/
abbrev restrictAmbient : WitnessedPair n where
  ambientDomain := P.ambientDomain.restrict U hU
  ribbonDomain := P.ribbonDomain
  ribbonEmbedding := P.ribbonEmbedding
  witness := P.witness
  smooth_witness := P.smooth_witness
  positive_witness := P.positive_witness
  ribbon_primitive := by
    intro x hx
    change P.ribbonDomain.domain.extension.pullback P.ambientDomain.domain.boundary
      P.ribbonEmbedding.map (fun y => P.witness y •
        (P.ambientDomain.domain.restrict U hU).boundaryForm
          ((P.ambientDomain.domain.extension.restrict U).pullback
            P.ambientDomain.domain.extension Subtype.val P.ambientDomain.liouville.primitive) y)
      x = P.ribbonDomain.liouville.primitive x
    rw [P.ambientDomain.domain.boundaryForm_restrict U hU]
    exact P.ribbon_primitive x hx
  ambientCompletion := P.ambientCompletion.restrict U hU
  ribbonCompletion := P.ribbonCompletion

@[simp] theorem restrictAmbient_witness : (P.restrictAmbient U hU).witness = P.witness := rfl

@[simp] theorem restrictAmbient_ribbonEmbedding :
    (P.restrictAmbient U hU).ribbonEmbedding = P.ribbonEmbedding := rfl

/-- The full embedded core is literally the same subset of the retained
boundary, since both the ribbon and its complete flow are unchanged. -/
@[simp] theorem embeddedCore_restrictAmbient :
    (P.restrictAmbient U hU).embeddedCore = P.embeddedCore := rfl

/-- The identity on the completed ambient is the actual permitted comparison
for this presentation change. Its boundary map is induced by the identical
end trajectories, its ribbon map is identity, and its primitive scale is one. -/
def restrictAmbientIdentification : CompletionIdentification P (P.restrictAmbient U hU) where
  ambientEquiv := Diffeomorph.refl _ _ ∞
  primitive := P.ambientCompletion.ambient.manifold.pullback_id _
  boundaryEquiv := Diffeomorph.refl _ _ ∞
  shift := fun _ => 0
  smooth_shift := contMDiff_const
  induced_at_infinity := by
    intro x
    exact ⟨0, fun r _ => by simp⟩
  boundary_primitive := by
    change P.ambientDomain.domain.boundary.pullback P.ambientDomain.domain.boundary id
      ((P.ambientDomain.domain.restrict U hU).boundaryForm
        ((P.ambientDomain.domain.extension.restrict U).pullback
          P.ambientDomain.domain.extension Subtype.val P.ambientDomain.liouville.primitive)) = _
    rw [P.ambientDomain.domain.boundaryForm_restrict U hU,
      P.ambientDomain.domain.boundary.pullback_id]
    simp
  ribbonEquiv := CompactDomainDiffeomorph.refl _
  scale := 1
  positive_scale := zero_lt_one
  ribbon_primitive := by
    intro x _
    change P.ribbonDomain.domain.extension.pullback P.ribbonDomain.domain.extension id
      P.ribbonDomain.liouville.primitive x = 1 • P.ribbonDomain.liouville.primitive x
    rw [P.ribbonDomain.domain.extension.pullback_id, one_smul]
  ribbon_square := fun _ _ => rfl

/-- A finite comparison chain whose single arrow is the constructed strict
identification; its endpoint is the entire restricted pair tuple. -/
def restrictAmbientChain : ComparisonChain P (P.restrictAmbient U hU) :=
  Quiver.Path.cons Quiver.Path.nil
    (ComparisonStep.identification (P.restrictAmbientIdentification U hU))

end WitnessedPair
end FsFltz.Geometry
