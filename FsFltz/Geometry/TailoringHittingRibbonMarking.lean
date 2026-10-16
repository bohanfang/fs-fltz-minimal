import FsFltz.Geometry.TailoringHittingRibbonFamily
import FsFltz.Geometry.TailoringRoundedCompletionMarking

/-!
# The same full-fiber marking of the completed hitting ribbon

Source: `geometric-part-fsf-proof.tex`, full-ribbon shrinking, lines 1840–1845,
and the completed decreasing-coefficient family, lines 1918–1924. Localization
changes the open compact presentation and its completion realization while
preserving the actual inclusion marking onto the same entire native fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.InclusionMarking

/-- Localize a specified completion marking to any actual flow collar,
retaining its compact inclusion and its all-real flow-induced end law. -/
def localizeToFlowCollar {d : ℕ} {D : LiouvilleDomain d} {C : Completion D}
    {X : CompleteLiouvilleManifold d} {q : D.domain.Point → X.manifold.Point}
    (m : InclusionMarking C X q) (B : LiouvilleDomain.FlowCollar D) :
    InclusionMarking B.cylindricalCompletion X
      (fun x => q ⟨B.originalInclusion.map x.val, by
        exact (B.image_originalInclusion_carrier ▸
          (show B.originalInclusion.map x.val ∈
            B.originalInclusion.map '' B.localizedDomain.domain.carrier from
              ⟨x.val, x.property, rfl⟩))⟩) := by
  let i : B.localizedDomain.domain.Point → X.manifold.Point :=
    fun x => q ⟨B.originalInclusion.map x.val, by
      exact (B.image_originalInclusion_carrier ▸
        (show B.originalInclusion.map x.val ∈
          B.originalInclusion.map '' B.localizedDomain.domain.carrier from
            ⟨x.val, x.property, rfl⟩))⟩
  let m' : InclusionMarking (C.localizeToFlowCollar B) X i :=
    { equiv := m.equiv
      primitive := m.primitive
      inclusion := fun x => m.inclusion
        ⟨B.originalInclusion.map x.val, by
          exact (B.image_originalInclusion_carrier ▸
            (show B.originalInclusion.map x.val ∈
              B.originalInclusion.map '' B.localizedDomain.domain.carrier from
                ⟨x.val, x.property, rfl⟩))⟩
      flow_induced := m.flow_induced }
  exact B.cylindricalCompletion.transportInclusionMarking
    (C.localizeToFlowCollar B) X i m'

end FsFltz.Geometry.InclusionMarking

namespace FsFltz.CompletedHittingRibbonFamily
open Geometry Geometry.SmoothManifold

/-- Every computed hitting slice retains an actual completion inclusion
marking onto the same entire native full fiber of the selected shrinking.
Its compact inclusion is the same intrinsic negative-flow embedding after
the actual localized collar inclusion. -/
def retainedFiberInclusionMarking {n : ℕ} {P : WitnessedPair n}
    (S : IntrinsicShrinkingData P)
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (Q : FullFiberRibbonMarking P R f value φ)
    {D : CompactDomain (2 * n)} {L : Parameter → LiouvilleStructure D}
    {j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D (S.pair parameterOne).ribbonDomain L j b)
    (t : Parameter) :
    InclusionMarking (H.deformation.pair t).ribbonCompletion
      Q.primitive.toCompleteLiouvilleManifold
      (fun x => (S.fiberEmbedding Q parameterOne).map
        ((H.ribbon.collars t).originalInclusion.map x.val)) :=
  (S.fullFiberMarking Q parameterOne).marking.localizeToFlowCollar (H.ribbon.collars t)

end FsFltz.CompletedHittingRibbonFamily
