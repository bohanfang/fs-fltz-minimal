import FsFltz.Geometry.Liouville
import FsFltz.Geometry.Family

/-!
# Trivialized smooth deformations of witnessed pairs

`def:chain`, lines 163–169, permits a chosen trivialization of the compact
domain and ribbon bundles. Here that presentation is explicit. The completed
ambient and ribbon also have trivializations respecting the compact pieces
and cylindrical ends, and their forms and fields vary jointly smoothly.
This implements the completed-family requirement in `sec:lean`, 788–793.

The correspondence between these extension-space presentations and arbitrary
smooth compact bundles is a pending foundation bridge. No deformation exists
merely because two embedded cores agree.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- A change of presentation of a compact boundary domain, with its actual
extension and boundary maps. No primitive is required to stay fixed. -/
structure DomainPresentationEquiv {d : ℕ} (D E : CompactDomain d) where
  extensionEquiv : D.extension.SmoothEquiv E.extension
  carrier : extensionEquiv '' D.carrier = E.carrier
  boundaryEquiv : D.boundary.SmoothEquiv E.boundary
  boundary_square : ∀ x, extensionEquiv (D.boundaryInclusion.map x) =
    E.boundaryInclusion.map (boundaryEquiv x)

/-- A trivialization of completions that extends the compact presentation
and uses the same cylinder coordinate. Primitive preservation is deliberately
not imposed: the primitives are the varying data of a deformation. -/
structure CompletionPresentationEquiv {d : ℕ} {D E : LiouvilleDomain d}
    (C : Completion D) (C' : Completion E) (h : DomainPresentationEquiv D.domain E.domain) where
  equiv : C.ambient.manifold.SmoothEquiv C'.ambient.manifold
  compact_square : ∀ x ∈ D.domain.carrier,
    equiv (C.inclusion.map x) = C'.inclusion.map (h.extensionEquiv x)
  end_square : ∀ x r, 0 ≤ r →
    equiv (C.endMap (x, r)) = C'.endMap (h.boundaryEquiv x, r)

/-- All actual endpoint tuples over the closed interval, presented on fixed
compact pieces and fixed completed spaces. Conditions outside the interval
are smooth extension conditions only; Liouville inequalities are asserted
by the tuples at parameters in the interval. -/
structure PairDeformation (n : ℕ) where
  pair : Parameter → WitnessedPair n
  ambientPresentation : ∀ t, DomainPresentationEquiv
    (pair parameterZero).ambientDomain.domain (pair t).ambientDomain.domain
  ribbonPresentation : ∀ t, DomainPresentationEquiv
    (pair parameterZero).ribbonDomain.domain (pair t).ribbonDomain.domain
  ambientCompletionPresentation : ∀ t, CompletionPresentationEquiv
    (pair parameterZero).ambientCompletion (pair t).ambientCompletion (ambientPresentation t)
  ribbonCompletionPresentation : ∀ t, CompletionPresentationEquiv
    (pair parameterZero).ribbonCompletion (pair t).ribbonCompletion (ribbonPresentation t)
  ambientPrimitive_smooth : (pair parameterZero).ambientDomain.domain.extension.IsSmoothIntervalFormFamily
    (fun t => (pair parameterZero).ambientDomain.domain.extension.pullback
      (pair t).ambientDomain.domain.extension (ambientPresentation t).extensionEquiv
      (pair t).ambientDomain.liouville.primitive)
  ribbonPrimitive_smooth : (pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalFormFamily
    (fun t => (pair parameterZero).ribbonDomain.domain.extension.pullback
      (pair t).ribbonDomain.domain.extension (ribbonPresentation t).extensionEquiv
      (pair t).ribbonDomain.liouville.primitive)
  ambientField_smooth : (pair parameterZero).ambientDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
    (fun t => (pair parameterZero).ambientDomain.domain.extension.pullbackVectorField
      (pair t).ambientDomain.domain.extension (ambientPresentation t).extensionEquiv
      (pair t).ambientDomain.liouville.field)
  ribbonField_smooth : (pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalVectorFieldFamily
    (fun t => (pair parameterZero).ribbonDomain.domain.extension.pullbackVectorField
      (pair t).ribbonDomain.domain.extension (ribbonPresentation t).extensionEquiv
      (pair t).ribbonDomain.liouville.field)
  ribbonEmbedding_smooth : (pair parameterZero).ribbonDomain.domain.extension.IsSmoothIntervalMapFamily
    (pair parameterZero).ambientDomain.domain.boundary
    (fun t x => (ambientPresentation t).boundaryEquiv.invFun
      ((pair t).ribbonEmbedding.map ((ribbonPresentation t).extensionEquiv x)))
  witness_smooth : (pair parameterZero).ambientDomain.domain.boundary.IsSmoothIntervalScalarFamily
    (fun t x => (pair t).witness ((ambientPresentation t).boundaryEquiv x))
  completedAmbientPrimitive_smooth :
    (pair parameterZero).ambientCompletion.ambient.manifold.IsSmoothIntervalFormFamily
      (fun t => (pair parameterZero).ambientCompletion.ambient.manifold.pullback
        (pair t).ambientCompletion.ambient.manifold (ambientCompletionPresentation t).equiv
        (pair t).ambientCompletion.ambient.primitive)
  completedRibbonPrimitive_smooth :
    (pair parameterZero).ribbonCompletion.ambient.manifold.IsSmoothIntervalFormFamily
      (fun t => (pair parameterZero).ribbonCompletion.ambient.manifold.pullback
        (pair t).ribbonCompletion.ambient.manifold (ribbonCompletionPresentation t).equiv
        (pair t).ribbonCompletion.ambient.primitive)
  completedAmbientField_smooth :
    (pair parameterZero).ambientCompletion.ambient.manifold.IsSmoothIntervalVectorFieldFamily
      (fun t => (pair parameterZero).ambientCompletion.ambient.manifold.pullbackVectorField
        (pair t).ambientCompletion.ambient.manifold (ambientCompletionPresentation t).equiv
        (pair t).ambientCompletion.ambient.field)
  completedRibbonField_smooth :
    (pair parameterZero).ribbonCompletion.ambient.manifold.IsSmoothIntervalVectorFieldFamily
      (fun t => (pair parameterZero).ribbonCompletion.ambient.manifold.pullbackVectorField
        (pair t).ribbonCompletion.ambient.manifold (ribbonCompletionPresentation t).equiv
        (pair t).ribbonCompletion.ambient.field)

namespace PairDeformation

def source {n : ℕ} (D : PairDeformation n) : WitnessedPair n := D.pair parameterZero

def target {n : ℕ} (D : PairDeformation n) : WitnessedPair n := D.pair parameterOne

/-- The completed primitive on the fixed source presentation, used by the
grading extension of this very deformation. -/
def completedPrimitive {n : ℕ} (D : PairDeformation n) (t : Parameter) :
    D.source.ambientCompletion.ambient.manifold.Form 1 :=
  D.source.ambientCompletion.ambient.manifold.pullback
    (D.pair t).ambientCompletion.ambient.manifold (D.ambientCompletionPresentation t).equiv
    (D.pair t).ambientCompletion.ambient.primitive

end PairDeformation
end FsFltz.Geometry
