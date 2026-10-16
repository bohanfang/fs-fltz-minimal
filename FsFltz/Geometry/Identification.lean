import FsFltz.Geometry.Liouville

/-!
# Strict completion identifications with their induced boundary maps

Source: `def:chain`, lines 171–189. The specified end-map equation makes the
boundary map the representative of the same escaping trajectory.
`BoundaryMapBridge`, `BoundarySmooth` and `BoundaryContact` construct the
smooth boundary map, shift and primitive pullback equation from a
primitive-preserving diffeomorphism (`sec:lean`, lines 805–814).
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- A diffeomorphism of compact domains, represented by smooth extensions on
open neighbourhoods of the compact pieces. The extensions need not be global
diffeomorphisms of the larger extension manifolds. -/
structure CompactDomainDiffeomorph {d : ℕ} (D E : CompactDomain d) where
  map : D.extension.Point → E.extension.Point
  inverse : E.extension.Point → D.extension.Point
  sourceNeighbourhood : Set D.extension.Point
  targetNeighbourhood : Set E.extension.Point
  open_source : IsOpen sourceNeighbourhood
  open_target : IsOpen targetNeighbourhood
  contains_source : D.carrier ⊆ sourceNeighbourhood
  contains_target : E.carrier ⊆ targetNeighbourhood
  smooth_map : ContMDiffOn (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ map sourceNeighbourhood
  smooth_inverse : ContMDiffOn (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ inverse targetNeighbourhood
  maps_source : MapsTo map D.carrier E.carrier
  maps_target : MapsTo inverse E.carrier D.carrier
  left_inverse : ∀ x ∈ D.carrier, inverse (map x) = x
  right_inverse : ∀ x ∈ E.carrier, map (inverse x) = x
  immersion : ∀ x ∈ D.carrier, Function.Injective
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) map x)

structure CompletionIdentification {n : ℕ} (P Q : WitnessedPair n) where
  ambientEquiv : P.ambientCompletion.ambient.manifold.SmoothEquiv
    Q.ambientCompletion.ambient.manifold
  primitive : P.ambientCompletion.ambient.manifold.pullback
    Q.ambientCompletion.ambient.manifold ambientEquiv
    Q.ambientCompletion.ambient.primitive = P.ambientCompletion.ambient.primitive
  boundaryEquiv : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary
  shift : P.ambientDomain.domain.boundary.Point → ℝ
  smooth_shift : ContMDiff (𝓘(ℝ, Model (2 * n - 1))) (𝓘(ℝ, ℝ)) ∞ shift
  induced_at_infinity : ∀ x, ∃ r0 : ℝ, ∀ r : ℝ, r0 ≤ r →
    ambientEquiv (P.ambientCompletion.endMap (x, r)) =
      Q.ambientCompletion.endMap (boundaryEquiv x, r + shift x)
  boundary_primitive : P.ambientDomain.domain.boundary.pullback
    Q.ambientDomain.domain.boundary boundaryEquiv
    (Q.ambientDomain.domain.boundaryForm Q.ambientDomain.liouville.primitive) =
    fun x => Real.exp (-shift x) •
      P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x
  ribbonEquiv : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain
  scale : ℝ
  positive_scale : 0 < scale
  ribbon_primitive : ∀ x ∈ P.ribbonDomain.domain.carrier,
    P.ribbonDomain.domain.extension.pullback Q.ribbonDomain.domain.extension ribbonEquiv.map
      Q.ribbonDomain.liouville.primitive x = scale • P.ribbonDomain.liouville.primitive x
  ribbon_square : ∀ x ∈ P.ribbonDomain.domain.carrier,
    boundaryEquiv (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (ribbonEquiv.map x)

end FsFltz.Geometry
