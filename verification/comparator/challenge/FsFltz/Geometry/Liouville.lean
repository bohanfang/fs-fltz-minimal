import FsFltz.Geometry.Smooth
import FsFltz.Core

/-!
# Compact smooth boundary domains and Liouville structures

Source: `def:pair`, lines 119–160; `sec:lean`, lines 783–814.
The domain is a regular local sublevel subset of a native smooth extension
manifold, with an explicit native smooth boundary presentation.
`BoundaryCharts` and `BoundaryAtlas` construct its native smooth half-space
atlas. `CylindricalCompletion` constructs completions after localization of
these presentations. Reverse intrinsic presentation and full source
correspondence remain pending. No target-specific geometric existence is asserted.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- Local smooth defining function, including the actual sublevel and zero
level identities. -/
structure BoundaryDefiningFunction {d : ℕ} (M : SmoothManifold d)
    (s : Set M.Point) (x : M.Point) where
  neighbourhood : Set M.Point
  open_neighbourhood : IsOpen neighbourhood
  mem_neighbourhood : x ∈ neighbourhood
  rho : M.Point → ℝ
  smooth_rho : ContMDiffOn (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ rho neighbourhood
  sublevel : ∀ y ∈ neighbourhood, y ∈ s ↔ rho y ≤ 0
  zero_level : ∀ y ∈ neighbourhood, y ∈ frontier s ↔ rho y = 0
  regular : mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) rho x ≠ 0

/-- Smooth compact domain with boundary extension. In dimension zero the
boundary is explicitly empty; no positivity is imposed on a zero tangent. -/
structure CompactDomain (d : ℕ) where
  extension : SmoothManifold d
  carrier : Set extension.Point
  compact : IsCompact carrier
  defining : ∀ x ∈ frontier carrier, BoundaryDefiningFunction extension carrier x
  boundary : SmoothManifold (d - 1)
  boundaryInclusion : boundary.SmoothEmbedding extension
  boundary_range : Set.range boundaryInclusion.map = frontier carrier
  zero_boundary : d = 0 → IsEmpty boundary.Point

namespace CompactDomain

abbrev Point {d : ℕ} (D : CompactDomain d) := {x : D.extension.Point // x ∈ D.carrier}

def boundaryForm {d : ℕ} (D : CompactDomain d) (alpha : D.extension.Form 1) :
    D.boundary.Form 1 := D.boundary.pullback D.extension D.boundaryInclusion.map alpha

end CompactDomain

/-- Defining properties on the compact domain, with smooth extensions across
its boundary. The field equation uses the actual exterior derivative. -/
structure LiouvilleStructure {d : ℕ} (D : CompactDomain d) where
  primitive : D.extension.Form 1
  smooth_primitive : D.extension.IsSmoothForm primitive
  symplectic : D.extension.IsSymplecticOn (D.extension.exteriorDerivative primitive) D.carrier
  field : (x : D.extension.Point) → D.extension.Tangent x
  smooth_field : D.extension.IsSmoothVectorField field
  contraction : ∀ x ∈ D.carrier, ∀ v,
    evalTwo (D.extension.exteriorDerivative primitive) x (field x) v = evalOne primitive x v
  outward : ∀ (x : D.extension.Point) (hx : x ∈ frontier D.carrier),
    0 < D.extension.scalarDerivative (D.defining x hx).rho x (field x)

theorem LiouvilleStructure.field_eq_liouvilleVector {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    L.field x = D.extension.liouvilleVector L.primitive x :=
  (D.extension.liouvilleVector_eq L.primitive x (L.symplectic.2.2 x hx)
    (L.contraction x hx)).symm

structure LiouvilleDomain (d : ℕ) where
  domain : CompactDomain d
  liouville : LiouvilleStructure domain

/-- A complete smooth flow of a specified vector field. It has all real
times, a jointly smooth action, and the actual coordinate ODE. -/
structure CompleteLiouvilleFlow {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) where
  flow : Flow ℝ M.Point
  smooth_action : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
    (fun p : ℝ × M.Point => flow p.1 p.2)
  solves : ∀ (x : M.Point) (t : ℝ), ∀ a : M.Point,
    flow t x ∈ (chartAt (Model d) a).source →
    HasDerivAt (fun s : ℝ => chartAt (Model d) a (flow s x))
      (M.chartTangentMap a (flow t x) (Z (flow t x))) t

/-- A completed Liouville manifold, with its actual primitive and complete
flow. The collar/gluing construction is not an assumed operator. -/
structure CompleteLiouvilleManifold (d : ℕ) where
  manifold : SmoothManifold d
  primitive : manifold.Form 1
  smooth_primitive : manifold.IsSmoothForm primitive
  symplectic : manifold.IsSymplecticOn (manifold.exteriorDerivative primitive) Set.univ
  field : (x : manifold.Point) → manifold.Tangent x
  smooth_field : manifold.IsSmoothVectorField field
  contraction : ∀ x v,
    evalTwo (manifold.exteriorDerivative primitive) x (field x) v = evalOne primitive x v
  completeFlow : CompleteLiouvilleFlow manifold field

theorem CompleteLiouvilleManifold.field_eq_liouvilleVector {d : ℕ}
    (X : CompleteLiouvilleManifold d) (x : X.manifold.Point) :
    X.field x = X.manifold.liouvilleVector X.primitive x :=
  (X.manifold.liouvilleVector_eq X.primitive x (X.symplectic.2.2 x (Set.mem_univ x))
    (X.contraction x)).symm

/-- An actual smooth completion realization. The end is parametrized by the
same complete flow from the compact boundary, and has exactly `exp(r) alpha`.
The inclusion extends to an open neighbourhood of the compact piece. -/
structure Completion {d : ℕ} (D : LiouvilleDomain d) where
  ambient : CompleteLiouvilleManifold d
  inclusion : D.domain.extension.SmoothEmbedding ambient.manifold
  primitive_on_domain : ∀ x ∈ D.domain.carrier,
    D.domain.extension.pullback ambient.manifold inclusion.map ambient.primitive x =
      D.liouville.primitive x
  field_on_domain : ∀ x ∈ D.domain.carrier,
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) inclusion.map x (D.liouville.field x) =
      ambient.field (inclusion.map x)
  endMap : D.domain.boundary.Point × ℝ → ambient.manifold.Point
  smooth_endMap : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
    (𝓘(ℝ, Model d)) ∞ endMap
  end_flow : ∀ x r, endMap (x, r) = ambient.completeFlow.flow r
    (inclusion.map (D.domain.boundaryInclusion.map x))
  end_embedding : Topology.IsEmbedding (fun p : D.domain.boundary.Point × Set.Ici (0 : ℝ) =>
    endMap (p.1, p.2))
  end_immersion : ∀ p : D.domain.boundary.Point × ℝ, Function.Injective
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d)) endMap p)
  end_primitive : ∀ (x : D.domain.boundary.Point) (r : ℝ) (v : Model (d - 1)) (s : ℝ),
    evalOne ambient.primitive (endMap (x, r))
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d)) endMap (x, r) (v, s)) =
    Real.exp r * evalOne (D.domain.boundaryForm D.liouville.primitive) x v
  covering : inclusion.map '' D.domain.carrier ∪
    endMap '' (Set.univ ×ˢ Set.Ici (0 : ℝ)) = Set.univ
  overlap : ∀ x r, 0 < r → endMap (x, r) ∉ inclusion.map '' D.domain.carrier

namespace Completion

/-- The full intrinsic core uses the complete flow of this very completion. -/
def core {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) : Set D.domain.extension.Point :=
  {x | x ∈ D.domain.carrier ∧ ∀ t : ℝ, 0 ≤ t →
    C.ambient.completeFlow.flow t (C.inclusion.map x) ∈ C.inclusion.map '' D.domain.carrier}

theorem image_core_eq_flowCore {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    C.inclusion.map '' C.core =
      FsFltz.flowCore C.ambient.completeFlow.flow (C.inclusion.map '' D.domain.carrier) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.2
  · intro hy
    obtain ⟨x, hx, rfl⟩ := FsFltz.flowCore_subset _ _ hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- The nested-image formula is proved for the flow of this actual smooth
completion, using the foundational all-real-time flow theorem. -/
theorem image_core_eq_iInter_image {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    C.inclusion.map '' C.core = ⋂ t : {t : ℝ // 0 ≤ t},
      C.ambient.completeFlow.flow (-t.val) '' (C.inclusion.map '' D.domain.carrier) := by
  rw [C.image_core_eq_flowCore, FsFltz.flowCore_eq_iInter_image]

end Completion

/-- Primitive-preserving smooth marking onto a specified completed ambient,
with its precise inclusion on the compact domain. -/
structure InclusionMarking {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (X : CompleteLiouvilleManifold d) (i : D.domain.Point → X.manifold.Point) where
  equiv : C.ambient.manifold.SmoothEquiv X.manifold
  primitive : C.ambient.manifold.pullback X.manifold equiv X.primitive = C.ambient.primitive
  inclusion : ∀ x : D.domain.Point, equiv (C.inclusion.map x.val) = i x
  flow_induced : ∀ (x : D.domain.boundary.Point) (r : ℝ),
    equiv (C.endMap (x, r)) = X.completeFlow.flow r
      (equiv (C.inclusion.map (D.domain.boundaryInclusion.map x)))

/-- A compact witnessed pair with a full smooth ribbon presentation and both
actual completion realizations. No chain or core equality is a field. -/
structure WitnessedPair (n : ℕ) where
  ambientDomain : LiouvilleDomain (2 * n)
  ribbonDomain : LiouvilleDomain (2 * n - 2)
  ribbonEmbedding : ribbonDomain.domain.extension.SmoothEmbedding ambientDomain.domain.boundary
  witness : ambientDomain.domain.boundary.Point → ℝ
  smooth_witness : ContMDiff (𝓘(ℝ, Model (2 * n - 1))) (𝓘(ℝ, ℝ)) ∞ witness
  positive_witness : ∀ x, 0 < witness x
  ribbon_primitive : ∀ x ∈ ribbonDomain.domain.carrier,
    ribbonDomain.domain.extension.pullback ambientDomain.domain.boundary ribbonEmbedding.map
      (fun y => witness y • ambientDomain.domain.boundaryForm ambientDomain.liouville.primitive y) x =
      ribbonDomain.liouville.primitive x
  ambientCompletion : Completion ambientDomain
  ribbonCompletion : Completion ribbonDomain

namespace WitnessedPair

def embeddedCore {n : ℕ} (P : WitnessedPair n) : Set P.ambientDomain.domain.boundary.Point :=
  P.ribbonEmbedding.map '' P.ribbonCompletion.core

end WitnessedPair

end FsFltz.Geometry
