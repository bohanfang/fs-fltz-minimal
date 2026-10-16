import FsFltz.Geometry.IntrinsicShrinkingPairLocalization

/-!
# A constructed finite shrinking comparison into a core neighborhood

Source: `geometric-part-fsf-proof.tex`, `lem:shrinking`, lines 470–488,
and `subsec:junction`, lines 1876–1892. Compactness gives a finite time;
the native moving-pair construction supplies the actual permitted comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace WitnessedPair

/-- A full-ribbon neighborhood consequence using an actual continuous map
from its specified completion. Every prescribed ambient grading travels on
the very same finite comparison, and the endpoint contains the entire ribbon. -/
theorem exists_shrinking_into {n a : ℕ} (P : WitnessedPair n)
    (hP : P.ribbonDomain.domain.carrier.Nonempty) (X : SmoothManifold a)
    (A : P.ambientDomain.domain.boundary.SmoothEmbedding X)
    (g : P.ribbonCompletion.ambient.manifold.Point → X.Point) (hg : Continuous g)
    (hcompact : ∀ x ∈ P.ribbonDomain.domain.carrier,
      g (P.ribbonCompletion.inclusion.map x) = A.map (P.ribbonEmbedding.map x))
    (W : TopologicalSpace.Opens X.Point)
    (hcore : (A.comp P.ribbonEmbedding).map '' P.ribbonCompletion.core ⊆ W) :
    ∃ (Q : WitnessedPair n) (B : Q.ambientDomain.domain.boundary.SmoothEmbedding X)
      (chain : ComparisonChain P Q),
      Q.ambientDomain = P.ambientDomain ∧
      Q.ambientCompletion.ambient = P.ambientCompletion.ambient ∧
      (∀ datum : P.Maslov, ∃ target : Q.Maslov,
        Nonempty (GradedComparisonChain P chain datum target)) ∧
      ((B.comp Q.ribbonEmbedding).map '' Q.ribbonDomain.domain.carrier ⊆ W) ∧
      (B.comp Q.ribbonEmbedding).map '' Q.ribbonCompletion.core =
        (A.comp P.ribbonEmbedding).map '' P.ribbonCompletion.core := by
  let C := P.ribbonCompletion
  let F := C.ambient.completeFlow.flow
  let K := C.inclusion.map '' P.ribbonDomain.domain.carrier
  have hK : IsCompact K := P.ribbonDomain.domain.compact.image C.inclusion.map.contMDiff.continuous
  have hneg : IsForwardInvariant F.reverse K := fun _ ht _ hx => C.negative_flow_mem hx ht
  have hC : FsFltz.flowCore F K ⊆ g ⁻¹' (W : Set X.Point) := by
    intro y hy
    rw [← C.image_core_eq_flowCore] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change g (C.inclusion.map x) ∈ W
    rw [hcompact x hx.1]
    exact hcore ⟨x, hx, rfl⟩
  obtain ⟨T, hT, htime⟩ := FsFltz.exists_negative_image_subset F hK hneg
    (W.isOpen.preimage hg) hC
  obtain ⟨J, U, hJ, hU, hdefined⟩ := C.exists_shrinking_neighborhood T hT
  obtain ⟨x, hx⟩ := hP
  let x₀ : U := ⟨x, hU hx⟩
  let D := P.shrinkingDeformation U hU T hT J hJ hdefined
  let B : D.target.ambientDomain.domain.boundary.SmoothEmbedding X := A
  refine ⟨D.target, B, P.shrinkingChain U hU x₀ T hT J hJ hdefined, rfl, rfl, ?_, ?_, ?_⟩
  · intro datum
    exact ⟨datum, ⟨P.gradedShrinkingChain U hU x₀ T hT J hJ hdefined datum⟩⟩
  · rintro y ⟨z, hz, rfl⟩
    let q := C.shrinkingLift T parameterOne.val z.val
    have hq : q ∈ P.ribbonDomain.domain.carrier := C.shrinkingLift_mem_carrier T hT parameterOne z.val hz
    change A.map (P.ribbonEmbedding.map q) ∈ W
    rw [← hcompact q hq]
    have hi := C.inclusion_shrinkingLift T parameterOne.val z.val
      (hdefined parameterOne.val (hJ parameterOne.property) z.val z.property)
    change C.inclusion.map q = F (-(T * parameterOne.val)) (C.inclusion.map z.val) at hi
    rw [hi]
    simp only [parameterOne, mul_one]
    exact htime ⟨C.inclusion.map z.val, ⟨z.val, hz, rfl⟩, rfl⟩
  · change (A.map ∘ D.target.ribbonEmbedding.map) '' D.target.ribbonCompletion.core =
      (A.map ∘ P.ribbonEmbedding.map) '' P.ribbonCompletion.core
    simpa only [WitnessedPair.embeddedCore, Set.image_image, Function.comp_def,
      D, PairDeformation.target] using
      congrArg (fun S => A.map '' S)
        (P.shrinkingDeformation_embeddedCore U hU T hT J hJ hdefined parameterOne)

end WitnessedPair
end FsFltz.Geometry
