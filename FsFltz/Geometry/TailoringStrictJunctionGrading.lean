import FsFltz.Geometry.TailoringStrictJunction
import FsFltz.Geometry.MaslovClassPullback
import FsFltz.Geometry.MaslovChain

/-!
# The actual incoming strict junction with its witness grading

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1919,
and `lem:grading`, lines 1994–2030. The strict incoming identification and
the constant-ambient witness interpolation are constructed together.
The source datum is pulled through this same strict map, and the grading
uses the specified hitting-family lift as its final arrow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Raw strict map and whole-ribbon witness equations construct the incoming
junction together with an actual grading of its three specified arrows.
The induced source datum uses the same given ambient map. -/
theorem StrictHittingJunction.exists_graded_of_strict_maps {n : ℕ}
    (P : WitnessedPair n) (H : PairDeformation n)
    (e : P.ambientManifold.SmoothEquiv H.source.ambientManifold)
    (he : P.ambientManifold.pullback H.source.ambientManifold e
      H.source.ambientCompletion.ambient.primitive = P.ambientCompletion.ambient.primitive)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv H.source.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (hs : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s)
    (hend : ∀ x r, e (P.ambientCompletion.endMap (x, r)) =
      H.source.ambientCompletion.endMap (ψ x, r + s x))
    (hcontact : P.ambientDomain.domain.boundary.pullback H.source.ambientDomain.domain.boundary ψ
      (H.source.ambientDomain.domain.boundaryForm H.source.ambientDomain.liouville.primitive) =
      fun x => Real.exp (-s x) •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x)
    (h : CompactDomainDiffeomorph P.ribbonDomain.domain H.source.ribbonDomain.domain)
    (hp : ∀ x ∈ P.ribbonDomain.domain.carrier,
      P.ribbonDomain.domain.extension.pullback H.source.ribbonDomain.domain.extension h.map
        H.source.ribbonDomain.liouville.primitive x = P.ribbonDomain.liouville.primitive x)
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = H.source.ribbonEmbedding.map (h.map x))
    (hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x)
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      H.source.witness (H.source.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x))
    (u : H.source.Maslov) (v : H.target.Maslov) (gH : GradedPairDeformation H u v) :
    ∃ J : StrictHittingJunction P H,
      ∃ datum : P.Maslov,
        HEq J.identification.ambientEquiv e ∧
        datum.tensor = pullbackSquaredTensor P.ambientManifold H.source.ambientManifold e u.tensor ∧
        Nonempty (GradedComparisonChain P J.chain datum v) := by
  let Q := H.source
  let b := P.strictIncomingWitness Q ψ s
  have hb := P.strictIncomingWitness_smooth Q ψ s hs
  have hpos := P.strictIncomingWitness_positive Q ψ s
  have heq := P.strictIncomingWitness_eq_on_ribbon Q ψ s h τ hsquare hshift hwitness
  let R := Q.withWitness b hb hpos heq
  let C : CompletionIdentification P R :=
    { ambientEquiv := e
      primitive := he
      boundaryEquiv := ψ
      shift := s
      smooth_shift := hs
      induced_at_infinity := fun x => ⟨0, fun r _ => hend x r⟩
      boundary_primitive := hcontact
      ribbonEquiv := h
      scale := 1
      positive_scale := zero_lt_one
      ribbon_primitive := by
        intro x hx
        change P.ribbonDomain.domain.extension.pullback H.source.ribbonDomain.domain.extension h.map
          H.source.ribbonDomain.liouville.primitive x = 1 • P.ribbonDomain.liouville.primitive x
        simpa only [one_smul] using hp x hx
      ribbon_square := hsquare }
  let B := Q.witnessDeformation b hb hpos heq
  let J : StrictHittingJunction P H :=
    ⟨R, C, rfl, B, Q.witnessDeformation_source b hb hpos heq,
      Q.witnessDeformation_target b hb hpos heq⟩
  let datum : P.Maslov := u.pullbackTo C.ambientEquiv C.pullback_symplecticForm
  have gC : GradedCompletionIdentification C datum u := by
    let r := MaslovHomotopy.refl datum
    exact { family := r.family
            sourceJ := r.sourceJ
            targetJ := r.targetJ
            sourceSection := r.sourceSection
            targetSection := r.targetSection }
  have gW : GradedComparisonStep J.witnessStep u u := by
    have g := GradedComparisonStep.reverse
      (GradedComparisonStep.deformation (Q.gradedWitnessDeformation b hb hpos heq u))
    convert g using 1
    · exact J.interpolation_target.symm
    · exact J.interpolation_source.symm
    · unfold StrictHittingJunction.witnessStep
      exact (cast_heq _ _).trans (cast_heq _ _)
  refine ⟨J, datum, HEq.rfl, rfl, ?_⟩
  exact ⟨(((GradedComparisonChain.nil datum).cons (.identification gC)).cons gW).cons
    (.deformation gH)⟩

end FsFltz
