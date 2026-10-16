import FsFltz.Geometry.TailoringStrictAmbientComparison
import FsFltz.Geometry.PotentialTailoringMarkedChain

/-!
# The strict marked comparison into the same hitting outer completion

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1905.
The existing outer marking is composed with the proved comparison between
its chosen collar completion and the chosen hitting collar completion.
Native compact inclusions agree pointwise. No comparison map is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Retain the existing rounded inclusion marking and construct its strict
comparison to any collar completion of the same outer compact primitive.
Native containment proves that every rounded compact point uses the compact
comparison formula, including all boundary ribbon points. -/
theorem OuterAmbientInclusionMarkingFamily.exists_marking_into_same_primitive_collar
    {n : ℕ} {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {ρ : LGSpace n → ℝ} {α : Parameter → (lgManifold n).Form 1}
    (O : OuterAmbientInclusionMarkingFamily Q J ρ α)
    (L : LiouvilleStructure O.domain)
    (C : (⟨O.domain, L⟩ : LiouvilleDomain (2 * n)).FlowCollar)
    (hD : O.domain.carrier.Nonempty)
    (hprimitive : (O.liouville parameterOne).primitive = L.primitive)
    (hsource : ∀ x ∈ Q.target.ambientDomain.domain.carrier, ρ ((J parameterOne).map x) ≤ 0) :
    ∃ i : Q.target.ambientDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point,
      ∃ _q : InclusionMarking Q.target.ambientCompletion C.cylindricalCompletion.ambient i,
        ∀ x : Q.target.ambientDomain.domain.Point,
          (O.nativeEmbedding.comp C.originalInclusion).map (i x) = (J parameterOne).map x.val := by
  let B := O.family.collars parameterOne
  obtain ⟨h, e, he, hcompact⟩ := B.exists_strictComparison_of_primitive_eq
    O.domain (O.liouville parameterOne) L C B.cylindricalCompletion C.cylindricalCompletion hD hprimitive
  have hmem (x : Q.target.ambientDomain.domain.Point) :
      O.inclusion parameterOne x ∈ B.localizedDomain.domain.carrier := by
    have hnative : (J parameterOne).map x.val ∈ O.nativeEmbedding.map '' O.domain.carrier := by
      rw [O.native_image]
      exact hsource x.val x.property
    obtain ⟨y, hy, hye⟩ := hnative
    obtain ⟨z, hz, hzy⟩ := (Set.ext_iff.mp B.image_originalInclusion_carrier y).mpr hy
    have heq : (O.nativeEmbedding.comp B.originalInclusion).map z =
        (O.nativeEmbedding.comp B.originalInclusion).map (O.inclusion parameterOne x) := by
      change O.nativeEmbedding.map (B.originalInclusion.map z) = _
      rw [hzy, hye]
      exact (O.compact_square parameterOne x).symm
    have hzx := (O.nativeEmbedding.comp B.originalInclusion).embedding.injective heq
    exact hzx ▸ hz
  let f := (O.marking parameterOne).equiv.trans e
  have hf : Q.target.ambientManifold.pullback C.cylindricalCompletion.ambient.manifold f
      C.cylindricalCompletion.ambient.primitive = Q.target.ambientCompletion.ambient.primitive := by
    change Q.target.ambientManifold.pullback C.cylindricalCompletion.ambient.manifold
      (e ∘ (O.marking parameterOne).equiv) C.cylindricalCompletion.ambient.primitive = _
    rw [Q.target.ambientManifold.pullback_comp B.cylindricalCompletion.ambient.manifold
      C.cylindricalCompletion.ambient.manifold
      ((O.marking parameterOne).equiv.contMDiff.mdifferentiable (by simp))
      (e.contMDiff.mdifferentiable (by simp)), he]
    exact (O.marking parameterOne).primitive
  let i : Q.target.ambientDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point :=
    fun x => e (O.inclusion parameterOne x)
  let q : InclusionMarking Q.target.ambientCompletion C.cylindricalCompletion.ambient i :=
    { equiv := f
      primitive := hf
      inclusion := fun x => congrArg e ((O.marking parameterOne).inclusion x)
      flow_induced := by
        intro b r
        rw [Q.target.ambientCompletion.end_flow]
        exact Q.target.ambientCompletion.ambient.map_flow C.cylindricalCompletion.ambient f hf _ r }
  refine ⟨i, q, ?_⟩
  intro x
  obtain ⟨hproj, hecompact⟩ := hcompact (O.inclusion parameterOne x) (hmem x)
  change e (O.inclusion parameterOne x) = h.map (O.inclusion parameterOne x) at hecompact
  change O.nativeEmbedding.map (C.originalInclusion.map (e (O.inclusion parameterOne x))) = _
  rw [hecompact, hproj]
  exact O.compact_square parameterOne x

/-- The actual retained prefix supplies native containment and nonemptiness
of the outer domain. Thus only the same hitting slice's explicit native
primitive is needed to construct its strict comparison with the old rounded
completion. No nesting or strict-junction hypothesis is added. -/
theorem PotentialTailoringMarkedPrefix.exists_marking_into_hitting_collar
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (L : LiouvilleStructure P.tailoring_ambient_marking.domain)
    (C : (⟨P.tailoring_ambient_marking.domain, L⟩ : LiouvilleDomain (2 * n)).FlowCollar)
    (hL : L.primitive = P.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
      P.tailoring_ambient_marking.nativeEmbedding.map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) :
    ∃ i : P.tailoring.deformation.target.ambientDomain.domain.Point →
      C.cylindricalCompletion.ambient.manifold.Point,
      ∃ _q : InclusionMarking P.tailoring.deformation.target.ambientCompletion
        C.cylindricalCompletion.ambient i,
        ∀ x : P.tailoring.deformation.target.ambientDomain.domain.Point,
          (P.tailoring_ambient_marking.nativeEmbedding.comp C.originalInclusion).map (i x) =
            (P.tailoring.embedding parameterOne).map x.val := by
  let O := P.tailoring_ambient_marking
  have hsource : ∀ x ∈ P.tailoring.deformation.target.ambientDomain.domain.carrier,
      φ ((P.tailoring.embedding parameterOne).map x).1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0 := by
    intro x hx
    have hy := mem_image_of_mem (P.tailoring.embedding parameterOne).map hx
    have hy' := (Set.ext_iff.mp (P.tailoring.ambient_image parameterOne)
      ((P.tailoring.embedding parameterOne).map x)).mp hy
    exact sub_nonpos.mpr (tailoringRoundedDomain_subset I φ β 1
      (Cplus ^ 2 * β ^ 2 / 2) (Real.exp_pos β) m hy').1
  have hD : O.domain.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := P.tailoring.ambient_nonempty parameterOne
    have hy : (P.tailoring.embedding parameterOne).map x ∈
        O.nativeEmbedding.map '' O.domain.carrier := by
      rw [O.native_image]
      exact hsource x hx
    obtain ⟨y, hy, _⟩ := hy
    exact ⟨y, hy⟩
  have hp : (O.liouville parameterOne).primitive = L.primitive :=
    (O.native_primitive parameterOne).trans hL.symm
  exact O.exists_marking_into_same_primitive_collar L C hD hp hsource

end FsFltz
