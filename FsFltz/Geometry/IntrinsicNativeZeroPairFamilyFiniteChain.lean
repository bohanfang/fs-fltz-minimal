import FsFltz.Geometry.IntrinsicNativeZeroPairFamilyRealization
import FsFltz.Geometry.PairFamilyFiniteChain

/-!
# Finite forward chains from original zero-ribbon families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`g:chain`, lines 385–413; and `sec:lean`, lines 788–814.
Every original family is realized once, retaining its full completed-family
and supplied-marking correspondence. The full finite ribbon equals its core. The original ambient primitive,
full ribbon embedding and witness at consecutive endpoints agree. These
native equalities construct a strict identification on the exact independent
presentations; zero-dimensional primitive scaling follows from vanishing forms. The finite chain
keeps all these chosen arrows and all independent endpoint tuples.

This is an arbitrary finite fixed-source foundation, not independently
trivialized bundle transitions, existence of a toric chain, a full-fiber
marking, FLTZ core equality, or prescribed grading existence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- Exact laws of a constructed native junction, on every full ribbon,
boundary witness, compact ambient point and all-real end radius. -/
def OriginalNativeZeroPairFamilyJunctionLaws
    {D E : OriginalNativeZeroPairFamily (A := A) (M := M)}
    (L : OriginalNativeZeroPairFamilyRealization D)
    (R : OriginalNativeZeroPairFamilyRealization E)
    (I : CompletionIdentification L.deformation.target R.deformation.source) : Prop :=
  I.scale = 1 ∧
  (∀ x, I.ribbonEquiv.map (L.presentation.ribbonEquiv parameterOne x).val =
    (R.presentation.ribbonEquiv parameterZero x).val) ∧
  (∀ x, I.ribbonEquiv.inverse (R.presentation.ribbonEquiv parameterZero x).val =
    (L.presentation.ribbonEquiv parameterOne x).val) ∧
  (∀ x, I.boundaryEquiv (L.presentation.boundaryEquiv parameterOne x) =
    R.presentation.boundaryEquiv parameterZero x) ∧
  (∀ x, I.shift x = 0) ∧
  (∀ x, R.deformation.source.witness (I.boundaryEquiv x) = L.deformation.target.witness x) ∧
  (∀ x, I.ambientEquiv
    (L.deformation.target.ambientCompletion.inclusion.map (L.presentation.ambientEquiv parameterOne x).val) =
      R.deformation.source.ambientCompletion.inclusion.map (R.presentation.ambientEquiv parameterZero x).val) ∧
  (∀ x, I.ambientEquiv.symm
    (R.deformation.source.ambientCompletion.inclusion.map (R.presentation.ambientEquiv parameterZero x).val) =
      L.deformation.target.ambientCompletion.inclusion.map (L.presentation.ambientEquiv parameterOne x).val) ∧
  (∀ x r, I.ambientEquiv
    (L.deformation.target.ambientCompletion.endMap (L.presentation.boundaryEquiv parameterOne x, r)) =
      R.deformation.source.ambientCompletion.endMap (R.presentation.boundaryEquiv parameterZero x, r))

/-- Original endpoint equality constructs the full zero-ribbon junction
on the exact independent completed realizations. -/
theorem OriginalNativeZeroPairFamilyRealization.exists_junction
    {D E : OriginalNativeZeroPairFamily (A := A) (M := M)}
    (L : OriginalNativeZeroPairFamilyRealization D)
    (R : OriginalNativeZeroPairFamilyRealization E)
    (hlamJ : D.lam parameterOne = E.lam parameterZero)
    (hjJ : D.j parameterOne = E.j parameterZero)
    (hbJ : D.b parameterOne = E.b parameterZero) :
    ∃ I : CompletionIdentification L.deformation.target R.deformation.source,
      OriginalNativeZeroPairFamilyJunctionLaws L R I := by
  have hLeft := L.presentation.presentation parameterOne
  have hRight := R.presentation.presentation parameterZero
  obtain ⟨I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend⟩ := CompletionIdentification.exists_of_same_native_zero_pair
      L.deformation.target R.deformation.source
      (D.lam parameterOne) (D.hlam.slice parameterOne) (D.hnd parameterOne) (D.hout parameterOne)
      (L.presentation.ambientEquiv parameterOne) (R.presentation.ambientEquiv parameterZero)
      (L.presentation.ribbonEquiv parameterOne) (R.presentation.ribbonEquiv parameterZero)
      (L.presentation.boundaryEquiv parameterOne) (R.presentation.boundaryEquiv parameterZero)
      hLeft.ambient_primitive
      (by simpa only [PairDeformation.source, hlamJ] using hRight.ambient_primitive)
      hLeft.ambient_coordinates hRight.ambient_coordinates
      hLeft.boundary_inclusion hRight.boundary_inclusion
      (D.j parameterOne) hLeft.ribbon_embedding
      (by simpa only [PairDeformation.source, hjJ] using hRight.ribbon_embedding)
      (D.b parameterOne) hLeft.witness
      (by simpa only [PairDeformation.source, hbJ] using hRight.witness)
  exact ⟨I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend⟩

/-- A nonempty finite forward run of original rank-one families constructs
its exact comparison chain, preserving the entire completion and marking
correspondence on each chosen family. Empty general ribbons are permitted;
the target's nonempty far-fiber assertion is a separate geometric obligation. -/
theorem exists_originalNativeZeroPairFamily_finiteJunctionChain
    (m : ℕ) (D : Fin (m + 1) → OriginalNativeZeroPairFamily (A := A) (M := M))
    (hlam : ∀ i : Fin m, (D i.castSucc).lam parameterOne = (D i.succ).lam parameterZero)
    (hj : ∀ i : Fin m, (D i.castSucc).j parameterOne = (D i.succ).j parameterZero)
    (hb : ∀ i : Fin m, (D i.castSucc).b parameterOne = (D i.succ).b parameterZero) :
    ∃ R : ∀ i, OriginalNativeZeroPairFamilyRealization (D i),
    ∃ I : ∀ i : Fin m,
      CompletionIdentification (R i.castSucc).deformation.target (R i.succ).deformation.source,
      (∀ i, OriginalNativeZeroPairFamilyJunctionLaws (R i.castSucc) (R i.succ) (I i)) ∧
    ∃ path : ComparisonChain (R 0).deformation.source (R (Fin.last m)).deformation.target,
      path = PairDeformation.finiteJunctionChain m (fun i => (R i).deformation) I ∧
      path.length = 2 * m + 1 ∧
      path.vertices = (List.ofFn (fun i => (R i).deformation)).flatMap
        (fun Q => [Q.source, Q.target]) := by
  classical
  let R := fun i => Classical.choice (D i).exists_realization
  have hJ (i : Fin m) := (R i.castSucc).exists_junction (R i.succ) (hlam i) (hj i) (hb i)
  choose I hI using hJ
  exact ⟨R, I, hI, PairDeformation.finiteJunctionChain m (fun i => (R i).deformation) I,
    rfl, PairDeformation.finiteJunctionChain_length m _ _,
    PairDeformation.finiteJunctionChain_vertices m _ _⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
