import FsFltz.Geometry.IntrinsicNativeIndependentEndpointIdentification
import FsFltz.Geometry.MaslovClassPullback
import FsFltz.Geometry.MaslovChain

/-!
# Native grading homotopies on the same completion identification

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–234, and
`sec:lean`, lines 788–814. A supplied grading homotopy on the original
completed ambients is pulled through the retained native slice maps. Its
actual almost complex family and squared tensor family are preserved by
pullback, with joint smoothness proved by `MaslovFamily.pullback`.

The ambient equation retained by the independent-endpoint producers indexes
this grading lift by their very completion identification. The three-step
consumer decorates the same two deformations and the same middle map, with
one literal representative at each junction. Existence of original grading
homotopies, graded deformations and prescribed toric endpoint classes remains
an additional geometric obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry

namespace MaslovCompletionLift

variable {n : ℕ} {M N X Y : SmoothManifold (2 * n)}
  {eta : M.Form 2} {eta' : N.Form 2}
  (S : X.SmoothEquiv M) (S' : Y.SmoothEquiv N) (Ψ : X.SmoothEquiv Y)
  (source : MaslovRepresentative M eta) (target : MaslovRepresentative N eta')
  (L : MaslovCompletionLift X Y (X.pullback M S eta) (Y.pullback N S' eta')
    Ψ (source.pullback S) (target.pullback S'))

/-- Transport the supplied native homotopy through the actual two slice
comparisons. Its entire represented family is the pullback along `S.symm`;
no choice of a replacement homotopy or class representative is made. -/
def conjugate :
    MaslovCompletionLift M N eta eta' ((S.symm.trans Ψ).trans S') source target where
  family :=
    { L.family.pullback S.symm with
      compatible := fun t ht => by
        have h := (L.family.pullback S.symm).compatible t ht
        change IsCompatibleAlmostComplex M
          (M.pullback X S.symm (X.pullback M S eta))
          (pullbackAlmostComplex M X S.symm (L.family.J t)) at h
        rw [X.pullback_symm_pullback M S eta] at h
        exact h }
  sourceJ := by
    change pullbackAlmostComplex M X S.symm (L.family.J 0) = _
    rw [L.sourceJ]
    change pullbackAlmostComplex M X S.symm (pullbackAlmostComplex X M S source.J) = _
    rw [← pullbackAlmostComplex_trans, S.symm_trans_self, pullbackAlmostComplex_refl]
  targetJ := by
    change pullbackAlmostComplex M X S.symm (L.family.J 1) = _
    rw [L.targetJ]
    change pullbackAlmostComplex M X S.symm
      (pullbackAlmostComplex X Y Ψ (pullbackAlmostComplex Y N S' target.J)) = _
    rw [← pullbackAlmostComplex_trans, ← pullbackAlmostComplex_trans]
  sourceSection := by
    change pullbackSquaredTensor M X S.symm (L.family.tensor 0) = _
    rw [L.sourceSection]
    change pullbackSquaredTensor M X S.symm (pullbackSquaredTensor X M S source.tensor) = _
    rw [← pullbackSquaredTensor_trans, S.symm_trans_self, pullbackSquaredTensor_refl]
  targetSection := by
    change pullbackSquaredTensor M X S.symm (L.family.tensor 1) = _
    rw [L.targetSection]
    change pullbackSquaredTensor M X S.symm
      (pullbackSquaredTensor X Y Ψ (pullbackSquaredTensor Y N S' target.tensor)) = _
    rw [← pullbackSquaredTensor_trans, ← pullbackSquaredTensor_trans]

@[simp] theorem conjugate_family_J (t : ℝ) :
    (L.conjugate S S' Ψ source target).family.J t =
      pullbackAlmostComplex M X S.symm (L.family.J t) := rfl

@[simp] theorem conjugate_family_tensor (t : ℝ) :
    (L.conjugate S S' Ψ source target).family.tensor t =
      pullbackSquaredTensor M X S.symm (L.family.tensor t) := rfl

end MaslovCompletionLift

namespace CompletionIdentification

variable {n : ℕ} {P Q : WitnessedPair n}
  (I : CompletionIdentification P Q)
  (X Y : SmoothManifold (2 * n))
  (S : X.SmoothEquiv P.ambientManifold) (S' : Y.SmoothEquiv Q.ambientManifold)
  (Ψ : X.SmoothEquiv Y) (hI : I.ambientEquiv = (S.symm.trans Ψ).trans S')
  (source : P.Maslov) (target : Q.Maslov)
  (L : MaslovCompletionLift X Y
    (X.pullback P.ambientManifold S P.ambientSymplecticForm)
    (Y.pullback Q.ambientManifold S' Q.ambientSymplecticForm)
    Ψ (source.pullback S) (target.pullback S'))

/-- The ambient equality retained by the native endpoint producer makes the
transported original homotopy a lift of that exact completion identification. -/
def gradedLiftOfNativeConjugation : GradedCompletionIdentification I source target where
  family := (L.conjugate S S' Ψ source target).family
  sourceJ := (L.conjugate S S' Ψ source target).sourceJ
  targetJ := by rw [hI]; exact (L.conjugate S S' Ψ source target).targetJ
  sourceSection := (L.conjugate S S' Ψ source target).sourceSection
  targetSection := by rw [hI]; exact (L.conjugate S S' Ψ source target).targetSection

@[simp] theorem gradedLiftOfNativeConjugation_family_J (t : ℝ) :
    (I.gradedLiftOfNativeConjugation X Y S S' Ψ hI source target L).family.J t =
      pullbackAlmostComplex P.ambientManifold X S.symm (L.family.J t) := rfl

@[simp] theorem gradedLiftOfNativeConjugation_family_tensor (t : ℝ) :
    (I.gradedLiftOfNativeConjugation X Y S S' Ψ hI source target L).family.tensor t =
      pullbackSquaredTensor P.ambientManifold X S.symm (L.family.tensor t) := rfl

end CompletionIdentification

namespace PairDeformation

/-- Supplied native junction grading and the two supplied deformation lifts
decorate the exact three-step geometric path. The middle graded lift is
constructed by native conjugation and shares its endpoint representatives
literally with the two deformation lifts. -/
def gradedThreeStepChainOfNativeConjugation {n : ℕ} (F G : PairDeformation n)
    (I : CompletionIdentification F.target G.source)
    (X Y : SmoothManifold (2 * n))
    (S : X.SmoothEquiv F.target.ambientManifold)
    (S' : Y.SmoothEquiv G.source.ambientManifold)
    (Ψ : X.SmoothEquiv Y) (hI : I.ambientEquiv = (S.symm.trans Ψ).trans S')
    (s₀ : F.source.Maslov) (s₁ : F.target.Maslov)
    (s₂ : G.source.Maslov) (s₃ : G.target.Maslov)
    (LF : GradedPairDeformation F s₀ s₁) (LG : GradedPairDeformation G s₂ s₃)
    (L : MaslovCompletionLift X Y
      (X.pullback F.target.ambientManifold S F.target.ambientSymplecticForm)
      (Y.pullback G.source.ambientManifold S' G.source.ambientSymplecticForm)
      Ψ (s₁.pullback S) (s₂.pullback S')) :
    GradedComparisonChain F.source
      (((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
        (ComparisonStep.identification I)).cons (ComparisonStep.deformation G)) s₀ s₃ :=
  ((GradedComparisonChain.nil s₀).cons (.deformation LF)).cons
    (.identification (I.gradedLiftOfNativeConjugation X Y S S' Ψ hI s₁ s₂ L)) |>.cons
      (.deformation LG)

end PairDeformation

end FsFltz.Geometry
