import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints

/-!
# Grade a chosen pair deformation with its completed Maslov family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–244; and `sec:lean`, lines 788–814.
The family on the fixed completed source is transported through the inverse
of each specified completion presentation to construct actual slice
representatives. Pulling them back through the same presentations recovers
the original family, including at time zero. This supplies a grade on the
literal chosen deformation, with exactly the supplied family.

This conditional foundation supplies no geometric comparison chain or
prescribed toric endpoint class for `thm:target`, lines 352–435.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.PairDeformation

variable {n : ℕ} (Q : PairDeformation n)

/-- Exterior naturality identifies the symplectic form of an actual slice
after pulling back along its specified completion presentation. -/
theorem pullback_ambientSymplecticForm (s : Parameter) :
    Q.source.ambientManifold.pullback (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientSymplecticForm =
        Q.completedSymplecticExtension s.val := by
  rw [Q.completedSymplecticExtension_apply]
  exact (Q.source.ambientManifold.exteriorDerivative_pullback (Q.pair s).ambientManifold
    (Q.ambientCompletionPresentation s).equiv.toContMDiffMap
    (Q.pair s).ambientCompletion.ambient.primitive
    (Q.pair s).ambientCompletion.ambient.smooth_primitive).symm

/-- The inverse of the actual completion presentation transports the
completed family form to the slice form. -/
theorem pullback_completedSymplecticExtension (s : Parameter) :
    (Q.pair s).ambientManifold.pullback Q.source.ambientManifold
      (Q.ambientCompletionPresentation s).equiv.symm (Q.completedSymplecticExtension s.val) =
        (Q.pair s).ambientSymplecticForm := by
  rw [← Q.pullback_ambientSymplecticForm s]
  exact Q.source.ambientManifold.pullback_symm_pullback (Q.pair s).ambientManifold
    (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientSymplecticForm

/-- The representative on every actual completed pair slice, constructed
from the given family through its inverse completion presentation. -/
def maslovFamilyRepresentative
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (s : Parameter) : (Q.pair s).Maslov :=
  (f.representative s).pullbackTo (Q.ambientCompletionPresentation s).equiv.symm
    (Q.pullback_completedSymplecticExtension s)

/-- Every slice representative recovers the original complex field under
the same completion presentation. -/
theorem maslovFamilyRepresentative_pullbackJ
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (s : Parameter) :
    f.J s.val = pullbackAlmostComplex Q.source.ambientManifold (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv (Q.maslovFamilyRepresentative f s).J := by
  change f.J s.val = pullbackAlmostComplex Q.source.ambientManifold (Q.pair s).ambientManifold
    (Q.ambientCompletionPresentation s).equiv
    (pullbackAlmostComplex (Q.pair s).ambientManifold Q.source.ambientManifold
      (Q.ambientCompletionPresentation s).equiv.symm (f.J s.val))
  rw [← pullbackAlmostComplex_trans, Diffeomorph.self_trans_symm, pullbackAlmostComplex_refl]

/-- Every tensor slot is recovered under the same completion presentation. -/
theorem maslovFamilyRepresentative_pullbackTensor
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (s : Parameter) :
    f.tensor s.val = pullbackSquaredTensor Q.source.ambientManifold (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv (Q.maslovFamilyRepresentative f s).tensor := by
  change f.tensor s.val = pullbackSquaredTensor Q.source.ambientManifold (Q.pair s).ambientManifold
    (Q.ambientCompletionPresentation s).equiv
    (pullbackSquaredTensor (Q.pair s).ambientManifold Q.source.ambientManifold
      (Q.ambientCompletionPresentation s).equiv.symm (f.tensor s.val))
  rw [← pullbackSquaredTensor_trans, Diffeomorph.self_trans_symm, pullbackSquaredTensor_refl]

/-- Grade this very deformation using exactly the supplied completed family
and the representatives derived from its actual endpoint presentations. -/
def gradedOfMaslovFamily
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension) :
    GradedPairDeformation Q (Q.maslovFamilyRepresentative f parameterZero)
      (Q.maslovFamilyRepresentative f parameterOne) where
  etaExtension := Q.completedSymplecticExtension
  eta_agrees := Q.completedSymplecticExtension_apply
  family := f
  sourceJ := Q.maslovFamilyRepresentative_pullbackJ f parameterZero
  targetJ := Q.maslovFamilyRepresentative_pullbackJ f parameterOne
  sourceTensor := Q.maslovFamilyRepresentative_pullbackTensor f parameterZero
  targetTensor := Q.maslovFamilyRepresentative_pullbackTensor f parameterOne

@[simp] theorem gradedOfMaslovFamily_etaExtension
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension) :
    (Q.gradedOfMaslovFamily f).etaExtension = Q.completedSymplecticExtension := rfl

@[simp] theorem gradedOfMaslovFamily_family
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension) :
    (Q.gradedOfMaslovFamily f).family = f := rfl

end FsFltz.Geometry.PairDeformation
