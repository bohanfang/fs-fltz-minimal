import FsFltz.Geometry.NativeCompletionJunction

/-!
# Original homotopies on the actual native completion junction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199;
`def:maslov`, lines 212–234; `g:chain`, lines 398–413; and
`sec:lean`, lines 788–814. Original endpoint representatives and an
original homotopy are compared with the retained endpoint presentations.
The differential and full-tensor comparison laws produce representative
pullback equalities; primitive preservation produces the symplectic
pullback identities. The resulting grading lift is on the exact permitted
identification constructed from the original whole-ribbon data.

This is a conditional foundational bridge. It assumes the original
geometric junction and original smooth homotopy, and proves their
representation on the independently chosen endpoints. It asserts no toric
chain, full-fiber marking, full-core equality, or prescribed endpoint class.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry

/-- Native differential intertwinement determines the actual pullback
complex structure, by injectivity of the comparison differential. -/
theorem almostComplex_eq_pullback_of_nativeIntertwines {n : ℕ}
    (X M : SmoothManifold (2 * n)) (S : X.SmoothEquiv M)
    (Jnative : AlmostComplexField X) (J : AlmostComplexField M)
    (hJ : ∀ x v,
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x (Jnative x v) =
        J (S x) (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x v)) :
    Jnative = pullbackAlmostComplex X M S J := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply (S.mfderivToContinuousLinearEquiv (by simp) x).injective
  change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x (Jnative x v) =
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x
      (pullbackAlmostComplex X M S J x v)
  rw [pullbackAlmostComplex_intertwines]
  exact hJ x v

namespace NativeAmbientJunction

variable {n : ℕ} {P Q : WitnessedPair n} (A : NativeAmbientJunction P Q)

/-- The original source primitive equation determines its symplectic form;
there is no separately assumed two-form compatibility certificate. -/
theorem sourceSymplectic :
    A.X.exteriorDerivative A.α =
      A.X.pullback P.ambientManifold A.S P.ambientSymplecticForm := by
  rw [← A.sourcePrimitive]
  exact A.X.exteriorDerivative_pullback P.ambientManifold A.S.toContMDiffMap
    P.ambientCompletion.ambient.primitive P.ambientCompletion.ambient.smooth_primitive

/-- The same primitive naturality identifies the original target form. -/
theorem targetSymplectic :
    A.Y.exteriorDerivative A.β =
      A.Y.pullback Q.ambientManifold A.S' Q.ambientSymplecticForm := by
  rw [← A.targetPrimitive]
  exact A.Y.exteriorDerivative_pullback Q.ambientManifold A.S'.toContMDiffMap
    Q.ambientCompletion.ambient.primitive Q.ambientCompletion.ambient.smooth_primitive

/-- Smoothness of the original target primitive follows from its actual
comparison with the supplied completed target primitive. -/
theorem smoothTargetPrimitive : A.Y.IsSmoothForm A.β := by
  rw [← A.targetPrimitive]
  exact A.Y.isSmoothForm_pullback_one Q.ambientManifold A.S'.toContMDiffMap
    Q.ambientCompletion.ambient.primitive
    Q.ambientCompletion.ambient.smooth_primitive

/-- The original strict map pulls back the original target symplectic form.
This is derived from strict primitive preservation and target smoothness. -/
theorem strictSymplectic :
    A.X.exteriorDerivative A.α =
      A.X.pullback A.Y A.Ψ (A.Y.exteriorDerivative A.β) := by
  rw [← A.strictPrimitive]
  exact A.X.exteriorDerivative_pullback A.Y A.Ψ.toContMDiffMap A.β
    A.smoothTargetPrimitive

/-- The represented source datum, read on the original completed ambient.
Its symplectic indexing is derived from the original primitive equation. -/
def sourceNativeRepresentative (source : P.Maslov) :
    MaslovRepresentative A.X (A.X.exteriorDerivative A.α) :=
  source.pullbackTo A.S A.sourceSymplectic.symm

/-- The represented target datum on the original target completed ambient. -/
def targetNativeRepresentative (target : Q.Maslov) :
    MaslovRepresentative A.Y (A.Y.exteriorDerivative A.β) :=
  target.pullbackTo A.S' A.targetSymplectic.symm

/-- Original source differential and tensor-slot laws identify the entire
native representative, including its compatible structure and section. -/
theorem sourceRepresentative_eq_of_nativeEquations
    (native : MaslovRepresentative A.X (A.X.exteriorDerivative A.α))
    (source : P.Maslov)
    (hJ : ∀ x v,
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S x (native.J x v) =
        source.J (A.S x)
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S x v))
    (hT : ∀ x vs, native.tensor x vs = source.tensor (A.S x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S x (vs i))) :
    native = A.sourceNativeRepresentative source := by
  apply MaslovRepresentative.ext
  · exact almostComplex_eq_pullback_of_nativeIntertwines A.X P.ambientManifold
      A.S native.J source.J hJ
  · funext x
    ext vs
    exact hT x vs

/-- Original target endpoint laws likewise identify the full representative;
no represented pullback identity is required from the caller. -/
theorem targetRepresentative_eq_of_nativeEquations
    (native : MaslovRepresentative A.Y (A.Y.exteriorDerivative A.β))
    (target : Q.Maslov)
    (hJ : ∀ x v,
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S' x (native.J x v) =
        target.J (A.S' x)
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S' x v))
    (hT : ∀ x vs, native.tensor x vs = target.tensor (A.S' x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) A.S' x (vs i))) :
    native = A.targetNativeRepresentative target := by
  apply MaslovRepresentative.ext
  · exact almostComplex_eq_pullback_of_nativeIntertwines A.Y Q.ambientManifold
      A.S' native.J target.J hJ
  · funext x
    ext vs
    exact hT x vs

end NativeAmbientJunction

namespace NativeCompletionJunction

variable {n : ℕ} {P Q : WitnessedPair n} (J : NativeCompletionJunction P Q)
  (nativeSource : MaslovRepresentative J.ambient.X
    (J.ambient.X.exteriorDerivative J.ambient.α))
  (nativeTarget : MaslovRepresentative J.ambient.Y
    (J.ambient.Y.exteriorDerivative J.ambient.β))
  (H : MaslovHomotopy nativeSource
    (nativeTarget.pullbackTo J.ambient.Ψ J.ambient.strictSymplectic.symm))
  (source : P.Maslov) (target : Q.Maslov)
  (hsourceJ : ∀ x v,
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S x
      (nativeSource.J x v) = source.J (J.ambient.S x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S x v))
  (hsourceT : ∀ x vs, nativeSource.tensor x vs = source.tensor (J.ambient.S x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S x (vs i)))
  (htargetJ : ∀ x v,
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S' x
      (nativeTarget.J x v) = target.J (J.ambient.S' x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S' x v))
  (htargetT : ∀ x vs, nativeTarget.tensor x vs = target.tensor (J.ambient.S' x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) J.ambient.S' x (vs i)))

/-- An original smooth homotopy with its actual original endpoints produces
the native grading lift. All four represented endpoint equalities are
derived from original differential and tensor-slot comparisons; a grading
lift on the represented endpoints is not input. -/
def nativeGradingOfOriginalHomotopy : J.NativeGrading source target where
  family :=
    { H.family with
      compatible := fun t ht => by
        rw [← J.ambient.sourceSymplectic]
        exact H.family.compatible t ht }
  sourceJ := by
    have hs := J.ambient.sourceRepresentative_eq_of_nativeEquations
      nativeSource source hsourceJ hsourceT
    rw [H.sourceJ, hs]
    rfl
  targetJ := by
    have ht := J.ambient.targetRepresentative_eq_of_nativeEquations
      nativeTarget target htargetJ htargetT
    rw [H.targetJ]
    change pullbackAlmostComplex J.ambient.X J.ambient.Y J.ambient.Ψ nativeTarget.J = _
    rw [ht]
    rfl
  sourceSection := by
    have hs := J.ambient.sourceRepresentative_eq_of_nativeEquations
      nativeSource source hsourceJ hsourceT
    rw [H.sourceSection, hs]
    rfl
  targetSection := by
    have ht := J.ambient.targetRepresentative_eq_of_nativeEquations
      nativeTarget target htargetJ htargetT
    rw [H.targetSection]
    change pullbackSquaredTensor J.ambient.X J.ambient.Y J.ambient.Ψ nativeTarget.tensor = _
    rw [ht]
    rfl

/-- The original homotopy decorates the identification generated from the
same original ambient and whole-ribbon maps. The existing endpoint tuples
and generated geometric identification are unchanged. -/
def gradedLiftOfOriginalHomotopy :
    GradedCompletionIdentification J.identification source target :=
  J.gradedLift (J.nativeGradingOfOriginalHomotopy nativeSource nativeTarget H
    source target hsourceJ hsourceT htargetJ htargetT)

@[simp] theorem gradedLiftOfOriginalHomotopy_family_J (t : ℝ) :
    (J.gradedLiftOfOriginalHomotopy nativeSource nativeTarget H source target
      hsourceJ hsourceT htargetJ htargetT).family.J t =
      pullbackAlmostComplex P.ambientManifold J.ambient.X J.ambient.S.symm
        (H.family.J t) := rfl

@[simp] theorem gradedLiftOfOriginalHomotopy_family_tensor (t : ℝ) :
    (J.gradedLiftOfOriginalHomotopy nativeSource nativeTarget H source target
      hsourceJ hsourceT htargetJ htargetT).family.tensor t =
      pullbackSquaredTensor P.ambientManifold J.ambient.X J.ambient.S.symm
        (H.family.tensor t) := rfl

end NativeCompletionJunction

end FsFltz.Geometry
