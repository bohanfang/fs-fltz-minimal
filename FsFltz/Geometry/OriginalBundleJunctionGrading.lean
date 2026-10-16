import FsFltz.Geometry.OriginalBundleMaslovFamily
import FsFltz.Geometry.OriginalBundleCompletionJunction

/-!
# Grading original bundle junctions on the same chosen realizations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199;
`def:maslov`, lines 212–234; `g:chain`, lines 398–413; and
`sec:lean`, lines 788–814. The original local completed maps and homotopy
are selected independently of the represented deformations. Their original
complex fields and full tensors are recovered through the actual endpoint
comparisons, and the homotopy grades the identification constructed from
those same comparisons and whole-ribbon maps.

These are conditional foundational transports. Original geometric maps,
regularity germs and homotopies remain supplied; the toric comparison,
prescribed endpoint grading and source-smooth-section correspondence remain
pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

section EndpointRecovery

variable {a n : ℕ} [NeZero n] {A : Type} [TopologicalSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  {EA : Parameter → Type*} [∀ s, TopologicalSpace (EA s)]
  [TopologicalSpace (TotalSpace A EA)]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {PA : BundlePrimitiveData (k := a) (M := A) EA}
  {LA : OriginalBundleLiouvilleLaws PA} {hdim : a + 1 = 2 * n}
  (g : Trivialization A (π A EA)) (hg : CompatibleTrivialization (𝓡∂ (a + 1)) EA g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n)
  (eAs : ∀ u, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
    (Q.pair u).ambientDomain.domain.Point ∞)
  (hp : ∀ u x, ((Q.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs u y).val) x) =
      PA.formInTrivialization g u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := a)
    (Q.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val))

/-- The fixed-source comparison followed by this very deformation's
completion presentation is the original local-to-endpoint comparison. -/
theorem localMaslovEndpointComparison_eq
    (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (LA.localCompletionFamily c t ht).base) :
    (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs).trans
      (Q.ambientCompletionPresentation s).equiv =
        CompletedMaslovDimension.comparison hdim
          ((LA.localCompletionFamily c t ht).sliceCompletion LA s).ambient
          (Q.pair s).ambientManifold
          ((LA.localCompletionFamily c t ht).ambientEndpointSliceComparison
            LA g hg hbase s hs Q hdim eAs hp hc).equiv := by
  unfold localMaslovComparison
  rw [CompletedMaslovDimension.comparison_trans]
  congr 1
  apply Diffeomorph.ext
  intro x
  exact (Q.ambientCompletionPresentation s).equiv.apply_symm_apply _

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData PA LA hdim)

/-- Original chart recovery on the actual completed endpoint, without a
new represented endpoint equation. Both canonical tensor blocks and every
slot are retained by the direct local completion comparison. -/
theorem pullback_maslovFamilyRepresentative_descended
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (hfJ : ∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase Q eAs hp hc s)
    (hfT : ∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase Q eAs hp hc s)
    (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (LA.localCompletionFamily c t ht).base) :
    let q := CompletedMaslovDimension.comparison hdim
      ((LA.localCompletionFamily c t ht).sliceCompletion LA s).ambient
      (Q.pair s).ambientManifold
      ((LA.localCompletionFamily c t ht).ambientEndpointSliceComparison
        LA g hg hbase s hs Q hdim eAs hp hc).equiv
    pullbackAlmostComplex (localMaslovAmbient hdim LA c t ht s).manifold
      (Q.pair s).ambientManifold q (Q.maslovFamilyRepresentative f s).J = S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim LA c t ht s).manifold
      (Q.pair s).ambientManifold q (Q.maslovFamilyRepresentative f s).tensor =
        S.tensor c t ht s hs := by
  obtain ⟨hJ, hT⟩ := S.pullback_maslovFamily_descended g hg hbase Q eAs hp hc f hfJ hfT
    c t ht s hs
  dsimp only
  rw [← localMaslovEndpointComparison_eq g hg hbase Q eAs hp hc c t ht s hs]
  constructor
  · rw [pullbackAlmostComplex_trans, ← Q.maslovFamilyRepresentative_pullbackJ f s]
    exact hJ
  · rw [pullbackSquaredTensor_trans, ← Q.maslovFamilyRepresentative_pullbackTensor f s]
    exact hT

end OriginalLocalCompletionMaslovData
end EndpointRecovery

section OriginalHomotopy

variable {a a' n : ℕ} [NeZero n]
  {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [ChartedSpace (EuclideanHalfSpace (a' + 1)) A']
  {EA EA' : Parameter → Type*} [∀ s, TopologicalSpace (EA s)] [∀ s, TopologicalSpace (EA' s)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  [SmoothCompactBundle (𝓡∂ (a' + 1)) (F := A') EA']
  {PA : BundlePrimitiveData (k := a) (M := A) EA}
  {PA' : BundlePrimitiveData (k := a') (M := A') EA'}
  {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
  {c : OriginalCompactChart (k := a) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := a') (M := A') (E := EA')}
  {t t' s s' : Parameter}
  {U : LocalCompletionFamily PA c t} {V : LocalCompletionFamily PA' c' t'}
  {hdim : a + 1 = 2 * n} {hdim' : a' + 1 = 2 * n}

namespace OriginalBundleAmbientJunction

variable (O : OriginalBundleAmbientJunction LA LA' U V s s' hdim hdim')

omit [NeZero n] in
/-- Primitive preservation supplies the symplectic equation of the original
strict map, before either represented endpoint is chosen. -/
theorem strictSymplectic :
    (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).manifold.exteriorDerivative
      (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).primitive =
    (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).manifold.pullback
      (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).manifold O.Ψ
      ((CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).manifold.exteriorDerivative
        (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).primitive) := by
  rw [← O.strictPrimitive]
  exact (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).manifold.exteriorDerivative_pullback
    (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).manifold
    O.Ψ.toContMDiffMap _
    (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).smooth_primitive

end OriginalBundleAmbientJunction
end OriginalHomotopy

end FsFltz.Geometry.IntrinsicSmoothBundle
