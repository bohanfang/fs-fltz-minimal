import FsFltz.Geometry.OriginalBundleMaslovSectionRecovery
import FsFltz.Geometry.OriginalBundleFiniteRealization

/-!
# Original pair realizations from the same independently prescribed section

Source: `geoemtric-part-fsf.tex`, `def:chain` (163–199), `def:maslov`
(212–244), and `sec:lean` (788–814). The constructors take the original
geometric bundle fields, independent completed ambient inclusion markings,
and a prescribed ambient representative. Covariant original local data and
all coframe germs are produced, then consumed by the existing full realization.
The resulting realization retains the full original geometry, actual grading,
and both marking recovery capabilities, including zero-dimensional ribbons.

Joint real-open regularity of the exact pulled source field and section graph
remains an explicit retained-base hypothesis. It is not inferred from arbitrary
parameterwise markings or slice-smooth representatives. No toric existence,
endpoint homotopy, or categorical theorem is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

section PositiveRibbon

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]
  (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
  (PA : BundlePrimitiveData (k := a) (M := A) EA)
  (PM : BundlePrimitiveData (k := k) (M := M) EM)
  (PW : BundleWitnessData (k := a) (M := A) EA)
  (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
  (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
  (LP : OriginalBundlePairLaws PA PM PW PJ)
  (Z : Parameter → CompleteLiouvilleManifold (2 * n))
  (O : OriginalBundleCompletionMarkingData LA Z)
  (σ : ∀ s, MaslovRepresentative (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))

variable
  (hJI : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalInteriorComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData hdimA σ).retainedNativeJ c t ht) F.base)
  (hJE : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalEndComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData hdimA σ).retainedNativeJ c t ht) F.base)
  (hmap : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalTotalLocalMapExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData hdimA σ).retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdimA) F.native.joint F.native.smooth F.native.inverse
      {x | parameter F.native.patches x ∈ F.base}
      (originalTotalSectionGraph F.native.collar ((O.originalMaslovData hdimA σ).retainedNativeJ c t ht)
        (interiorMaslovModelEquiv hdimA) ((O.originalMaslovData hdimA σ).retainedNativeSection c t ht)))

/-- Construct the existing original positive-ribbon bundle. The two Maslov
fields are exactly the pullbacks of the supplied representative; covariance
and all coframe/scalar germs are proved before the realization is selected. -/
def prescribedPositiveBundle : OriginalPositiveBundle a k n where
  A := A
  M := M
  EA := EA
  EM := EM
  hdimA := hdimA
  hdimM := hdimM
  PA := PA
  PM := PM
  PW := PW
  PJ := PJ
  LA := LA
  LM := LM
  LP := LP
  S := O.originalMaslovData hdimA σ
  hS := (O.originalMaslovData hdimA σ).coframeGerms_of_retainedSectionMapExtensions hJI hJE hmap

/-- The existing full realization consumes the generated original data and
coframe germs. Its geometry, grade and both marking-recovery capabilities
are retained in the complete existing realization type. -/
def prescribedPositiveRealization :
    OriginalPositiveRealization
      (prescribedPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O σ hJI hJE hmap) :=
  (prescribedPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O σ hJI hJE hmap).realize

end PositiveRibbon

section ZeroRibbon

variable {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {EA : Parameter → Type} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]
  {EM : Parameter → Type} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  (PA : BundlePrimitiveData (k := 1) (M := A) EA)
  (PW : BundleWitnessData (k := 1) (M := A) EA)
  (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
  (LA : OriginalBundleLiouvilleLaws PA)
  (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet → Function.Injective (PJ.map cM cA t))
  (μ : Parameter → (sourceManifold M).Form 1)
  (Z : Parameter → CompleteLiouvilleManifold 2)
  (O : OriginalBundleCompletionMarkingData LA Z)
  (σ : ∀ s, MaslovRepresentative (n := 1) (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))

variable
  (hJI : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalInteriorComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData (n := 1) rfl σ).retainedNativeJ c t ht) F.base)
  (hJE : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalEndComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData (n := 1) rfl σ).retainedNativeJ c t ht) F.base)
  (hmap : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasOriginalTotalLocalMapExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero ((O.originalMaslovData (n := 1) rfl σ).retainedNativeJ c t ht)
      (interiorMaslovModelEquiv (n := 1) rfl) F.native.joint F.native.smooth F.native.inverse
      {x | parameter F.native.patches x ∈ F.base}
      (originalTotalSectionGraph F.native.collar ((O.originalMaslovData (n := 1) rfl σ).retainedNativeJ c t ht)
        (interiorMaslovModelEquiv (n := 1) rfl) ((O.originalMaslovData (n := 1) rfl σ).retainedNativeSection c t ht)))

/-- The rank-one constructor produces the existing original bundle of a
finite ribbon, with the exact same prescribed ambient section. -/
def prescribedZeroBundle : OriginalZeroBundle where
  A := A
  M := M
  EA := EA
  EM := EM
  PA := PA
  PW := PW
  PJ := PJ
  LA := LA
  hPJ := hPJ
  μ := μ
  S := O.originalMaslovData (n := 1) rfl σ
  hS := (O.originalMaslovData (n := 1) rfl σ).coframeGerms_of_retainedSectionMapExtensions hJI hJE hmap

/-- The full zero-ribbon realization retains its entire ribbon core,
actual grade and ambient/finite-ribbon marking recovery capabilities. -/
def prescribedZeroRealization :
    OriginalZeroRealization (prescribedZeroBundle PA PW PJ LA hPJ μ Z O σ hJI hJE hmap) :=
  (prescribedZeroBundle PA PW PJ LA hPJ μ Z O σ hJI hJE hmap).realize

end ZeroRibbon
end FsFltz.Geometry.IntrinsicSmoothBundle
