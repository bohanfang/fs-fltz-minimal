import FsFltz.Geometry.OriginalBundleJunctionGrading
import FsFltz.Geometry.OriginalBundleZeroCompletionJunction

/-!
# Original zero-ribbon homotopies on independently retained realizations

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–161;
`def:chain`, lines 171–199; `def:maslov`, lines 225–234; and
`sec:lean`, lines 788–814 and 825–830. The entire original finite ribbon
and its two map directions are retained. Original Maslov fields and full
canonical-square tensors recover the endpoint representatives through the
same completion comparisons that construct the geometric identification.

These are conditional foundational consumers. The original geometric maps,
regularity germs, markings and homotopy are supplied; their toric existence,
the finite comparison chain and its prescribed endpoint class remain pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle
namespace OriginalBundleAmbientJunction

section RetainedRealizations

variable {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace 2) A] [ChartedSpace (EuclideanHalfSpace 2) A']
  {EA EA' : Parameter → Type*} [∀ u, TopologicalSpace (EA u)] [∀ u, TopologicalSpace (EA' u)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ 2) (F := A) EA] [SmoothCompactBundle (𝓡∂ 2) (F := A') EA']
  {PA : BundlePrimitiveData (k := 1) (M := A) EA}
  {PA' : BundlePrimitiveData (k := 1) (M := A') EA'}
  {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
  {c : OriginalCompactChart (k := 1) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := 1) (M := A') (E := EA')}
  {t t' s s' : Parameter} {ht : t ∈ c.val.baseSet} {ht' : t' ∈ c'.val.baseSet}
  (O : OriginalBundleAmbientJunction LA LA'
    (LA.localCompletionFamily c t ht) (LA'.localCompletionFamily c' t' ht') s s' (n := 1) rfl rfl)
  (g : Trivialization A (π A EA)) (g' : Trivialization A' (π A' EA'))
  (hg : CompatibleTrivialization (𝓡∂ 2) EA g)
  (hg' : CompatibleTrivialization (𝓡∂ 2) EA' g')
  (hbase : g.baseSet = univ) (hbase' : g'.baseSet = univ)
  (hs : s ∈ (LA.localCompletionFamily c t ht).base)
  (hs' : s' ∈ (LA'.localCompletionFamily c' t' ht').base)
  (F G : PairDeformation 1)
  (eAs : ∀ u, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A (F.pair u).ambientDomain.domain.Point ∞)
  (eAs' : ∀ u, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A' (G.pair u).ambientDomain.domain.Point ∞)
  (hp : ∀ u x, ((F.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs u y).val) x) = PA.formInTrivialization g u x)
  (hp' : ∀ u x, ((G.pair u).ambientDomain.liouville.primitive (eAs' u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs' u y).val) x) = PA'.formInTrivialization g' u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := 1)
    (F.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val))
  (hc' : ∀ u, HasNativeCoordinateExtensions (k := 1)
    (G.pair u).ambientDomain.domain.extension (fun x => (eAs' u x).val))
  (R : OriginalBundleZeroRibbonJunction O)
  {EM EN : Parameter → Type*} [∀ u, TopologicalSpace (EM u)] [∀ u, TopologicalSpace (EN u)]
  [TopologicalSpace (TotalSpace R.M EM)] [TopologicalSpace (TotalSpace R.N EN)]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.M) EM]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.N) EN]
  (PJ : BundleRibbonData (a := 1) (M := R.M) (A := A) 𝓘(ℝ, Model 0) EM EA)
  (PJ' : BundleRibbonData (a := 1) (M := R.N) (A := A') 𝓘(ℝ, Model 0) EN EA')
  (cM : OriginalZeroCompactChart (M := R.M) (E := EM))
  (cN : OriginalZeroCompactChart (M := R.N) (E := EN))
  (hsM : s ∈ cM.val.baseSet) (hsN : s' ∈ cN.val.baseSet)
  (hjoriginal : PJ.map cM c s = R.j) (hj'original : PJ'.map cN c' s' = R.j')
  (gM : Trivialization R.M (π R.M EM)) (gN : Trivialization R.N (π R.N EN))
  (hbaseM : gM.baseSet = univ) (hbaseN : gN.baseSet = univ)
  (eMs : ∀ u, letI := (F.pair u).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.M (F.pair u).ribbonDomain.domain.Point ∞)
  (eNs : ∀ u, letI := (G.pair u).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.N (G.pair u).ribbonDomain.domain.Point ∞)
  (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv (F.pair s).ambientDomain.domain.boundary)
  (eB' : (IntrinsicBoundary.smoothManifold 1 A').SmoothEquiv (G.pair s').ambientDomain.domain.boundary)
  (hb : ∀ b, (F.pair s).ambientDomain.domain.boundaryInclusion.map (eB b) = (eAs s b.val).val)
  (hb' : ∀ b, (G.pair s').ambientDomain.domain.boundaryInclusion.map (eB' b) = (eAs' s' b.val).val)
  (hjGlobal : ∀ x, (F.pair s).ribbonEmbedding.map (eMs s x).val =
    eB (PJ.mapInTrivializations gM g hg s x))
  (hjGlobal' : ∀ x, (G.pair s').ribbonEmbedding.map (eNs s' x).val =
    eB' (PJ'.mapInTrivializations gN g' hg' s' x))
  (S : OriginalLocalCompletionMaslovData PA LA (n := 1) rfl)
  (S' : OriginalLocalCompletionMaslovData PA' LA' (n := 1) rfl)
  (f : MaslovFamily F.source.ambientManifold F.completedSymplecticExtension)
  (f' : MaslovFamily G.source.ambientManifold G.completedSymplecticExtension)
  (hfJ : ∀ u : Parameter, f.J u.val = S.descendedJ g hg hbase F eAs hp hc u)
  (hfT : ∀ u : Parameter, f.tensor u.val = S.descendedTensor g hg hbase F eAs hp hc u)
  (hfJ' : ∀ u : Parameter, f'.J u.val = S'.descendedJ g' hg' hbase' G eAs' hp' hc' u)
  (hfT' : ∀ u : Parameter, f'.tensor u.val = S'.descendedTensor g' hg' hbase' G eAs' hp' hc' u)
  (nativeSource : MaslovRepresentative (localMaslovAmbient rfl LA c t ht s).manifold
    ((localMaslovAmbient rfl LA c t ht s).manifold.exteriorDerivative
      (localMaslovAmbient rfl LA c t ht s).primitive))
  (nativeTarget : MaslovRepresentative (localMaslovAmbient rfl LA' c' t' ht' s').manifold
    ((localMaslovAmbient rfl LA' c' t' ht' s').manifold.exteriorDerivative
      (localMaslovAmbient rfl LA' c' t' ht' s').primitive))
  (hsourceJ : nativeSource.J = S.J c t ht s hs)
  (hsourceT : nativeSource.tensor = S.tensor c t ht s hs)
  (htargetJ : nativeTarget.J = S'.J c' t' ht' s' hs')
  (htargetT : nativeTarget.tensor = S'.tensor c' t' ht' s' hs')
  (H : MaslovHomotopy nativeSource (nativeTarget.pullbackTo O.Ψ O.strictSymplectic.symm))

/-- Original full-field recovery grades the exact zero-ribbon identification
on two independently retained realizations. The four represented endpoint
equations are derived, and a represented grading lift is never input. -/
def gradedZeroLiftOfLocalMaslovHomotopy_of_originalRibbonBundleData :
    let J := O.toNativeZeroCompletionJunction_of_originalRibbonBundleData
      g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
      eB eB' hb hb' PJ PJ' cM cN hsM hsN hjoriginal hj'original
      gM gN hbaseM hbaseN eMs eNs hjGlobal hjGlobal'
    GradedCompletionIdentification J.identification
      (F.maslovFamilyRepresentative f s) (G.maslovFamilyRepresentative f' s') := by
  let J := O.toNativeZeroCompletionJunction_of_originalRibbonBundleData
    g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
    eB eB' hb hb' PJ PJ' cM cN hsM hsN hjoriginal hj'original
    gM gN hbaseM hbaseN eMs eNs hjGlobal hjGlobal'
  have hsource := S.pullback_maslovFamilyRepresentative_descended
    g hg hbase F eAs hp hc f hfJ hfT c t ht s hs
  have htarget := S'.pullback_maslovFamilyRepresentative_descended
    g' hg' hbase' G eAs' hp' hc' f' hfJ' hfT' c' t' ht' s' hs'
  refine J.gradedLiftOfOriginalHomotopy nativeSource nativeTarget H
    (F.maslovFamilyRepresentative f s) (G.maslovFamilyRepresentative f' s') ?_ ?_ ?_ ?_
  · intro x v
    rw [hsourceJ, ← hsource.1]
    exact pullbackAlmostComplex_intertwines _ _ _ _ x v
  · intro x vs
    rw [hsourceT, ← hsource.2]
    rfl
  · intro x v
    rw [htargetJ, ← htarget.1]
    exact pullbackAlmostComplex_intertwines _ _ _ _ x v
  · intro x vs
    rw [htargetT, ← htarget.2]
    rfl

/-- Every real parameter retains the original homotopy's complex field
under the inverse of the exact source completion comparison. -/
theorem gradedZeroLiftOfLocalMaslovHomotopy_family_J (τ : ℝ) :
    let lift := O.gradedZeroLiftOfLocalMaslovHomotopy_of_originalRibbonBundleData
      g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
      PJ PJ' cM cN hsM hsN hjoriginal hj'original gM gN hbaseM hbaseN
      eMs eNs eB eB' hb hb' hjGlobal hjGlobal' S S' f f' hfJ hfT hfJ' hfT'
      nativeSource nativeTarget hsourceJ hsourceT htargetJ htargetT H
    let q := CompletedMaslovDimension.comparison rfl
      ((LA.localCompletionFamily c t ht).sliceCompletion LA s).ambient
      (F.pair s).ambientManifold
      ((LA.localCompletionFamily c t ht).ambientEndpointSliceComparison
        LA g hg hbase s hs F rfl eAs hp hc).equiv
    lift.family.J τ = pullbackAlmostComplex (F.pair s).ambientManifold
      (localMaslovAmbient rfl LA c t ht s).manifold q.symm (H.family.J τ) := rfl

/-- The same exact inverse comparison retains every slot of both tensor
blocks of the original homotopy at every real parameter. -/
theorem gradedZeroLiftOfLocalMaslovHomotopy_family_tensor (τ : ℝ) :
    let lift := O.gradedZeroLiftOfLocalMaslovHomotopy_of_originalRibbonBundleData
      g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
      PJ PJ' cM cN hsM hsN hjoriginal hj'original gM gN hbaseM hbaseN
      eMs eNs eB eB' hb hb' hjGlobal hjGlobal' S S' f f' hfJ hfT hfJ' hfT'
      nativeSource nativeTarget hsourceJ hsourceT htargetJ htargetT H
    let q := CompletedMaslovDimension.comparison rfl
      ((LA.localCompletionFamily c t ht).sliceCompletion LA s).ambient
      (F.pair s).ambientManifold
      ((LA.localCompletionFamily c t ht).ambientEndpointSliceComparison
        LA g hg hbase s hs F rfl eAs hp hc).equiv
    lift.family.tensor τ = pullbackSquaredTensor (F.pair s).ambientManifold
      (localMaslovAmbient rfl LA c t ht s).manifold q.symm (H.family.tensor τ) := rfl

end RetainedRealizations

section OriginalRealizations

variable {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace 2) A] [ChartedSpace (EuclideanHalfSpace 2) A']
  {EA EA' : Parameter → Type*} [∀ u, TopologicalSpace (EA u)] [∀ u, TopologicalSpace (EA' u)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ 2) (F := A) EA] [SmoothCompactBundle (𝓡∂ 2) (F := A') EA']
  {PA : BundlePrimitiveData (k := 1) (M := A) EA}
  {PA' : BundlePrimitiveData (k := 1) (M := A') EA'}
  {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
  {c : OriginalCompactChart (k := 1) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := 1) (M := A') (E := EA')}
  {t t' : Parameter} {ht : t ∈ c.val.baseSet} {ht' : t' ∈ c'.val.baseSet}

/-- Two original bundle datasets produce independently selected graded
realizations and a graded identification on their literal retained endpoints.
Every original constructor conclusion is retained, including both entire
finite ribbons, the realization coherence, and independently supplied ambient
and ribbon markings in all original charts. Only an original homotopy is input.
-/
theorem exists_gradedJunction_of_originalZeroBundleData
    (O : OriginalBundleAmbientJunction LA LA'
      (LA.localCompletionFamily c t ht) (LA'.localCompletionFamily c' t' ht') parameterOne parameterZero (n := 1) rfl rfl)
    (hs : parameterOne ∈ (LA.localCompletionFamily c t ht).base)
    (hs' : parameterZero ∈ (LA'.localCompletionFamily c' t' ht').base)
    (R : OriginalBundleZeroRibbonJunction O)
    {EM EN : Parameter → Type*} [∀ u, TopologicalSpace (EM u)] [∀ u, TopologicalSpace (EN u)]
    [TopologicalSpace (TotalSpace R.M EM)] [TopologicalSpace (TotalSpace R.N EN)]
    [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.M) EM]
    [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.N) EN]
    (PJ : BundleRibbonData (a := 1) (M := R.M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (PJ' : BundleRibbonData (a := 1) (M := R.N) (A := A') 𝓘(ℝ, Model 0) EN EA')
    (hPJ : ∀ cM cA u, u ∈ cM.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ.map cM cA u))
    (hPJ' : ∀ cN cA u, u ∈ cN.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ'.map cN cA u))
    (PW : BundleWitnessData (k := 1) (M := A) EA)
    (PW' : BundleWitnessData (k := 1) (M := A') EA')
    (μ : Parameter → (sourceManifold R.M).Form 1)
    (μ' : Parameter → (sourceManifold R.N).Form 1)
    (S : OriginalLocalCompletionMaslovData PA LA (n := 1) rfl)
    (S' : OriginalLocalCompletionMaslovData PA' LA' (n := 1) rfl)
    (hS : OriginalLocalCompletionMaslovCoframeGerms S)
    (hS' : OriginalLocalCompletionMaslovCoframeGerms S')
    (cM : OriginalZeroCompactChart (M := R.M) (E := EM))
    (cN : OriginalZeroCompactChart (M := R.N) (E := EN))
    (hsM : parameterOne ∈ cM.val.baseSet) (hsN : parameterZero ∈ cN.val.baseSet)
    (hjoriginal : PJ.map cM c parameterOne = R.j) (hj'original : PJ'.map cN c' parameterZero = R.j')
    (nativeSource : MaslovRepresentative (localMaslovAmbient rfl LA c t ht parameterOne).manifold
      ((localMaslovAmbient rfl LA c t ht parameterOne).manifold.exteriorDerivative
        (localMaslovAmbient rfl LA c t ht parameterOne).primitive))
    (nativeTarget : MaslovRepresentative (localMaslovAmbient rfl LA' c' t' ht' parameterZero).manifold
      ((localMaslovAmbient rfl LA' c' t' ht' parameterZero).manifold.exteriorDerivative
        (localMaslovAmbient rfl LA' c' t' ht' parameterZero).primitive))
    (hsourceJ : nativeSource.J = S.J c t ht parameterOne hs)
    (hsourceT : nativeSource.tensor = S.tensor c t ht parameterOne hs)
    (htargetJ : nativeTarget.J = S'.J c' t' ht' parameterZero hs')
    (htargetT : nativeTarget.tensor = S'.tensor c' t' ht' parameterZero hs')
    (H : MaslovHomotopy nativeSource (nativeTarget.pullbackTo O.Ψ O.strictSymplectic.symm)) :
    ∃ gM : Trivialization R.M (π R.M EM),
    ∃ g : Trivialization A (π A EA), ∃ (hbaseM : gM.baseSet = univ) (hbase : g.baseSet = univ),
    ∃ _hgM : CompatibleTrivialization 𝓘(ℝ, Model 0) EM gM,
    ∃ hg : CompatibleTrivialization (𝓡∂ 2) EA g,
    let αF := PA.formInTrivialization g;
    let jF := PJ.mapInTrivializations gM g hg;
    let bF := PW.witnessInTrivialization g hg;
    (∀ c hc t, t ∈ c.baseSet →
      αF t = nativePullbackForm (g.coordChange c t) (PA.form ⟨c, hc⟩ t)) ∧
    (∀ (cM : Trivialization R.M (π R.M EM)) hcM (cA : Trivialization A (π A EA)) hcA t,
      t ∈ cM.baseSet ∩ cA.baseSet → ∀ x,
      (jF t x).val = cA.coordChange g t
        (PJ.map ⟨cM, hcM⟩ ⟨cA, hcA⟩ t (gM.coordChange cM t x)).val) ∧
    (∀ c hc t, t ∈ c.baseSet → ∀ x,
      bF t x = PW.witness ⟨c, hc⟩ t
        (boundaryFamilyOn (g.baseSet ∩ c.baseSet) (g.coordChange c)
          (compatibleTransition_boundary g c hg (compatibleTrivialization_of_mem hc)) t x)) ∧
    ∃ F : PairDeformation 1,
    ∃ eAs : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A
      (F.pair t).ambientDomain.domain.Point ∞,
    ∃ eMs : ∀ t, letI := (F.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.M (F.pair t).ribbonDomain.domain.Point ∞,
    ∃ eBs : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
      (F.pair t).ambientDomain.domain.boundary,
    ∃ (RA : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A A ∞)
      (RM : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.M R.M ∞),
      IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) RA ∧
      IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RM ∧
      (∀ t x, (F.ambientPresentation t).extensionEquiv
        ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
      (∀ t x, (F.ribbonPresentation t).extensionEquiv
        ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val) ∧
      (∀ t x, (F.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
      (∀ t,
      let P := F.pair t;
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eMs t x).val = eBs t (jF t x)) ∧
        (∀ x, P.witness (eBs t x) = bF t x) ∧
        P.embeddedCore = (eBs t) '' range (jF t) ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = αF t x) ∧
        (sourceManifold R.M).pullback P.ribbonDomain.domain.extension
          (fun x => (eMs t x).val) P.ribbonDomain.liouville.primitive = μ t ∧
        (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (αF t) ∧
        HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val)) ∧
      ∃ (hp : ∀ s x, ((F.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (2)) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization g s x)
        (hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
          (F.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∃ f : MaslovFamily F.source.ambientManifold F.completedSymplecticExtension,
        (∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase F eAs hp hc s) ∧
        (∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase F eAs hp hc s) ∧
        (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
            F.source.ambientManifold (localMaslovComparison g hg hbase F eAs hp hc c t ht s hs)
            (f.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
            F.source.ambientManifold (localMaslovComparison g hg hbase F eAs hp hc c t ht s hs)
            (f.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpointsF := F.maslovFamilyRepresentative f
        let gradeF := F.gradedOfMaslovFamily f
        gradeF.etaExtension = F.completedSymplecticExtension ∧ gradeF.family = f ∧
        ∃ actualGradeF : GradedPairDeformation F (endpointsF parameterZero) (endpointsF parameterOne),
          actualGradeF = gradeF ∧
          (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
              (F.pair s).ambientManifold
              ((localMaslovComparison g hg hbase F eAs hp hc c t ht s hs).trans
                (F.ambientCompletionPresentation s).equiv) (endpointsF s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
              (F.pair s).ambientManifold
              ((localMaslovComparison g hg hbase F eAs hp hc c t ht s hs).trans
                (F.ambientCompletionPresentation s).equiv) (endpointsF s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold 2)
            (AMark : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (F.pair s).ambientCompletion (W s)
              (fun y => chartValue g (AMark.compact s) s ((eAs s).symm y)),
            markings = (fun s => AMark.ambientMarkingAt g hg hbase F rfl eAs hp hc s) ∧
            (∀ s x, (markings s).equiv
              ((F.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
                chartValue g (AMark.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
              (t : Parameter) (Umark : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ Umark.base),
              (Umark.ambientEndpointSliceComparison LA g hg hbase s hs F rfl eAs hp hc).equiv.trans
                (markings s).equiv = AMark.localEquiv Umark s hs) ∧
          (∀ (HMark : Parameter → CompleteLiouvilleManifold 0)
            (RMark : OriginalZeroBundleCompletionMarkingData (M := R.M) (E := EM) HMark),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (F.pair s).ribbonCompletion (HMark s)
              (fun y => chartValue gM (RMark.compact s) s ((eMs s).symm y)),
            ribbonMarkings = (fun s => RMark.ribbonMarkingAt gM hbaseM F eMs s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((F.pair s).ribbonCompletion.inclusion.map (eMs s x).val) =
                chartValue gM (RMark.compact s) s x) ∧
            ∀ (c : OriginalZeroCompactChart (M := R.M) (E := EM))
              (s : Parameter) (hs : s ∈ c.val.baseSet),
              (zeroRibbonEndpointEquiv gM hbaseM F eMs c s hs).trans
                (ribbonMarkings s).equiv = RMark.chart c s hs) ∧
    ∃ gN : Trivialization R.N (π R.N EN),
    ∃ g' : Trivialization A' (π A' EA'), ∃ (hbaseN : gN.baseSet = univ) (hbase' : g'.baseSet = univ),
    ∃ _hgN : CompatibleTrivialization 𝓘(ℝ, Model 0) EN gN,
    ∃ hg' : CompatibleTrivialization (𝓡∂ 2) EA' g',
    let αG := PA'.formInTrivialization g';
    let jG := PJ'.mapInTrivializations gN g' hg';
    let bG := PW'.witnessInTrivialization g' hg';
    (∀ c hc' t, t ∈ c.baseSet →
      αG t = nativePullbackForm (g'.coordChange c t) (PA'.form ⟨c, hc'⟩ t)) ∧
    (∀ (cM : Trivialization R.N (π R.N EN)) hcM (cA : Trivialization A' (π A' EA')) hcA t,
      t ∈ cM.baseSet ∩ cA.baseSet → ∀ x,
      (jG t x).val = cA.coordChange g' t
        (PJ'.map ⟨cM, hcM⟩ ⟨cA, hcA⟩ t (gN.coordChange cM t x)).val) ∧
    (∀ c hc' t, t ∈ c.baseSet → ∀ x,
      bG t x = PW'.witness ⟨c, hc'⟩ t
        (boundaryFamilyOn (g'.baseSet ∩ c.baseSet) (g'.coordChange c)
          (compatibleTransition_boundary g' c hg' (compatibleTrivialization_of_mem hc')) t x)) ∧
    ∃ G : PairDeformation 1,
    ∃ eAs' : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A'
      (G.pair t).ambientDomain.domain.Point ∞,
    ∃ eNs : ∀ t, letI := (G.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.N (G.pair t).ribbonDomain.domain.Point ∞,
    ∃ eBs' : ∀ t, (IntrinsicBoundary.smoothManifold 1 A').SmoothEquiv
      (G.pair t).ambientDomain.domain.boundary,
    ∃ (RA' : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A' A' ∞)
      (RN : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.N R.N ∞),
      IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) RA' ∧
      IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RN ∧
      (∀ t x, (G.ambientPresentation t).extensionEquiv
        ((eAs' parameterZero (RA' t.val x)).val) = (eAs' t x).val) ∧
      (∀ t x, (G.ribbonPresentation t).extensionEquiv
        ((eNs parameterZero (RN t.val x)).val) = (eNs t x).val) ∧
      (∀ t x, (G.ambientPresentation t).boundaryEquiv (eBs' parameterZero x) = eBs' t x) ∧
      (∀ t,
      let P := G.pair t;
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs' t x) = (eAs' t x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eNs t x).val = eBs' t (jG t x)) ∧
        (∀ x, P.witness (eBs' t x) = bG t x) ∧
        P.embeddedCore = (eBs' t) '' range (jG t) ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eAs' t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs' t y).val) x) = αG t x) ∧
        (sourceManifold R.N).pullback P.ribbonDomain.domain.extension
          (fun x => (eNs t x).val) P.ribbonDomain.liouville.primitive = μ' t ∧
        (IntrinsicBoundary.smoothManifold 1 A').pullback P.ambientDomain.domain.boundary (eBs' t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (αG t) ∧
        HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs' t x).val)) ∧
      ∃ (hp' : ∀ s x, ((G.pair s).ambientDomain.liouville.primitive (eAs' s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (2)) 𝓘(ℝ, Model 2) (fun y => (eAs' s y).val) x) =
          PA'.formInTrivialization g' s x)
        (hc' : ∀ s, HasNativeCoordinateExtensions (k := 1)
          (G.pair s).ambientDomain.domain.extension (fun x => (eAs' s x).val)),
      ∃ f' : MaslovFamily G.source.ambientManifold G.completedSymplecticExtension,
        (∀ s : Parameter, f'.J s.val = S'.descendedJ g' hg' hbase' G eAs' hp' hc' s) ∧
        (∀ s : Parameter, f'.tensor s.val = S'.descendedTensor g' hg' hbase' G eAs' hp' hc' s) ∧
        (∀ (c : OriginalCompactChart (k := 1) (M := A') (E := EA'))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA'.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient rfl LA' c t ht s).manifold
            G.source.ambientManifold (localMaslovComparison g' hg' hbase' G eAs' hp' hc' c t ht s hs)
            (f'.J s.val) = S'.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient rfl LA' c t ht s).manifold
            G.source.ambientManifold (localMaslovComparison g' hg' hbase' G eAs' hp' hc' c t ht s hs)
            (f'.tensor s.val) = S'.tensor c t ht s hs) ∧
        let endpointsG := G.maslovFamilyRepresentative f'
        let gradeG := G.gradedOfMaslovFamily f'
        gradeG.etaExtension = G.completedSymplecticExtension ∧ gradeG.family = f' ∧
        ∃ actualGradeG : GradedPairDeformation G (endpointsG parameterZero) (endpointsG parameterOne),
          actualGradeG = gradeG ∧
          (∀ (c : OriginalCompactChart (k := 1) (M := A') (E := EA'))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA'.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient rfl LA' c t ht s).manifold
              (G.pair s).ambientManifold
              ((localMaslovComparison g' hg' hbase' G eAs' hp' hc' c t ht s hs).trans
                (G.ambientCompletionPresentation s).equiv) (endpointsG s).J = S'.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient rfl LA' c t ht s).manifold
              (G.pair s).ambientManifold
              ((localMaslovComparison g' hg' hbase' G eAs' hp' hc' c t ht s hs).trans
                (G.ambientCompletionPresentation s).equiv) (endpointsG s).tensor =
                  S'.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold 2)
            (AMark : OriginalBundleCompletionMarkingData LA' W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (G.pair s).ambientCompletion (W s)
              (fun y => chartValue g' (AMark.compact s) s ((eAs' s).symm y)),
            markings = (fun s => AMark.ambientMarkingAt g' hg' hbase' G rfl eAs' hp' hc' s) ∧
            (∀ s x, (markings s).equiv
              ((G.pair s).ambientCompletion.inclusion.map (eAs' s x).val) =
                chartValue g' (AMark.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := 1) (M := A') (E := EA'))
              (t : Parameter) (Vmark : LocalCompletionFamily PA' c t)
              (s : Parameter) (hs : s ∈ Vmark.base),
              (Vmark.ambientEndpointSliceComparison LA' g' hg' hbase' s hs G rfl eAs' hp' hc').equiv.trans
                (markings s).equiv = AMark.localEquiv Vmark s hs) ∧
          (∀ (HMark : Parameter → CompleteLiouvilleManifold 0)
            (RMark : OriginalZeroBundleCompletionMarkingData (M := R.N) (E := EN) HMark),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (G.pair s).ribbonCompletion (HMark s)
              (fun y => chartValue gN (RMark.compact s) s ((eNs s).symm y)),
            ribbonMarkings = (fun s => RMark.ribbonMarkingAt gN hbaseN G eNs s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((G.pair s).ribbonCompletion.inclusion.map (eNs s x).val) =
                chartValue gN (RMark.compact s) s x) ∧
            ∀ (c : OriginalZeroCompactChart (M := R.N) (E := EN))
              (s : Parameter) (hs : s ∈ c.val.baseSet),
              (zeroRibbonEndpointEquiv gN hbaseN G eNs c s hs).trans
                (ribbonMarkings s).equiv = RMark.chart c s hs) ∧
    ∃ (hb : ∀ u b, (F.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
        (eAs u b.val).val)
      (hb' : ∀ u b, (G.pair u).ambientDomain.domain.boundaryInclusion.map (eBs' u b) =
        (eAs' u b.val).val)
      (hjGlobal : ∀ u x, (F.pair u).ribbonEmbedding.map (eMs u x).val =
        eBs u (PJ.mapInTrivializations gM g hg u x))
      (hjGlobal' : ∀ u x, (G.pair u).ribbonEmbedding.map (eNs u x).val =
        eBs' u (PJ'.mapInTrivializations gN g' hg' u x)),
    let J := O.toNativeZeroCompletionJunction_of_originalRibbonBundleData
      g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
      (eBs parameterOne) (eBs' parameterZero) (hb parameterOne) (hb' parameterZero) PJ PJ' cM cN hsM hsN hjoriginal hj'original
      gM gN hbaseM hbaseN eMs eNs (hjGlobal parameterOne) (hjGlobal' parameterZero)
    ∃ lift : GradedCompletionIdentification J.identification
      (F.maslovFamilyRepresentative f parameterOne) (G.maslovFamilyRepresentative f' parameterZero),
      (∀ τ : ℝ, lift.family.J τ = pullbackAlmostComplex (F.pair parameterOne).ambientManifold
        J.ambient.X J.ambient.S.symm (H.family.J τ)) ∧
      (∀ τ : ℝ, lift.family.tensor τ = pullbackSquaredTensor (F.pair parameterOne).ambientManifold
        J.ambient.X J.ambient.S.symm (H.family.tensor τ)) ∧
      J.identification.ambientEquiv = (J.ambient.S.symm.trans O.Ψ).trans J.ambient.S' ∧
      J.identification.boundaryEquiv = (J.ambient.bS.symm.trans O.ψ).trans J.ambient.bS' ∧
      J.identification.shift = O.shift ∘ J.ambient.bS.symm ∧
      let path := ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
        (ComparisonStep.identification J.identification)).cons (ComparisonStep.deformation G)
      ∃ grading : GradedComparisonChain F.source path
        (endpointsF parameterZero) (endpointsG parameterOne),
        grading = (by
          dsimp only [path]
          exact (((GradedComparisonChain.nil (endpointsF parameterZero)).cons
            (.deformation actualGradeF)).cons (.identification lift)).cons (.deformation actualGradeG)) ∧
        path.length = 3 ∧ path.vertices = [F.source, F.target, G.source, G.target] := by
  obtain ⟨gM, g, hbaseM, hbase, hgM, hg, hcov, hj, hw,
    F, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint,
    hp, hc, f, hfJ, hfT, hrecover, heta, hfamily, actualGradeF, hactual,
    hrecoverEndpoint, hmarkings, hribbonMarkings⟩ :=
      exists_zero_pairDeformation_with_originalMaslovFamily PA LA PJ hPJ PW μ S hS
  obtain ⟨gN, g', hbaseN, hbase', hgN, hg', hcov', hj', hw',
    G, eAs', eNs, eBs', RA', RN, hRA', hRN, hsquare', hsquareN, hsquareB', hpoint',
    hp', hc', f', hfJ', hfT', hrecover', heta', hfamily', actualGradeG, hactual',
    hrecoverEndpoint', hmarkings', hribbonMarkings'⟩ :=
      exists_zero_pairDeformation_with_originalMaslovFamily PA' LA' PJ' hPJ' PW' μ' S' hS'
  refine ⟨gM, g, hbaseM, hbase, hgM, hg, hcov, hj, hw,
    F, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint,
    hp, hc, f, hfJ, hfT, hrecover, heta, hfamily, actualGradeF, hactual,
    hrecoverEndpoint, hmarkings, hribbonMarkings,
    gN, g', hbaseN, hbase', hgN, hg', hcov', hj', hw',
    G, eAs', eNs, eBs', RA', RN, hRA', hRN, hsquare', hsquareN, hsquareB', hpoint',
    hp', hc', f', hfJ', hfT', hrecover', heta', hfamily', actualGradeG, hactual',
    hrecoverEndpoint', hmarkings', hribbonMarkings', ?_⟩
  have hb : ∀ u b, (F.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val := fun u => (hpoint u).1
  have hb' : ∀ u b, (G.pair u).ambientDomain.domain.boundaryInclusion.map (eBs' u b) =
      (eAs' u b.val).val := fun u => (hpoint' u).1
  have hjGlobal : ∀ u x, (F.pair u).ribbonEmbedding.map (eMs u x).val =
      eBs u (PJ.mapInTrivializations gM g hg u x) := fun u => (hpoint u).2.1
  have hjGlobal' : ∀ u x, (G.pair u).ribbonEmbedding.map (eNs u x).val =
      eBs' u (PJ'.mapInTrivializations gN g' hg' u x) := fun u => (hpoint' u).2.1
  let J := O.toNativeZeroCompletionJunction_of_originalRibbonBundleData
    g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
    (eBs parameterOne) (eBs' parameterZero) (hb parameterOne) (hb' parameterZero)
    PJ PJ' cM cN hsM hsN hjoriginal hj'original gM gN hbaseM hbaseN eMs eNs
    (hjGlobal parameterOne) (hjGlobal' parameterZero)
  let lift := O.gradedZeroLiftOfLocalMaslovHomotopy_of_originalRibbonBundleData
    g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc' R
    PJ PJ' cM cN hsM hsN hjoriginal hj'original gM gN hbaseM hbaseN eMs eNs
    (eBs parameterOne) (eBs' parameterZero) (hb parameterOne) (hb' parameterZero) (hjGlobal parameterOne) (hjGlobal' parameterZero)
    S S' f f' hfJ hfT hfJ' hfT' nativeSource nativeTarget hsourceJ hsourceT htargetJ htargetT H
  refine ⟨hb, hb', hjGlobal, hjGlobal', lift, fun _ => rfl, fun _ => rfl,
    J.identification_ambientEquiv, J.identification_boundaryEquiv, J.identification_shift, ?_⟩
  exact ⟨(((GradedComparisonChain.nil (F.maslovFamilyRepresentative f parameterZero)).cons
    (.deformation actualGradeF)).cons (.identification lift)).cons (.deformation actualGradeG),
    rfl, rfl, rfl⟩

end OriginalRealizations
end OriginalBundleAmbientJunction
end FsFltz.Geometry.IntrinsicSmoothBundle
