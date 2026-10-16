import FsFltz.Geometry.OriginalBundleJunctionGrading

/-!
# Two original pair bundles with their exact graded junction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199;
`def:maslov`, lines 212–234; `g:chain`, lines 398–413; and
`sec:lean`, lines 788–814. Choose the two geometric realizations once,
retaining the full covariance, compact geometry, coherent presentations,
original Maslov recovery and independent ambient/ribbon marking outputs
of both original-bundle constructors. The independently supplied original
junction homotopy grades the exact identification between their endpoints.
Its pullback formulas hold at all real homotopy parameters.

This is a conditional foundational consumer. It constructs neither the
original strict maps nor their smooth homotopy, the toric finite chain,
the prescribed endpoint class, or the source-smooth-section correspondence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {a a' n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A A' : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace A'] [T2Space A'] [SecondCountableTopology A'] [CompactSpace A']
  [ChartedSpace (EuclideanHalfSpace (a' + 1)) A'] [IsManifold (𝓡∂ (a' + 1)) ∞ A']
  {EA EA' : Parameter → Type*} [∀ u, TopologicalSpace (EA u)] [∀ u, TopologicalSpace (EA' u)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  [SmoothCompactBundle (𝓡∂ (a' + 1)) (F := A') EA']

/-- Realize two independent original pair bundles exactly once, preserve
all outputs of both original marked Maslov-family constructors, and grade
their actual junction by the original smooth homotopy. The source-only
input contains no represented endpoint or grading lift. -/
theorem exists_gradedJunction_of_originalPositiveBundleData
    (hA : a + 1 = 2 * n) (hA' : a' + 1 = 2 * n)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PA' : BundlePrimitiveData (k := a') (M := A') EA')
    (LA : OriginalBundleLiouvilleLaws PA) (LA' : OriginalBundleLiouvilleLaws PA')
    (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (c' : OriginalCompactChart (k := a') (M := A') (E := EA'))
    (t t' : Parameter) (ht : t ∈ c.val.baseSet) (ht' : t' ∈ c'.val.baseSet)
    (hs : parameterOne ∈ (LA.localCompletionFamily c t ht).base)
    (hs' : parameterZero ∈ (LA'.localCompletionFamily c' t' ht').base)
    (O : OriginalBundleAmbientJunction LA LA'
      (LA.localCompletionFamily c t ht) (LA'.localCompletionFamily c' t' ht')
      parameterOne parameterZero hA hA')
    (R : OriginalBundlePositiveRibbonJunction O)
    [T2Space R.M] [SecondCountableTopology R.M]
    [T2Space R.N] [SecondCountableTopology R.N] [CompactSpace R.N]
    {EM EN : Parameter → Type*}
    [∀ u, TopologicalSpace (EM u)] [∀ u, TopologicalSpace (EN u)]
    [TopologicalSpace (TotalSpace R.M EM)] [TopologicalSpace (TotalSpace R.N EN)]
    [SmoothCompactBundle (𝓡∂ (R.k + 1)) (F := R.M) EM]
    [SmoothCompactBundle (𝓡∂ (R.k + 1)) (F := R.N) EN]
    (PM : BundlePrimitiveData (k := R.k) (M := R.M) EM)
    (PN : BundlePrimitiveData (k := R.k) (M := R.N) EN)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PW' : BundleWitnessData (k := a') (M := A') EA')
    (PJ : BundleRibbonData (a := a) (M := R.M) (A := A) (𝓡∂ (R.k + 1)) EM EA)
    (PJ' : BundleRibbonData (a := a') (M := R.N) (A := A') (𝓡∂ (R.k + 1)) EN EA')
    (LM : OriginalBundleLiouvilleLaws PM) (LN : OriginalBundleLiouvilleLaws PN)
    (LP : OriginalBundlePairLaws PA PM PW PJ) (LP' : OriginalBundlePairLaws PA' PN PW' PJ')
    (S : OriginalLocalCompletionMaslovData PA LA hA)
    (S' : OriginalLocalCompletionMaslovData PA' LA' hA')
    (hS : OriginalLocalCompletionMaslovCoframeGerms S)
    (hS' : OriginalLocalCompletionMaslovCoframeGerms S')
    (cM : OriginalCompactChart (k := R.k) (M := R.M) (E := EM))
    (cN : OriginalCompactChart (k := R.k) (M := R.N) (E := EN))
    (tM tN : Parameter) (htM : tM ∈ cM.val.baseSet) (htN : tN ∈ cN.val.baseSet)
    (hsM : parameterOne ∈ (LM.localCompletionFamily cM tM htM).base)
    (hsN : parameterZero ∈ (LN.localCompletionFamily cN tN htN).base)
    (hμ : PM.form cM parameterOne = R.μ) (hν : PN.form cN parameterZero = R.ν)
    (hj : PJ.map cM c parameterOne = R.j) (hj' : PJ'.map cN c' parameterZero = R.j')
    (nativeSource : MaslovRepresentative (localMaslovAmbient hA LA c t ht parameterOne).manifold
      ((localMaslovAmbient hA LA c t ht parameterOne).manifold.exteriorDerivative
        (localMaslovAmbient hA LA c t ht parameterOne).primitive))
    (nativeTarget : MaslovRepresentative (localMaslovAmbient hA' LA' c' t' ht' parameterZero).manifold
      ((localMaslovAmbient hA' LA' c' t' ht' parameterZero).manifold.exteriorDerivative
        (localMaslovAmbient hA' LA' c' t' ht' parameterZero).primitive))
    (H : MaslovHomotopy nativeSource (nativeTarget.pullbackTo O.Ψ O.strictSymplectic.symm))
    (hSourceJ : nativeSource.J = S.J c t ht parameterOne hs)
    (hSourceT : nativeSource.tensor = S.tensor c t ht parameterOne hs)
    (hTargetJ : nativeTarget.J = S'.J c' t' ht' parameterZero hs')
    (hTargetT : nativeTarget.tensor = S'.tensor c' t' ht' parameterZero hs') :
    ∃ (cAF : Trivialization A (π A EA)) (cMF : Trivialization R.M (π R.M EM)),
      ∃ (hbaseAF : cAF.baseSet = univ) (hbaseMF : cMF.baseSet = univ),
      ∃ (heAF : CompatibleTrivialization (𝓡∂ (a + 1)) EA cAF)
        (heMF : CompatibleTrivialization (𝓡∂ (R.k + 1)) EM cMF),
      let lamF := PA.formInTrivialization cAF
      let μF := PM.formInTrivialization cMF
      let jF := PJ.mapInTrivializations cMF cAF heAF
      let bF := PW.witnessInTrivialization cAF heAF
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x vs,
        lamF t x vs = PA.form ⟨dA, hdA⟩ t (cAF.coordChange dA t x)
          (fun i => mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) (cAF.coordChange dA t) x (vs i))) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas R.M EM) t, t ∈ dM.baseSet → ∀ x vs,
        μF t x vs = PM.form ⟨dM, hdM⟩ t (cMF.coordChange dM t x)
          (fun i => mfderiv (𝓡∂ (R.k + 1)) (𝓡∂ (R.k + 1)) (cMF.coordChange dM t) x (vs i))) ∧
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x,
        bF t x = PW.witness ⟨dA, hdA⟩ t
          (boundaryFamilyOn (cAF.baseSet ∩ dA.baseSet) (cAF.coordChange dA)
            (compatibleTransition_boundary cAF dA heAF (compatibleTrivialization_of_mem hdA)) t x)) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas R.M EM) dA (hdA : dA ∈ trivializationAtlas A EA) t,
        t ∈ dM.baseSet ∩ dA.baseSet → ∀ x,
        (jF t x).val = dA.coordChange cAF t (PJ.map ⟨dM, hdM⟩ ⟨dA, hdA⟩ t
          (cMF.coordChange dM t x)).val) ∧
      ∃ F : PairDeformation n,
      ∃ (eAsF : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
          (F.pair t).ambientDomain.domain.Point ∞)
        (eMsF : ∀ t, Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.M
          (F.pair t).ribbonDomain.domain.Point ∞)
        (eBsF : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
          (F.pair t).ambientDomain.domain.boundary),
      ∃ (RAF : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A ∞)
        (RMF : ℝ → Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (R.k + 1)) R.M R.M ∞),
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) RAF ∧
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (R.k + 1)) RMF ∧
        (∀ t x, (F.ambientPresentation t).extensionEquiv
          ((eAsF parameterZero (RAF t.val x)).val) = (eAsF t x).val) ∧
        (∀ t x, (F.ribbonPresentation t).extensionEquiv
          ((eMsF parameterZero (RMF t.val x)).val) = (eMsF t x).val) ∧
        (∀ t x, (F.ambientPresentation t).boundaryEquiv (eBsF parameterZero x) = eBsF t x) ∧
        (∀ t : Parameter,
        let P := F.pair t
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBsF t) x) = ((eAsF t) x.val).val) ∧
        (∀ x, (P.ambientDomain.liouville.primitive ((eAsF t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAsF t) y).val) x) = lamF t x) ∧
        (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary (eBsF t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (lamF t) ∧
        (∀ x, P.ribbonEmbedding.map ((eMsF t) x).val = (eBsF t) (jF t x)) ∧
        (∀ x, P.witness ((eBsF t) x) = bF t x) ∧
        (∀ x, (P.ribbonDomain.liouville.primitive ((eMsF t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMsF t) y).val) x) = μF t x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBsF t) '' range (jF t) ∧
        P.embeddedCore = (fun x => (eBsF t) (jF t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
          P.ribbonCompletion.ambient.completeFlow.flow s
            (P.ribbonCompletion.inclusion.map ((eMsF t) x).val) ∈
              range (fun y => P.ribbonCompletion.inclusion.map ((eMsF t) y).val)} ∧
        HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eAsF t) x).val) ∧
        HasNativeCoordinateExtensions (k := R.k) P.ribbonDomain.domain.extension (fun x => ((eMsF t) x).val)) ∧
      ∃ (hpF : ∀ s x, ((F.pair s).ambientDomain.liouville.primitive (eAsF s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAsF s y).val) x) =
          PA.formInTrivialization cAF s x)
        (hcF : ∀ s, HasNativeCoordinateExtensions (k := a)
          (F.pair s).ambientDomain.domain.extension (fun x => (eAsF s x).val)),
      ∃ fF : MaslovFamily F.source.ambientManifold F.completedSymplecticExtension,
        (∀ s : Parameter, fF.J s.val = S.descendedJ cAF heAF hbaseAF F eAsF hpF hcF s) ∧
        (∀ s : Parameter, fF.tensor s.val = S.descendedTensor cAF heAF hbaseAF F eAsF hpF hcF s) ∧
        (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient hA LA c t ht s).manifold
            F.source.ambientManifold (localMaslovComparison cAF heAF hbaseAF F eAsF hpF hcF c t ht s hs)
            (fF.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient hA LA c t ht s).manifold
            F.source.ambientManifold (localMaslovComparison cAF heAF hbaseAF F eAsF hpF hcF c t ht s hs)
            (fF.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpointsF := F.maslovFamilyRepresentative fF
        let gradeF := F.gradedOfMaslovFamily fF
        gradeF.etaExtension = F.completedSymplecticExtension ∧ gradeF.family = fF ∧
        ∃ actualGradeF : GradedPairDeformation F (endpointsF parameterZero) (endpointsF parameterOne),
          actualGradeF = gradeF ∧
          (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient hA LA c t ht s).manifold
              (F.pair s).ambientManifold
              ((localMaslovComparison cAF heAF hbaseAF F eAsF hpF hcF c t ht s hs).trans
                (F.ambientCompletionPresentation s).equiv) (endpointsF s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient hA LA c t ht s).manifold
              (F.pair s).ambientManifold
              ((localMaslovComparison cAF heAF hbaseAF F eAsF hpF hcF c t ht s hs).trans
                (F.ambientCompletionPresentation s).equiv) (endpointsF s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold (2 * n))
            (O : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (F.pair s).ambientCompletion (W s)
              (fun y => chartValue cAF (O.compact s) s ((eAsF s).symm y)),
            markings = (fun s => O.ambientMarkingAt cAF heAF hbaseAF F hA eAsF hpF hcF s) ∧
            (∀ s x, (markings s).equiv
              ((F.pair s).ambientCompletion.inclusion.map (eAsF s x).val) =
                chartValue cAF (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
              (t : Parameter) (localCompletionF : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ localCompletionF.base),
              (localCompletionF.ambientEndpointSliceComparison LA cAF heAF hbaseAF s hs F hA eAsF hpF hcF).equiv.trans
                (markings s).equiv = O.localEquiv localCompletionF s hs) ∧
          ∃ (hpMF : ∀ s x,
            ((F.pair s).ribbonDomain.liouville.primitive (eMsF s x).val).compContinuousLinearMap
              (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2))
                (fun y => (eMsF s y).val) x) = PM.formInTrivialization cMF s x)
            (hcMF : ∀ s, HasNativeCoordinateExtensions (k := R.k)
              (F.pair s).ribbonDomain.domain.extension (fun x => (eMsF s x).val)),
          (∀ (H : Parameter → CompleteLiouvilleManifold (2 * n - 2))
            (originalRibbonMarkingsF : OriginalBundleCompletionMarkingData LM H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (F.pair s).ribbonCompletion (H s)
              (fun y => chartValue cMF (originalRibbonMarkingsF.compact s) s ((eMsF s).symm y)),
            ribbonMarkings = (fun s => originalRibbonMarkingsF.ribbonMarkingAt cMF heMF hbaseMF F R.dimension eMsF hpMF hcMF s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((F.pair s).ribbonCompletion.inclusion.map (eMsF s x).val) =
                chartValue cMF (originalRibbonMarkingsF.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := R.k) (M := R.M) (E := EM))
              (t : Parameter) (localCompletionF : LocalCompletionFamily PM c t)
              (s : Parameter) (hs : s ∈ localCompletionF.base),
              (localCompletionF.ribbonEndpointSliceComparison LM cMF heMF hbaseMF s hs F R.dimension eMsF hpMF hcMF).equiv.trans
                (ribbonMarkings s).equiv = originalRibbonMarkingsF.localEquiv localCompletionF s hs) ∧
    ∃ (cAG : Trivialization A' (π A' EA')) (cMG : Trivialization R.N (π R.N EN)),
      ∃ (hbaseAG : cAG.baseSet = univ) (hbaseMG : cMG.baseSet = univ),
      ∃ (heAG : CompatibleTrivialization (𝓡∂ (a' + 1)) EA' cAG)
        (heMG : CompatibleTrivialization (𝓡∂ (R.k + 1)) EN cMG),
      let lamG := PA'.formInTrivialization cAG
      let μG := PN.formInTrivialization cMG
      let jG := PJ'.mapInTrivializations cMG cAG heAG
      let bG := PW'.witnessInTrivialization cAG heAG
      (∀ dA (hdA : dA ∈ trivializationAtlas A' EA') t, t ∈ dA.baseSet → ∀ x vs,
        lamG t x vs = PA'.form ⟨dA, hdA⟩ t (cAG.coordChange dA t x)
          (fun i => mfderiv (𝓡∂ (a' + 1)) (𝓡∂ (a' + 1)) (cAG.coordChange dA t) x (vs i))) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas R.N EN) t, t ∈ dM.baseSet → ∀ x vs,
        μG t x vs = PN.form ⟨dM, hdM⟩ t (cMG.coordChange dM t x)
          (fun i => mfderiv (𝓡∂ (R.k + 1)) (𝓡∂ (R.k + 1)) (cMG.coordChange dM t) x (vs i))) ∧
      (∀ dA (hdA : dA ∈ trivializationAtlas A' EA') t, t ∈ dA.baseSet → ∀ x,
        bG t x = PW'.witness ⟨dA, hdA⟩ t
          (boundaryFamilyOn (cAG.baseSet ∩ dA.baseSet) (cAG.coordChange dA)
            (compatibleTransition_boundary cAG dA heAG (compatibleTrivialization_of_mem hdA)) t x)) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas R.N EN) dA (hdA : dA ∈ trivializationAtlas A' EA') t,
        t ∈ dM.baseSet ∩ dA.baseSet → ∀ x,
        (jG t x).val = dA.coordChange cAG t (PJ'.map ⟨dM, hdM⟩ ⟨dA, hdA⟩ t
          (cMG.coordChange dM t x)).val) ∧
      ∃ G : PairDeformation n,
      ∃ (eAsG : ∀ t, Diffeomorph (𝓡∂ (a' + 1)) (𝓡∂ (2 * n)) A'
          (G.pair t).ambientDomain.domain.Point ∞)
        (eMsG : ∀ t, Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.N
          (G.pair t).ribbonDomain.domain.Point ∞)
        (eBsG : ∀ t, (IntrinsicBoundary.smoothManifold a' A').SmoothEquiv
          (G.pair t).ambientDomain.domain.boundary),
      ∃ (RAG : ℝ → Diffeomorph (𝓡∂ (a' + 1)) (𝓡∂ (a' + 1)) A' A' ∞)
        (RMG : ℝ → Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (R.k + 1)) R.N R.N ∞),
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (a' + 1)) RAG ∧
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (R.k + 1)) RMG ∧
        (∀ t x, (G.ambientPresentation t).extensionEquiv
          ((eAsG parameterZero (RAG t.val x)).val) = (eAsG t x).val) ∧
        (∀ t x, (G.ribbonPresentation t).extensionEquiv
          ((eMsG parameterZero (RMG t.val x)).val) = (eMsG t x).val) ∧
        (∀ t x, (G.ambientPresentation t).boundaryEquiv (eBsG parameterZero x) = eBsG t x) ∧
        (∀ t : Parameter,
        let P := G.pair t
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBsG t) x) = ((eAsG t) x.val).val) ∧
        (∀ x, (P.ambientDomain.liouville.primitive ((eAsG t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (a' + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAsG t) y).val) x) = lamG t x) ∧
        (IntrinsicBoundary.smoothManifold a' A').pullback P.ambientDomain.domain.boundary (eBsG t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (lamG t) ∧
        (∀ x, P.ribbonEmbedding.map ((eMsG t) x).val = (eBsG t) (jG t x)) ∧
        (∀ x, P.witness ((eBsG t) x) = bG t x) ∧
        (∀ x, (P.ribbonDomain.liouville.primitive ((eMsG t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMsG t) y).val) x) = μG t x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBsG t) '' range (jG t) ∧
        P.embeddedCore = (fun x => (eBsG t) (jG t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
          P.ribbonCompletion.ambient.completeFlow.flow s
            (P.ribbonCompletion.inclusion.map ((eMsG t) x).val) ∈
              range (fun y => P.ribbonCompletion.inclusion.map ((eMsG t) y).val)} ∧
        HasNativeCoordinateExtensions (k := a') P.ambientDomain.domain.extension (fun x => ((eAsG t) x).val) ∧
        HasNativeCoordinateExtensions (k := R.k) P.ribbonDomain.domain.extension (fun x => ((eMsG t) x).val)) ∧
      ∃ (hpG : ∀ s x, ((G.pair s).ambientDomain.liouville.primitive (eAsG s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a' + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAsG s y).val) x) =
          PA'.formInTrivialization cAG s x)
        (hcG : ∀ s, HasNativeCoordinateExtensions (k := a')
          (G.pair s).ambientDomain.domain.extension (fun x => (eAsG s x).val)),
      ∃ fG : MaslovFamily G.source.ambientManifold G.completedSymplecticExtension,
        (∀ s : Parameter, fG.J s.val = S'.descendedJ cAG heAG hbaseAG G eAsG hpG hcG s) ∧
        (∀ s : Parameter, fG.tensor s.val = S'.descendedTensor cAG heAG hbaseAG G eAsG hpG hcG s) ∧
        (∀ (c : OriginalCompactChart (k := a') (M := A') (E := EA'))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA'.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient hA' LA' c t ht s).manifold
            G.source.ambientManifold (localMaslovComparison cAG heAG hbaseAG G eAsG hpG hcG c t ht s hs)
            (fG.J s.val) = S'.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient hA' LA' c t ht s).manifold
            G.source.ambientManifold (localMaslovComparison cAG heAG hbaseAG G eAsG hpG hcG c t ht s hs)
            (fG.tensor s.val) = S'.tensor c t ht s hs) ∧
        let endpointsG := G.maslovFamilyRepresentative fG
        let gradeG := G.gradedOfMaslovFamily fG
        gradeG.etaExtension = G.completedSymplecticExtension ∧ gradeG.family = fG ∧
        ∃ actualGradeG : GradedPairDeformation G (endpointsG parameterZero) (endpointsG parameterOne),
          actualGradeG = gradeG ∧
          (∀ (c : OriginalCompactChart (k := a') (M := A') (E := EA'))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA'.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient hA' LA' c t ht s).manifold
              (G.pair s).ambientManifold
              ((localMaslovComparison cAG heAG hbaseAG G eAsG hpG hcG c t ht s hs).trans
                (G.ambientCompletionPresentation s).equiv) (endpointsG s).J = S'.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient hA' LA' c t ht s).manifold
              (G.pair s).ambientManifold
              ((localMaslovComparison cAG heAG hbaseAG G eAsG hpG hcG c t ht s hs).trans
                (G.ambientCompletionPresentation s).equiv) (endpointsG s).tensor =
                  S'.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold (2 * n))
            (O : OriginalBundleCompletionMarkingData LA' W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (G.pair s).ambientCompletion (W s)
              (fun y => chartValue cAG (O.compact s) s ((eAsG s).symm y)),
            markings = (fun s => O.ambientMarkingAt cAG heAG hbaseAG G hA' eAsG hpG hcG s) ∧
            (∀ s x, (markings s).equiv
              ((G.pair s).ambientCompletion.inclusion.map (eAsG s x).val) =
                chartValue cAG (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := a') (M := A') (E := EA'))
              (t : Parameter) (localCompletionG : LocalCompletionFamily PA' c t)
              (s : Parameter) (hs : s ∈ localCompletionG.base),
              (localCompletionG.ambientEndpointSliceComparison LA' cAG heAG hbaseAG s hs G hA' eAsG hpG hcG).equiv.trans
                (markings s).equiv = O.localEquiv localCompletionG s hs) ∧
          ∃ (hpMG : ∀ s x,
            ((G.pair s).ribbonDomain.liouville.primitive (eMsG s x).val).compContinuousLinearMap
              (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2))
                (fun y => (eMsG s y).val) x) = PN.formInTrivialization cMG s x)
            (hcMG : ∀ s, HasNativeCoordinateExtensions (k := R.k)
              (G.pair s).ribbonDomain.domain.extension (fun x => (eMsG s x).val)),
          (∀ (H : Parameter → CompleteLiouvilleManifold (2 * n - 2))
            (originalRibbonMarkingsG : OriginalBundleCompletionMarkingData LN H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (G.pair s).ribbonCompletion (H s)
              (fun y => chartValue cMG (originalRibbonMarkingsG.compact s) s ((eMsG s).symm y)),
            ribbonMarkings = (fun s => originalRibbonMarkingsG.ribbonMarkingAt cMG heMG hbaseMG G R.dimension eMsG hpMG hcMG s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((G.pair s).ribbonCompletion.inclusion.map (eMsG s x).val) =
                chartValue cMG (originalRibbonMarkingsG.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := R.k) (M := R.N) (E := EN))
              (t : Parameter) (localCompletionG : LocalCompletionFamily PN c t)
              (s : Parameter) (hs : s ∈ localCompletionG.base),
              (localCompletionG.ribbonEndpointSliceComparison LN cMG heMG hbaseMG s hs G R.dimension eMsG hpMG hcMG).equiv.trans
                (ribbonMarkings s).equiv = originalRibbonMarkingsG.localEquiv localCompletionG s hs) ∧
    ∃ (hbF : ∀ x, F.target.ambientDomain.domain.boundaryInclusion.map
          (eBsF parameterOne x) = (eAsF parameterOne x.val).val)
      (hbG : ∀ x, G.source.ambientDomain.domain.boundaryInclusion.map
          (eBsG parameterZero x) = (eAsG parameterZero x.val).val)
      (hjF : ∀ x, F.target.ribbonEmbedding.map (eMsF parameterOne x).val =
          eBsF parameterOne (PJ.mapInTrivializations cMF cAF heAF parameterOne x))
      (hjG : ∀ x, G.source.ribbonEmbedding.map (eMsG parameterZero x).val =
          eBsG parameterZero (PJ'.mapInTrivializations cMG cAG heAG parameterZero x)),
    let J := O.toNativeCompletionJunction_of_originalRibbonBundleData
        cAF cAG heAF heAG hbaseAF hbaseAG hs hs' F G eAsF eAsG hpF hpG hcF hcG R
        (eBsF parameterOne) (eBsG parameterZero) hbF hbG
        PM PN LM LN PJ PJ' cM cN (LM.localCompletionFamily cM tM htM)
        (LN.localCompletionFamily cN tN htN) hsM hsN hμ hν hj hj'
        cMF cMG heMF heMG hbaseMF hbaseMG eMsF eMsG hpMF hpMG hcMF hcMG hjF hjG
    ∃ mid : GradedCompletionIdentification J.identification
      (endpointsF parameterOne) (endpointsG parameterZero),
      (∀ u, mid.family.J u = pullbackAlmostComplex F.target.ambientManifold
        J.ambient.X J.ambient.S.symm (H.family.J u)) ∧
      (∀ u, mid.family.tensor u = pullbackSquaredTensor F.target.ambientManifold
        J.ambient.X J.ambient.S.symm (H.family.tensor u)) ∧
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
            (.deformation actualGradeF)).cons (.identification mid)).cons (.deformation actualGradeG)) ∧
        path.length = 3 ∧ path.vertices = [F.source, F.target, G.source, G.target] := by
  obtain ⟨cAF, cMF, hbaseAF, hbaseMF, heAF, heMF, hcovAF, hcovMF, hwF, hjcovF,
    F, eAsF, eMsF, eBsF, RAF, RMF, hRAF, hRMF, hsquareF, hsquareMF, hsquareBF, hpointF,
    hpF, hcF, fF, hfJF, hfTF, hrecoverF, hetaF, hfamilyF, actualGradeF, hactualGradeF,
    hendpointF, hmarkingsF, hpMF, hcMF, hribbonMarkingsF⟩ :=
      exists_pairDeformation_with_originalMaslovFamily hA R.dimension PA PM PW PJ LA LM LP S hS
  obtain ⟨cAG, cMG, hbaseAG, hbaseMG, heAG, heMG, hcovAG, hcovMG, hwG, hjcovG,
    G, eAsG, eMsG, eBsG, RAG, RMG, hRAG, hRMG, hsquareG, hsquareMG, hsquareBG, hpointG,
    hpG, hcG, fG, hfJG, hfTG, hrecoverG, hetaG, hfamilyG, actualGradeG, hactualGradeG,
    hendpointG, hmarkingsG, hpMG, hcMG, hribbonMarkingsG⟩ :=
      exists_pairDeformation_with_originalMaslovFamily hA' R.dimension PA' PN PW' PJ' LA' LN LP' S' hS'
  have hbF := (hpointF parameterOne).1
  have hbG := (hpointG parameterZero).1
  have hjF := (hpointF parameterOne).2.2.2.1
  have hjG := (hpointG parameterZero).2.2.2.1
  let J := O.toNativeCompletionJunction_of_originalRibbonBundleData
    cAF cAG heAF heAG hbaseAF hbaseAG hs hs' F G eAsF eAsG hpF hpG hcF hcG R
    (eBsF parameterOne) (eBsG parameterZero) hbF hbG
    PM PN LM LN PJ PJ' cM cN (LM.localCompletionFamily cM tM htM)
    (LN.localCompletionFamily cN tN htN) hsM hsN hμ hν hj hj'
    cMF cMG heMF heMG hbaseMF hbaseMG eMsF eMsG hpMF hpMG hcMF hcMG hjF hjG
  obtain ⟨hJF, hTF⟩ := S.pullback_maslovFamilyRepresentative_descended
    cAF heAF hbaseAF F eAsF hpF hcF fF hfJF hfTF c t ht parameterOne hs
  obtain ⟨hJG, hTG⟩ := S'.pullback_maslovFamilyRepresentative_descended
    cAG heAG hbaseAG G eAsG hpG hcG fG hfJG hfTG c' t' ht' parameterZero hs'
  have hnativeJF : nativeSource.J = pullbackAlmostComplex J.ambient.X F.target.ambientManifold
      J.ambient.S (F.maslovFamilyRepresentative fF parameterOne).J := hSourceJ.trans hJF.symm
  have hnativeTF : nativeSource.tensor = pullbackSquaredTensor J.ambient.X F.target.ambientManifold
      J.ambient.S (F.maslovFamilyRepresentative fF parameterOne).tensor := hSourceT.trans hTF.symm
  have hnativeJG : nativeTarget.J = pullbackAlmostComplex J.ambient.Y G.source.ambientManifold
      J.ambient.S' (G.maslovFamilyRepresentative fG parameterZero).J := hTargetJ.trans hJG.symm
  have hnativeTG : nativeTarget.tensor = pullbackSquaredTensor J.ambient.Y G.source.ambientManifold
      J.ambient.S' (G.maslovFamilyRepresentative fG parameterZero).tensor := hTargetT.trans hTG.symm
  let mid := J.gradedLiftOfOriginalHomotopy nativeSource nativeTarget H
    (F.maslovFamilyRepresentative fF parameterOne) (G.maslovFamilyRepresentative fG parameterZero)
    (by
      intro x v
      rw [hnativeJF]
      exact pullbackAlmostComplex_intertwines _ _ _ _ x v)
    (by
      intro x vs
      rw [hnativeTF]
      rfl)
    (by
      intro x v
      rw [hnativeJG]
      exact pullbackAlmostComplex_intertwines _ _ _ _ x v)
    (by
      intro x vs
      rw [hnativeTG]
      rfl)
  refine ⟨cAF, cMF, hbaseAF, hbaseMF, heAF, heMF, hcovAF, hcovMF, hwF, hjcovF,
    F, eAsF, eMsF, eBsF, RAF, RMF, hRAF, hRMF, hsquareF, hsquareMF, hsquareBF, hpointF,
    hpF, hcF, fF, hfJF, hfTF, hrecoverF, hetaF, hfamilyF, actualGradeF, hactualGradeF,
    hendpointF, hmarkingsF, hpMF, hcMF, hribbonMarkingsF,
    cAG, cMG, hbaseAG, hbaseMG, heAG, heMG, hcovAG, hcovMG, hwG, hjcovG,
    G, eAsG, eMsG, eBsG, RAG, RMG, hRAG, hRMG, hsquareG, hsquareMG, hsquareBG, hpointG,
    hpG, hcG, fG, hfJG, hfTG, hrecoverG, hetaG, hfamilyG, actualGradeG, hactualGradeG,
    hendpointG, hmarkingsG, hpMG, hcMG, hribbonMarkingsG, hbF, hbG, hjF, hjG,
    mid, fun _ => rfl, fun _ => rfl, J.identification_ambientEquiv,
    J.identification_boundaryEquiv, J.identification_shift, ?_⟩
  exact ⟨(((GradedComparisonChain.nil (F.maslovFamilyRepresentative fF parameterZero)).cons
    (.deformation actualGradeF)).cons (.identification mid)).cons (.deformation actualGradeG),
    rfl, rfl, rfl⟩

end FsFltz.Geometry.IntrinsicSmoothBundle
