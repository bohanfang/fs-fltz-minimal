import FsFltz.Geometry.OriginalBundlePositiveJunctionGrading
import FsFltz.Geometry.OriginalBundleZeroJunctionGrading

/-!
# Retained realizations of original marked and graded pair bundles

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–244; `g:initial`, lines 374–384; and
`sec:lean`, lines 788–814. These structures expose the complete output of
one original-bundle construction so a finite itinerary can choose each
realization once and reuse it at both neighboring junctions. The inputs are
original bundles, their geometric laws and local Maslov regularity germs.
No represented pair, completion identification or grading lift is input.

The existence results are conditional foundational transports. They do
not construct the toric source data, the FLTZ endpoint or its prescribed
homotopy. The source geometric theorem remains unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- Original source data for one positive-dimensional ribbon bundle.
Only original geometry and local smooth Maslov data occur in the fields. -/
structure OriginalPositiveBundle (a k n : ℕ) [NeZero n] [NeZero (2 * n - 2)] where
  A : Type
  M : Type
  [topologyA : TopologicalSpace A]
  [separatedA : T2Space A]
  [countableA : SecondCountableTopology A]
  [compactA : CompactSpace A]
  [chartedA : ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [manifoldA : IsManifold (𝓡∂ (a + 1)) ∞ A]
  [topologyM : TopologicalSpace M]
  [separatedM : T2Space M]
  [countableM : SecondCountableTopology M]
  [compactM : CompactSpace M]
  [chartedM : ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [manifoldM : IsManifold (𝓡∂ (k + 1)) ∞ M]
  EA : Parameter → Type
  EM : Parameter → Type
  [topologyEA : ∀ t, TopologicalSpace (EA t)]
  [topologyEM : ∀ t, TopologicalSpace (EM t)]
  [topologyTotalA : TopologicalSpace (TotalSpace A EA)]
  [topologyTotalM : TopologicalSpace (TotalSpace M EM)]
  [bundleA : SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  [bundleM : SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]
  hdimA : a + 1 = 2 * n
  hdimM : k + 1 = 2 * n - 2
  PA : BundlePrimitiveData (k := a) (M := A) EA
  PM : BundlePrimitiveData (k := k) (M := M) EM
  PW : BundleWitnessData (k := a) (M := A) EA
  PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA
  LA : OriginalBundleLiouvilleLaws PA
  LM : OriginalBundleLiouvilleLaws PM
  LP : OriginalBundlePairLaws PA PM PW PJ
  S : OriginalLocalCompletionMaslovData PA LA (n := n) hdimA
  hS : OriginalLocalCompletionMaslovCoframeGerms S

attribute [instance]
  OriginalPositiveBundle.topologyA
  OriginalPositiveBundle.separatedA
  OriginalPositiveBundle.countableA
  OriginalPositiveBundle.compactA
  OriginalPositiveBundle.chartedA
  OriginalPositiveBundle.manifoldA
  OriginalPositiveBundle.topologyM
  OriginalPositiveBundle.separatedM
  OriginalPositiveBundle.countableM
  OriginalPositiveBundle.compactM
  OriginalPositiveBundle.chartedM
  OriginalPositiveBundle.manifoldM
  OriginalPositiveBundle.topologyEA
  OriginalPositiveBundle.topologyEM
  OriginalPositiveBundle.topologyTotalA
  OriginalPositiveBundle.topologyTotalM
  OriginalPositiveBundle.bundleA
  OriginalPositiveBundle.bundleM

/-- One chosen realization, retaining original covariance, compact geometry,
coherent presentations, full Maslov recovery and both marking recoveries. -/
structure OriginalPositiveRealization {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)] (D : OriginalPositiveBundle a k n) where
  cA : Trivialization D.A (π D.A D.EA)
  cM : Trivialization D.M (π D.M D.EM)
  hbaseA : cA.baseSet = univ
  hbaseM : cM.baseSet = univ
  heA : CompatibleTrivialization (𝓡∂ (a + 1)) D.EA cA
  heM : CompatibleTrivialization (𝓡∂ (k + 1)) D.EM cM
  covarianceA : ∀ dA (hdA : dA ∈ trivializationAtlas D.A D.EA) t, t ∈ dA.baseSet → ∀ x vs,
    (D.PA.formInTrivialization cA) t x vs = D.PA.form ⟨dA, hdA⟩ t (cA.coordChange dA t x)
    (fun i => mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) (cA.coordChange dA t) x (vs i))
  covarianceM : ∀ dM (hdM : dM ∈ trivializationAtlas D.M D.EM) t, t ∈ dM.baseSet → ∀ x vs,
    (D.PM.formInTrivialization cM) t x vs = D.PM.form ⟨dM, hdM⟩ t (cM.coordChange dM t x)
    (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (cM.coordChange dM t) x (vs i))
  witnessCovariance : ∀ dA (hdA : dA ∈ trivializationAtlas D.A D.EA) t, t ∈ dA.baseSet → ∀ x,
    (D.PW.witnessInTrivialization cA heA) t x = D.PW.witness ⟨dA, hdA⟩ t
    (boundaryFamilyOn (cA.baseSet ∩ dA.baseSet) (cA.coordChange dA)
    (compatibleTransition_boundary cA dA heA (compatibleTrivialization_of_mem hdA)) t x)
  embeddingCovariance : ∀ dM (hdM : dM ∈ trivializationAtlas D.M D.EM) dA (hdA : dA ∈ trivializationAtlas D.A D.EA) t,
    t ∈ dM.baseSet ∩ dA.baseSet → ∀ x,
    ((D.PJ.mapInTrivializations cM cA heA) t x).val = dA.coordChange cA t (D.PJ.map ⟨dM, hdM⟩ ⟨dA, hdA⟩ t
    (cM.coordChange dM t x)).val
  Q : PairDeformation n
  eAs : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) D.A
    (Q.pair t).ambientDomain.domain.Point ∞
  eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) D.M
    (Q.pair t).ribbonDomain.domain.Point ∞
  eBs : ∀ t, (IntrinsicBoundary.smoothManifold a D.A).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary
  RA : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) D.A D.A ∞
  RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) D.M D.M ∞
  smoothRA : IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) RA
  smoothRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM
  ambientSquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val
  ribbonSquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val
  boundarySquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x
  geometry : ∀ t : Parameter,
    let P := Q.pair t
    (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBs t) x) = ((eAs t) x.val).val) ∧
    (∀ x, (P.ambientDomain.liouville.primitive ((eAs t) x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAs t) y).val) x) = (D.PA.formInTrivialization cA) t x) ∧
    (IntrinsicBoundary.smoothManifold a D.A).pullback P.ambientDomain.domain.boundary (eBs t)
    (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
    IntrinsicBoundary.restrictForm ((D.PA.formInTrivialization cA) t) ∧
    (∀ x, P.ribbonEmbedding.map ((eMs t) x).val = (eBs t) ((D.PJ.mapInTrivializations cM cA heA) t x)) ∧
    (∀ x, P.witness ((eBs t) x) = (D.PW.witnessInTrivialization cA heA) t x) ∧
    (∀ x, (P.ribbonDomain.liouville.primitive ((eMs t) x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMs t) y).val) x) = (D.PM.formInTrivialization cM) t x) ∧
    P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBs t) '' range ((D.PJ.mapInTrivializations cM cA heA) t) ∧
    P.embeddedCore = (fun x => (eBs t) ((D.PJ.mapInTrivializations cM cA heA) t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
    P.ribbonCompletion.ambient.completeFlow.flow s
    (P.ribbonCompletion.inclusion.map ((eMs t) x).val) ∈
    range (fun y => P.ribbonCompletion.inclusion.map ((eMs t) y).val)} ∧
    HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eAs t) x).val) ∧
    HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => ((eMs t) x).val)
  hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
    D.PA.formInTrivialization cA s x
  hc : ∀ s, HasNativeCoordinateExtensions (k := a)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)
  f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension
  familyJ : ∀ s : Parameter, f.J s.val = D.S.descendedJ cA heA hbaseA Q eAs hp hc s
  familyTensor : ∀ s : Parameter, f.tensor s.val = D.S.descendedTensor cA heA hbaseA Q eAs hp hc s
  recovery : ∀ (c : OriginalCompactChart (k := a) (M := D.A) (E := D.EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (D.LA.localCompletionFamily c t ht).base),
    pullbackAlmostComplex (localMaslovAmbient D.hdimA D.LA c t ht s).manifold
    Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
    (f.J s.val) = D.S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient D.hdimA D.LA c t ht s).manifold
    Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
    (f.tensor s.val) = D.S.tensor c t ht s hs
  gradeExtension : (Q.gradedOfMaslovFamily f).etaExtension = Q.completedSymplecticExtension
  gradeFamily : (Q.gradedOfMaslovFamily f).family = f
  actualGrade : GradedPairDeformation Q ((Q.maslovFamilyRepresentative f) parameterZero) ((Q.maslovFamilyRepresentative f) parameterOne)
  grade_eq : actualGrade = (Q.gradedOfMaslovFamily f)
  endpointRecovery : ∀ (c : OriginalCompactChart (k := a) (M := D.A) (E := D.EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (D.LA.localCompletionFamily c t ht).base),
    pullbackAlmostComplex (localMaslovAmbient D.hdimA D.LA c t ht s).manifold
    (Q.pair s).ambientManifold
    ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
    (Q.ambientCompletionPresentation s).equiv) ((Q.maslovFamilyRepresentative f) s).J = D.S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient D.hdimA D.LA c t ht s).manifold
    (Q.pair s).ambientManifold
    ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
    (Q.ambientCompletionPresentation s).equiv) ((Q.maslovFamilyRepresentative f) s).tensor =
    D.S.tensor c t ht s hs
  ambientMarkings : ∀ (W : Parameter → CompleteLiouvilleManifold (2 * n))
    (O : OriginalBundleCompletionMarkingData D.LA W),
    ∃ markings : ∀ s : Parameter,
    InclusionMarking (Q.pair s).ambientCompletion (W s)
    (fun y => chartValue cA (O.compact s) s ((eAs s).symm y)),
    markings = (fun s => O.ambientMarkingAt cA heA hbaseA Q D.hdimA eAs hp hc s) ∧
    (∀ s x, (markings s).equiv
    ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
    chartValue cA (O.compact s) s x) ∧
    ∀ (c : OriginalCompactChart (k := a) (M := D.A) (E := D.EA))
    (t : Parameter) (F : LocalCompletionFamily D.PA c t)
    (s : Parameter) (hs : s ∈ F.base),
    (F.ambientEndpointSliceComparison D.LA cA heA hbaseA s hs Q D.hdimA eAs hp hc).equiv.trans
    (markings s).equiv = O.localEquiv F s hs
  hpM : ∀ s x,
    ((Q.pair s).ribbonDomain.liouville.primitive (eMs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
    (fun y => (eMs s y).val) x) = D.PM.formInTrivialization cM s x
  hcM : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ribbonDomain.domain.extension (fun x => (eMs s x).val)
  ribbonMarkings : ∀ (H : Parameter → CompleteLiouvilleManifold (2 * n - 2))
    (R : OriginalBundleCompletionMarkingData D.LM H),
    ∃ ribbonMarkings : ∀ s : Parameter,
    InclusionMarking (Q.pair s).ribbonCompletion (H s)
    (fun y => chartValue cM (R.compact s) s ((eMs s).symm y)),
    ribbonMarkings = (fun s => R.ribbonMarkingAt cM heM hbaseM Q D.hdimM eMs hpM hcM s) ∧
    (∀ s x, (ribbonMarkings s).equiv
    ((Q.pair s).ribbonCompletion.inclusion.map (eMs s x).val) =
    chartValue cM (R.compact s) s x) ∧
    ∀ (c : OriginalCompactChart (k := k) (M := D.M) (E := D.EM))
    (t : Parameter) (F : LocalCompletionFamily D.PM c t)
    (s : Parameter) (hs : s ∈ F.base),
    (F.ribbonEndpointSliceComparison D.LM cM heM hbaseM s hs Q D.hdimM eMs hpM hcM).equiv.trans
    (ribbonMarkings s).equiv = R.localEquiv F s hs

/-- The full retained realization is produced from original source data. -/
theorem OriginalPositiveBundle.nonempty_realization {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)] (D : OriginalPositiveBundle a k n) :
    Nonempty (OriginalPositiveRealization D) := by
  obtain ⟨cA, cM, hbaseA, hbaseM, heA, heM, covarianceA, covarianceM, witnessCovariance, embeddingCovariance, Q, eAs, eMs, eBs, RA, RM, smoothRA, smoothRM, ambientSquare, ribbonSquare, boundarySquare, geometry, hp, hc, f, familyJ, familyTensor, recovery, gradeExtension, gradeFamily, actualGrade, grade_eq, endpointRecovery, ambientMarkings, hpM, hcM, ribbonMarkings⟩ :=
    exists_pairDeformation_with_originalMaslovFamily D.hdimA D.hdimM D.PA D.PM D.PW D.PJ D.LA D.LM D.LP D.S D.hS
  exact ⟨⟨cA, cM, hbaseA, hbaseM, heA, heM, covarianceA, covarianceM, witnessCovariance, embeddingCovariance, Q, eAs, eMs, eBs, RA, RM, smoothRA, smoothRM, ambientSquare, ribbonSquare, boundarySquare, geometry, hp, hc, f, familyJ, familyTensor, recovery, gradeExtension, gradeFamily, actualGrade, grade_eq, endpointRecovery, ambientMarkings, hpM, hcM, ribbonMarkings⟩⟩

/-- Choose this source bundle once; finite-chain constructors retain and reuse
this exact choice at both adjacent junctions. -/
def OriginalPositiveBundle.realize {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)] (D : OriginalPositiveBundle a k n) : OriginalPositiveRealization D :=
  Classical.choice D.nonempty_realization

/-- Original source data for one zero-dimensional ribbon bundle.
Only original geometry and local smooth Maslov data occur in the fields. -/
structure OriginalZeroBundle where
  A : Type
  M : Type
  [topologyA : TopologicalSpace A]
  [separatedA : T2Space A]
  [countableA : SecondCountableTopology A]
  [compactA : CompactSpace A]
  [chartedA : ChartedSpace (EuclideanHalfSpace (1 + 1)) A]
  [manifoldA : IsManifold (𝓡∂ (1 + 1)) ∞ A]
  [topologyM : TopologicalSpace M]
  [separatedM : T2Space M]
  [countableM : SecondCountableTopology M]
  [compactM : CompactSpace M]
  [chartedM : ChartedSpace (Model 0) M]
  [manifoldM : IsManifold 𝓘(ℝ, Model 0) ∞ M]
  EA : Parameter → Type
  EM : Parameter → Type
  [topologyEA : ∀ t, TopologicalSpace (EA t)]
  [topologyEM : ∀ t, TopologicalSpace (EM t)]
  [topologyTotalA : TopologicalSpace (TotalSpace A EA)]
  [topologyTotalM : TopologicalSpace (TotalSpace M EM)]
  [bundleA : SmoothCompactBundle (𝓡∂ (1 + 1)) (F := A) EA]
  [bundleM : SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  PA : BundlePrimitiveData (k := 1) (M := A) EA
  PW : BundleWitnessData (k := 1) (M := A) EA
  PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA
  LA : OriginalBundleLiouvilleLaws PA
  hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
    Function.Injective (PJ.map cM cA t)
  μ : Parameter → (sourceManifold M).Form 1
  S : OriginalLocalCompletionMaslovData PA LA (n := 1) rfl
  hS : OriginalLocalCompletionMaslovCoframeGerms S

attribute [instance]
  OriginalZeroBundle.topologyA
  OriginalZeroBundle.separatedA
  OriginalZeroBundle.countableA
  OriginalZeroBundle.compactA
  OriginalZeroBundle.chartedA
  OriginalZeroBundle.manifoldA
  OriginalZeroBundle.topologyM
  OriginalZeroBundle.separatedM
  OriginalZeroBundle.countableM
  OriginalZeroBundle.compactM
  OriginalZeroBundle.chartedM
  OriginalZeroBundle.manifoldM
  OriginalZeroBundle.topologyEA
  OriginalZeroBundle.topologyEM
  OriginalZeroBundle.topologyTotalA
  OriginalZeroBundle.topologyTotalM
  OriginalZeroBundle.bundleA
  OriginalZeroBundle.bundleM

/-- One chosen realization, retaining original covariance, compact geometry,
coherent presentations, full Maslov recovery and both marking recoveries. -/
structure OriginalZeroRealization (D : OriginalZeroBundle) where
  eM : Trivialization D.M (π D.M D.EM)
  eA : Trivialization D.A (π D.A D.EA)
  hbaseM : eM.baseSet = univ
  hbaseA : eA.baseSet = univ
  _heM : CompatibleTrivialization 𝓘(ℝ, Model 0) D.EM eM
  heA : CompatibleTrivialization (𝓡∂ 2) D.EA eA
  covarianceA : ∀ c hc t, t ∈ c.baseSet →
    (D.PA.formInTrivialization eA) t = nativePullbackForm (eA.coordChange c t) (D.PA.form ⟨c, hc⟩ t)
  embeddingCovariance : ∀ (cM : Trivialization D.M (π D.M D.EM)) hcM (cA : Trivialization D.A (π D.A D.EA)) hcA t,
    t ∈ cM.baseSet ∩ cA.baseSet → ∀ x,
    ((D.PJ.mapInTrivializations eM eA heA) t x).val = cA.coordChange eA t
    (D.PJ.map ⟨cM, hcM⟩ ⟨cA, hcA⟩ t (eM.coordChange cM t x)).val
  witnessCovariance : ∀ c hc t, t ∈ c.baseSet → ∀ x,
    (D.PW.witnessInTrivialization eA heA) t x = D.PW.witness ⟨c, hc⟩ t
    (boundaryFamilyOn (eA.baseSet ∩ c.baseSet) (eA.coordChange c)
    (compatibleTransition_boundary eA c heA (compatibleTrivialization_of_mem hc)) t x)
  Q : PairDeformation 1
  eAs : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) D.A
    (Q.pair t).ambientDomain.domain.Point ∞
  eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) D.M (Q.pair t).ribbonDomain.domain.Point ∞
  eBs : ∀ t, (IntrinsicBoundary.smoothManifold 1 D.A).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary
  RA : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) D.A D.A ∞
  RM : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) D.M D.M ∞
  smoothRA : IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) RA
  smoothRM : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RM
  ambientSquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val
  ribbonSquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    ((eFs parameterZero (RM t.val x)).val) = (eFs t x).val
  boundarySquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x
  geometry : ∀ t,
    let P := Q.pair t;
    (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val) ∧
    (∀ x, P.ribbonEmbedding.map (eFs t x).val = eBs t ((D.PJ.mapInTrivializations eM eA heA) t x)) ∧
    (∀ x, P.witness (eBs t x) = (D.PW.witnessInTrivialization eA heA) t x) ∧
    P.embeddedCore = (eBs t) '' range ((D.PJ.mapInTrivializations eM eA heA) t) ∧
    (∀ x, (P.ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = (D.PA.formInTrivialization eA) t x) ∧
    (sourceManifold D.M).pullback P.ribbonDomain.domain.extension
    (fun x => (eFs t x).val) P.ribbonDomain.liouville.primitive = D.μ t ∧
    (IntrinsicBoundary.smoothManifold 1 D.A).pullback P.ambientDomain.domain.boundary (eBs t)
    (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
    IntrinsicBoundary.restrictForm ((D.PA.formInTrivialization eA) t) ∧
    HasNativeCoordinateExtensions (k := 1)
    P.ambientDomain.domain.extension (fun x => (eAs t x).val)
  hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (2)) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
    D.PA.formInTrivialization eA s x
  hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)
  f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension
  familyJ : ∀ s : Parameter, f.J s.val = D.S.descendedJ eA heA hbaseA Q eAs hp hc s
  familyTensor : ∀ s : Parameter, f.tensor s.val = D.S.descendedTensor eA heA hbaseA Q eAs hp hc s
  recovery : ∀ (c : OriginalCompactChart (k := 1) (M := D.A) (E := D.EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (D.LA.localCompletionFamily c t ht).base),
    pullbackAlmostComplex (localMaslovAmbient rfl D.LA c t ht s).manifold
    Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
    (f.J s.val) = D.S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient rfl D.LA c t ht s).manifold
    Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
    (f.tensor s.val) = D.S.tensor c t ht s hs
  gradeExtension : (Q.gradedOfMaslovFamily f).etaExtension = Q.completedSymplecticExtension
  gradeFamily : (Q.gradedOfMaslovFamily f).family = f
  actualGrade : GradedPairDeformation Q ((Q.maslovFamilyRepresentative f) parameterZero) ((Q.maslovFamilyRepresentative f) parameterOne)
  grade_eq : actualGrade = (Q.gradedOfMaslovFamily f)
  endpointRecovery : ∀ (c : OriginalCompactChart (k := 1) (M := D.A) (E := D.EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (D.LA.localCompletionFamily c t ht).base),
    pullbackAlmostComplex (localMaslovAmbient rfl D.LA c t ht s).manifold
    (Q.pair s).ambientManifold
    ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
    (Q.ambientCompletionPresentation s).equiv) ((Q.maslovFamilyRepresentative f) s).J = D.S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient rfl D.LA c t ht s).manifold
    (Q.pair s).ambientManifold
    ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
    (Q.ambientCompletionPresentation s).equiv) ((Q.maslovFamilyRepresentative f) s).tensor =
    D.S.tensor c t ht s hs
  ambientMarkings : ∀ (W : Parameter → CompleteLiouvilleManifold 2)
    (O : OriginalBundleCompletionMarkingData D.LA W),
    ∃ markings : ∀ s : Parameter,
    InclusionMarking (Q.pair s).ambientCompletion (W s)
    (fun y => chartValue eA (O.compact s) s ((eAs s).symm y)),
    markings = (fun s => O.ambientMarkingAt eA heA hbaseA Q rfl eAs hp hc s) ∧
    (∀ s x, (markings s).equiv
    ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
    chartValue eA (O.compact s) s x) ∧
    ∀ (c : OriginalCompactChart (k := 1) (M := D.A) (E := D.EA))
    (t : Parameter) (F : LocalCompletionFamily D.PA c t)
    (s : Parameter) (hs : s ∈ F.base),
    (F.ambientEndpointSliceComparison D.LA eA heA hbaseA s hs Q rfl eAs hp hc).equiv.trans
    (markings s).equiv = O.localEquiv F s hs
  ribbonMarkings : ∀ (H : Parameter → CompleteLiouvilleManifold 0)
    (R : OriginalZeroBundleCompletionMarkingData (M := D.M) (E := D.EM) H),
    ∃ ribbonMarkings : ∀ s : Parameter,
    InclusionMarking (Q.pair s).ribbonCompletion (H s)
    (fun y => chartValue eM (R.compact s) s ((eFs s).symm y)),
    ribbonMarkings = (fun s => R.ribbonMarkingAt eM hbaseM Q eFs s) ∧
    (∀ s x, (ribbonMarkings s).equiv
    ((Q.pair s).ribbonCompletion.inclusion.map (eFs s x).val) =
    chartValue eM (R.compact s) s x) ∧
    ∀ (c : OriginalZeroCompactChart (M := D.M) (E := D.EM))
    (s : Parameter) (hs : s ∈ c.val.baseSet),
    (zeroRibbonEndpointEquiv eM hbaseM Q eFs c s hs).trans
    (ribbonMarkings s).equiv = R.chart c s hs

/-- The full retained realization is produced from original source data. -/
theorem OriginalZeroBundle.nonempty_realization (D : OriginalZeroBundle) :
    Nonempty (OriginalZeroRealization D) := by
  obtain ⟨eM, eA, hbaseM, hbaseA, _heM, heA, covarianceA, embeddingCovariance, witnessCovariance, Q, eAs, eFs, eBs, RA, RM, smoothRA, smoothRM, ambientSquare, ribbonSquare, boundarySquare, geometry, hp, hc, f, familyJ, familyTensor, recovery, gradeExtension, gradeFamily, actualGrade, grade_eq, endpointRecovery, ambientMarkings, ribbonMarkings⟩ :=
    exists_zero_pairDeformation_with_originalMaslovFamily D.PA D.LA D.PJ D.hPJ D.PW D.μ D.S D.hS
  exact ⟨⟨eM, eA, hbaseM, hbaseA, _heM, heA, covarianceA, embeddingCovariance, witnessCovariance, Q, eAs, eFs, eBs, RA, RM, smoothRA, smoothRM, ambientSquare, ribbonSquare, boundarySquare, geometry, hp, hc, f, familyJ, familyTensor, recovery, gradeExtension, gradeFamily, actualGrade, grade_eq, endpointRecovery, ambientMarkings, ribbonMarkings⟩⟩

/-- Choose this source bundle once; finite-chain constructors retain and reuse
this exact choice at both adjacent junctions. -/
def OriginalZeroBundle.realize (D : OriginalZeroBundle) : OriginalZeroRealization D :=
  Classical.choice D.nonempty_realization

end FsFltz.Geometry.IntrinsicSmoothBundle
