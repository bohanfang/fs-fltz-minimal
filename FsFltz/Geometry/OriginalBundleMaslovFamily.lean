import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovFamily
import FsFltz.Geometry.IntrinsicBundlePairFamily
import FsFltz.Geometry.IntrinsicBundleZeroPairFamily
import FsFltz.Geometry.PairDeformationMaslovFamily
import FsFltz.Geometry.OriginalBundleRibbonCompletionMarking

/-!
# Original pair bundles with their preselected smooth ambient data

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199,
`def:maslov`, lines 212–244, `g:initial`, lines 374–384,
and `sec:lean`, lines 788–814.
Choose the geometric realization once from the original pair bundle and
transport its independently supplied smooth ambient data to that same
completed family. The original ribbon, witness, primitives and coherent
presentations remain in the conclusion, including zero-dimensional ribbons.
The same supplied Maslov family constructs representatives on every completed
slice and an actual grade on that very deformation, with original-chart
recovery through the presentation-composed comparison.
Independently supplied original ambient and ribbon markings descend to the
same chosen completed slices, with their common compact inclusions and
recovery on every whole original local completion. Their existence is a
conditional source input; joint smoothness of the parameterwise markings is
not asserted.
This does not construct the toric comparison or prescribed endpoint homotopy.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

section PositiveRibbon

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]


/-- Realize one original pair bundle and its preselected smooth ambient data together,
retaining all original ribbon, witness, primitive, core and coherence equations.
The returned grade uses exactly this family's compatible field and tensor.
Both independently supplied original marking families descend to this same Q. -/
theorem exists_pairDeformation_with_originalMaslovFamily
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) EM)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
    (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
    (LP : OriginalBundlePairLaws PA PM PW PJ)
    (S : OriginalLocalCompletionMaslovData PA LA hdimA)
    (hS : OriginalLocalCompletionMaslovCoframeGerms S) :
    ∃ (cA : Trivialization A (π A EA)) (cM : Trivialization M (π M EM)),
      ∃ (hbaseA : cA.baseSet = univ) (hbaseM : cM.baseSet = univ),
      ∃ (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA cA)
        (heM : CompatibleTrivialization (𝓡∂ (k + 1)) EM cM),
      let lam := PA.formInTrivialization cA
      let μ := PM.formInTrivialization cM
      let j := PJ.mapInTrivializations cM cA heA
      let b := PW.witnessInTrivialization cA heA
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x vs,
        lam t x vs = PA.form ⟨dA, hdA⟩ t (cA.coordChange dA t x)
          (fun i => mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) (cA.coordChange dA t) x (vs i))) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas M EM) t, t ∈ dM.baseSet → ∀ x vs,
        μ t x vs = PM.form ⟨dM, hdM⟩ t (cM.coordChange dM t x)
          (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (cM.coordChange dM t) x (vs i))) ∧
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x,
        b t x = PW.witness ⟨dA, hdA⟩ t
          (boundaryFamilyOn (cA.baseSet ∩ dA.baseSet) (cA.coordChange dA)
            (compatibleTransition_boundary cA dA heA (compatibleTrivialization_of_mem hdA)) t x)) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas M EM) dA (hdA : dA ∈ trivializationAtlas A EA) t,
        t ∈ dM.baseSet ∩ dA.baseSet → ∀ x,
        (j t x).val = dA.coordChange cA t (PJ.map ⟨dM, hdM⟩ ⟨dA, hdA⟩ t
          (cM.coordChange dM t x)).val) ∧
      ∃ Q : PairDeformation n,
      ∃ (eAs : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
          (Q.pair t).ambientDomain.domain.Point ∞)
        (eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
          (Q.pair t).ribbonDomain.domain.Point ∞)
        (eBs : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
          (Q.pair t).ambientDomain.domain.boundary),
      ∃ (RA : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A ∞)
        (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞),
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) RA ∧
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val) ∧
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
        (∀ t : Parameter,
        let P := Q.pair t
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBs t) x) = ((eAs t) x.val).val) ∧
        (∀ x, (P.ambientDomain.liouville.primitive ((eAs t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAs t) y).val) x) = lam t x) ∧
        (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (lam t) ∧
        (∀ x, P.ribbonEmbedding.map ((eMs t) x).val = (eBs t) (j t x)) ∧
        (∀ x, P.witness ((eBs t) x) = b t x) ∧
        (∀ x, (P.ribbonDomain.liouville.primitive ((eMs t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMs t) y).val) x) = μ t x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBs t) '' range (j t) ∧
        P.embeddedCore = (fun x => (eBs t) (j t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
          P.ribbonCompletion.ambient.completeFlow.flow s
            (P.ribbonCompletion.inclusion.map ((eMs t) x).val) ∈
              range (fun y => P.ribbonCompletion.inclusion.map ((eMs t) y).val)} ∧
        HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eAs t) x).val) ∧
        HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => ((eMs t) x).val)) ∧
      ∃ (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization cA s x)
        (hc : ∀ s, HasNativeCoordinateExtensions (k := a)
          (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
        (∀ s : Parameter, f.J s.val = S.descendedJ cA heA hbaseA Q eAs hp hc s) ∧
        (∀ s : Parameter, f.tensor s.val = S.descendedTensor cA heA hbaseA Q eAs hp hc s) ∧
        (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpoints := Q.maslovFamilyRepresentative f
        let grade := Q.gradedOfMaslovFamily f
        grade.etaExtension = Q.completedSymplecticExtension ∧ grade.family = f ∧
        ∃ actualGrade : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
          actualGrade = grade ∧
          (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold (2 * n))
            (O : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ambientCompletion (W s)
              (fun y => chartValue cA (O.compact s) s ((eAs s).symm y)),
            markings = (fun s => O.ambientMarkingAt cA heA hbaseA Q hdimA eAs hp hc s) ∧
            (∀ s x, (markings s).equiv
              ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
                chartValue cA (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
              (t : Parameter) (F : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ambientEndpointSliceComparison LA cA heA hbaseA s hs Q hdimA eAs hp hc).equiv.trans
                (markings s).equiv = O.localEquiv F s hs) ∧
          ∃ (hpM : ∀ s x,
            ((Q.pair s).ribbonDomain.liouville.primitive (eMs s x).val).compContinuousLinearMap
              (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
                (fun y => (eMs s y).val) x) = PM.formInTrivialization cM s x)
            (hcM : ∀ s, HasNativeCoordinateExtensions (k := k)
              (Q.pair s).ribbonDomain.domain.extension (fun x => (eMs s x).val)),
          ∀ (H : Parameter → CompleteLiouvilleManifold (2 * n - 2))
            (R : OriginalBundleCompletionMarkingData LM H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ribbonCompletion (H s)
              (fun y => chartValue cM (R.compact s) s ((eMs s).symm y)),
            ribbonMarkings = (fun s => R.ribbonMarkingAt cM heM hbaseM Q hdimM eMs hpM hcM s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((Q.pair s).ribbonCompletion.inclusion.map (eMs s x).val) =
                chartValue cM (R.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := k) (M := M) (E := EM))
              (t : Parameter) (F : LocalCompletionFamily PM c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ribbonEndpointSliceComparison LM cM heM hbaseM s hs Q hdimM eMs hpM hcM).equiv.trans
                (ribbonMarkings s).equiv = R.localEquiv F s hs := by
  obtain ⟨cA, cM, hbaseA, hbaseM, heA, heM, hcovA, hcovM, hw, hj,
    Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint⟩ :=
      exists_pairDeformation_of_original_bundle_data hdimA hdimM PA PM PW PJ LA LM LP
  have hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
        PA.formInTrivialization cA s x := fun s => (hpoint s).2.1
  have hc : ∀ s, HasNativeCoordinateExtensions (k := a)
      (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val) := by
    intro s
    obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := hpoint s
    exact hc
  obtain ⟨f, hfJ, hfT⟩ := S.exists_maslovFamily_descended cA heA hbaseA Q eAs hp hc hS
    eBs (fun s => (hpoint s).1) hsquareB RA hRA hsquare
  refine ⟨cA, cM, hbaseA, hbaseM, heA, heM, hcovA, hcovM, hw, hj,
    Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint,
    hp, hc, f, hfJ, hfT, S.pullback_maslovFamily_descended cA heA hbaseA Q eAs hp hc f hfJ hfT,
    rfl, rfl, Q.gradedOfMaslovFamily f, rfl, ?_⟩
  constructor
  · intro c t ht s hs
    obtain ⟨hJ, hT⟩ := S.pullback_maslovFamily_descended cA heA hbaseA Q eAs hp hc f hfJ hfT
      c t ht s hs
    constructor
    · rw [pullbackAlmostComplex_trans, ← Q.maslovFamilyRepresentative_pullbackJ f s]
      exact hJ
    · rw [pullbackSquaredTensor_trans, ← Q.maslovFamilyRepresentative_pullbackTensor f s]
      exact hT
  · constructor
    · intro W O
      refine ⟨fun s => O.ambientMarkingAt cA heA hbaseA Q hdimA eAs hp hc s, rfl, ?_, ?_⟩
      · intro s x
        simpa only [Diffeomorph.symm_apply_apply] using
          (O.ambientMarkingAt cA heA hbaseA Q hdimA eAs hp hc s).inclusion (eAs s x)
      · intro c t F s hs
        exact O.ambientMarkingAt_recovers_original F cA heA hbaseA Q hdimA eAs hp hc s hs
    · have hpM : ∀ s x,
          ((Q.pair s).ribbonDomain.liouville.primitive (eMs s x).val).compContinuousLinearMap
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
              (fun y => (eMs s y).val) x) = PM.formInTrivialization cM s x := by
        intro s
        obtain ⟨_, _, _, _, _, hpM, _, _, _, _⟩ := hpoint s
        exact hpM
      have hcM : ∀ s, HasNativeCoordinateExtensions (k := k)
          (Q.pair s).ribbonDomain.domain.extension (fun x => (eMs s x).val) := by
        intro s
        obtain ⟨_, _, _, _, _, _, _, _, _, hcM⟩ := hpoint s
        exact hcM
      refine ⟨hpM, hcM, ?_⟩
      intro H R
      refine ⟨fun s => R.ribbonMarkingAt cM heM hbaseM Q hdimM eMs hpM hcM s, rfl, ?_, ?_⟩
      · intro s x
        simpa only [Diffeomorph.symm_apply_apply] using
          (R.ribbonMarkingAt cM heM hbaseM Q hdimM eMs hpM hcM s).inclusion (eMs s x)
      · intro c t F s hs
        exact R.ribbonMarkingAt_recovers_original F cM heM hbaseM Q hdimM eMs hpM hcM s hs

end PositiveRibbon

section ZeroRibbon

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]


/-- The rank-one realization retains the entire zero-dimensional ribbon and
its original core while transporting the same supplied smooth ambient data
and constructing the grade on the same chosen deformation. Independent
ambient and finite-ribbon markings recover their original atlas maps. -/
theorem exists_zero_pairDeformation_with_originalMaslovFamily
    (PA : BundlePrimitiveData (k := 1) (M := A) EA)
    (LA : OriginalBundleLiouvilleLaws PA)
    (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ.map cM cA t))
    (PW : BundleWitnessData (k := 1) (M := A) EA)
    (μ : Parameter → (sourceManifold M).Form 1)
    (S : OriginalLocalCompletionMaslovData PA LA (n := 1) rfl)
    (hS : OriginalLocalCompletionMaslovCoframeGerms S) :
    ∃ eM : Trivialization M (π M EM),
    ∃ eA : Trivialization A (π A EA), ∃ (hbaseM : eM.baseSet = univ) (hbaseA : eA.baseSet = univ),
    ∃ _heM : CompatibleTrivialization 𝓘(ℝ, Model 0) EM eM,
    ∃ heA : CompatibleTrivialization (𝓡∂ 2) EA eA,
    let α := PA.formInTrivialization eA;
    let j := PJ.mapInTrivializations eM eA heA;
    let b := PW.witnessInTrivialization eA heA;
    (∀ c hc t, t ∈ c.baseSet →
      α t = nativePullbackForm (eA.coordChange c t) (PA.form ⟨c, hc⟩ t)) ∧
    (∀ (cM : Trivialization M (π M EM)) hcM (cA : Trivialization A (π A EA)) hcA t,
      t ∈ cM.baseSet ∩ cA.baseSet → ∀ x,
      (j t x).val = cA.coordChange eA t
        (PJ.map ⟨cM, hcM⟩ ⟨cA, hcA⟩ t (eM.coordChange cM t x)).val) ∧
    (∀ c hc t, t ∈ c.baseSet → ∀ x,
      b t x = PW.witness ⟨c, hc⟩ t
        (boundaryFamilyOn (eA.baseSet ∩ c.baseSet) (eA.coordChange c)
          (compatibleTransition_boundary eA c heA (compatibleTrivialization_of_mem hc)) t x)) ∧
    ∃ Q : PairDeformation 1,
    ∃ eAs : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A
      (Q.pair t).ambientDomain.domain.Point ∞,
    ∃ eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞,
    ∃ eBs : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary,
    ∃ (RA : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A A ∞)
      (RM : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞),
      IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) RA ∧
      IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RM ∧
      (∀ t x, (Q.ambientPresentation t).extensionEquiv
        ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
      (∀ t x, (Q.ribbonPresentation t).extensionEquiv
        ((eFs parameterZero (RM t.val x)).val) = (eFs t x).val) ∧
      (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
      (∀ t,
      let P := Q.pair t;
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eFs t x).val = eBs t (j t x)) ∧
        (∀ x, P.witness (eBs t x) = b t x) ∧
        P.embeddedCore = (eBs t) '' range (j t) ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = α t x) ∧
        (sourceManifold M).pullback P.ribbonDomain.domain.extension
          (fun x => (eFs t x).val) P.ribbonDomain.liouville.primitive = μ t ∧
        (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (α t) ∧
        HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val)) ∧
      ∃ (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (2)) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization eA s x)
        (hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
          (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
        (∀ s : Parameter, f.J s.val = S.descendedJ eA heA hbaseA Q eAs hp hc s) ∧
        (∀ s : Parameter, f.tensor s.val = S.descendedTensor eA heA hbaseA Q eAs hp hc s) ∧
        (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpoints := Q.maslovFamilyRepresentative f
        let grade := Q.gradedOfMaslovFamily f
        grade.etaExtension = Q.completedSymplecticExtension ∧ grade.family = f ∧
        ∃ actualGrade : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
          actualGrade = grade ∧
          (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold 2)
            (O : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ambientCompletion (W s)
              (fun y => chartValue eA (O.compact s) s ((eAs s).symm y)),
            markings = (fun s => O.ambientMarkingAt eA heA hbaseA Q rfl eAs hp hc s) ∧
            (∀ s x, (markings s).equiv
              ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
                chartValue eA (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
              (t : Parameter) (F : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ambientEndpointSliceComparison LA eA heA hbaseA s hs Q rfl eAs hp hc).equiv.trans
                (markings s).equiv = O.localEquiv F s hs) ∧
          ∀ (H : Parameter → CompleteLiouvilleManifold 0)
            (R : OriginalZeroBundleCompletionMarkingData (M := M) (E := EM) H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ribbonCompletion (H s)
              (fun y => chartValue eM (R.compact s) s ((eFs s).symm y)),
            ribbonMarkings = (fun s => R.ribbonMarkingAt eM hbaseM Q eFs s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((Q.pair s).ribbonCompletion.inclusion.map (eFs s x).val) =
                chartValue eM (R.compact s) s x) ∧
            ∀ (c : OriginalZeroCompactChart (M := M) (E := EM))
              (s : Parameter) (hs : s ∈ c.val.baseSet),
              (zeroRibbonEndpointEquiv eM hbaseM Q eFs c s hs).trans
                (ribbonMarkings s).equiv = R.chart c s hs := by
  obtain ⟨eM, eA, hbaseM, hbaseA, heM, heA, hcovA, hj, hw,
    Q, eAs, eFs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint⟩ :=
      exists_zero_pairDeformation_of_original_bundle_data PA LA PJ hPJ PW μ
  have hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
        PA.formInTrivialization eA s x := by
    intro s
    obtain ⟨_, _, _, _, hp, _, _, _⟩ := hpoint s
    exact hp
  have hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
      (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val) := by
    intro s
    obtain ⟨_, _, _, _, _, _, _, hc⟩ := hpoint s
    exact hc
  obtain ⟨f, hfJ, hfT⟩ := S.exists_maslovFamily_descended eA heA hbaseA Q eAs hp hc hS
    eBs (fun s => (hpoint s).1) hsquareB RA hRA hsquare
  refine ⟨eM, eA, hbaseM, hbaseA, heM, heA, hcovA, hj, hw,
    Q, eAs, eFs, eBs, RA, RM, hRA, hRM, hsquare, hsquareM, hsquareB, hpoint,
    hp, hc, f, hfJ, hfT, S.pullback_maslovFamily_descended eA heA hbaseA Q eAs hp hc f hfJ hfT,
    rfl, rfl, Q.gradedOfMaslovFamily f, rfl, ?_⟩
  constructor
  · intro c t ht s hs
    obtain ⟨hJ, hT⟩ := S.pullback_maslovFamily_descended eA heA hbaseA Q eAs hp hc f hfJ hfT
      c t ht s hs
    constructor
    · rw [pullbackAlmostComplex_trans, ← Q.maslovFamilyRepresentative_pullbackJ f s]
      exact hJ
    · rw [pullbackSquaredTensor_trans, ← Q.maslovFamilyRepresentative_pullbackTensor f s]
      exact hT
  · constructor
    · intro W O
      refine ⟨fun s => O.ambientMarkingAt eA heA hbaseA Q rfl eAs hp hc s, rfl, ?_, ?_⟩
      · intro s x
        simpa only [Diffeomorph.symm_apply_apply] using
          (O.ambientMarkingAt eA heA hbaseA Q rfl eAs hp hc s).inclusion (eAs s x)
      · intro c t F s hs
        exact O.ambientMarkingAt_recovers_original F eA heA hbaseA Q rfl eAs hp hc s hs
    · intro H R
      refine ⟨fun s => R.ribbonMarkingAt eM hbaseM Q eFs s, rfl, ?_, ?_⟩
      · intro s x
        exact R.ribbonMarkingAt_native eM hbaseM Q eFs s x
      · intro c s hs
        exact R.ribbonMarkingAt_recovers_original eM hbaseM Q eFs c s hs

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
