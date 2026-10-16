import FsFltz.Geometry.IntrinsicBundlePairFamily
import FsFltz.Geometry.IntrinsicNativeZeroPairFamily

/-!
# Original bundle data produce the zero-dimensional ribbon pair family

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 825–830.
The same constructed ambient and ribbon charts carry the original primitive,
actual ribbon map and positive witness. Original local Liouville laws imply
the transported laws. The conclusion includes the actual completed family,
its native markings, their joint coherence, and the entire embedded core.
The arbitrary native zero-dimensional primitive is retained; its regularity
is automatic by `IntrinsicZeroLiouville.positiveForm_eq_zero`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]

/-- Original compact bundle atlases, primitives and geometric laws construct
an actual rank-one completed pair deformation. All parameters, including
both endpoints, retain the entire original zero-dimensional ribbon image. -/
theorem exists_zero_pairDeformation_of_original_bundle_data
    (PA : BundlePrimitiveData (k := 1) (M := A) EA)
    (LA : OriginalBundleLiouvilleLaws PA)
    (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ.map cM cA t))
    (PW : BundleWitnessData (k := 1) (M := A) EA)
    (μ : Parameter → (sourceManifold M).Form 1) :
    ∃ eM : Trivialization M (π M EM),
    ∃ eA : Trivialization A (π A EA), eM.baseSet = univ ∧ eA.baseSet = univ ∧
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
      ∀ t,
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
          P.ambientDomain.domain.extension (fun x => (eAs t x).val) := by
  obtain ⟨eM, eA, hM, hA, heM, heA, hjs⟩ := PJ.exists_global_charts
  refine ⟨eM, eA, hM, hA, heM, heA, ?_, ?_, ?_, ?_⟩
  · intro c hc t ht
    exact PA.formInTrivialization_eq_pullback eA heA c hc ⟨by simp [hA], ht⟩
  · intro cM hcM cA hcA t ht x
    exact PJ.mapInTrivializations_eq_local_val eM eA heA cM hcM cA hcA
      ⟨⟨by simp [hM], ht.1⟩, ⟨by simp [hA], ht.2⟩⟩ x
  · intro c hc t ht x
    exact PW.witnessInTrivialization_eq eA heA c hc ⟨by simp [hA], ht⟩ x
  · have hα : IsLocallyExtendibleFormFamily (PA.formInTrivialization eA) :=
      hasSmoothFormFamilyOn_univ_iff.mp (by
        simpa only [hA] using PA.smooth_in_compatible_chart eA heA)
    have hj : ∀ t, Function.Injective (PJ.mapInTrivializations eM eA heA t) := by
      intro t
      let cM := trivializationAt M EM t
      let cA := trivializationAt A EA t
      have hcM : cM ∈ trivializationAtlas M EM := trivialization_mem_atlas _ _ _
      have hcA : cA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
      have htM : t ∈ cM.baseSet := mem_baseSet_trivializationAt _ _ _
      have htA : t ∈ cA.baseSet := mem_baseSet_trivializationAt _ _ _
      exact PJ.injective_mapInTrivializations eM eA heA cM hcM cA hcA
        ⟨⟨by simp [hM], htM⟩, ⟨by simp [hA], htA⟩⟩
        (hPJ ⟨cM, hcM⟩ ⟨cA, hcA⟩ t ⟨htM, htA⟩)
    have hjs' : IsLocallyExtendibleRibbonMapFamily
        (IntrinsicBoundary.smoothManifold 1 A) (PJ.mapInTrivializations eM eA heA) :=
      HasSmoothTargetFamilyOn.native_zero_map (IntrinsicBoundary.smoothManifold 1 A)
        (by simpa only [hM, hA, inter_self] using hjs)
    have hb : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily
        (PW.witnessInTrivialization eA heA) :=
      HasSmoothValueFamilyOn.native_scalar (IntrinsicBoundary.smoothManifold 1 A)
        (by simpa only [hA] using PW.smooth_in_compatible_chart eA heA)
    exact exists_native_zero_pairDeformation_with_native_coherence_and_coordinates
      (PA.formInTrivialization eA) hα
      (fun t x => LA.nondegenerate_in_compatible_chart eA heA t (by simp [hA]) x)
      (fun t x => LA.outward_in_compatible_chart eA heA t (by simp [hA]) x)
      μ (PJ.mapInTrivializations eM eA heA) hj hjs'
      (PW.witnessInTrivialization eA heA) hb (PW.witnessInTrivialization_positive eA heA)

end FsFltz.Geometry.IntrinsicSmoothBundle
