import FsFltz.Geometry.IntrinsicBundlePrimitiveData
import FsFltz.Geometry.IntrinsicBundleWitnessData
import FsFltz.Geometry.IntrinsicBundleRibbonData
import FsFltz.Geometry.IntrinsicBundleRibbonPrimitive
import FsFltz.Geometry.NativeLiouvillePullback
import FsFltz.Geometry.IntrinsicNativePairFamily

/-!
# Original bundle pair data produce a native completed pair family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–199, and `sec:lean`, lines 788–814.
All inputs live in the original bundle atlases. A single compatible global
chart for each bundle carries the primitives, witness and ribbon map into
the same native model. The native Liouville and ribbon laws are derived
there, rather than supplied as hypotheses after trivialization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

section OriginalLiouvilleLaws

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- The geometric Liouville laws are stated only for original local
primitives and original native points. No transported chart law is input. -/
structure OriginalBundleLiouvilleLaws (P : BundlePrimitiveData (k := k) (M := M) E) where
  nondegenerate : ∀ c t, t ∈ c.val.baseSet → ∀ x,
    Nondegenerate (exteriorDerivative (P.form c t)) x
  outward : ∀ c t, t ∈ c.val.baseSet → ∀ b : IntrinsicBoundary.Point k M,
    ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
      rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
        (liouvilleVector (P.form c t) (exteriorDerivative (P.form c t)) b.val))

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

namespace OriginalBundleLiouvilleLaws

/-- An original chart's primitive, local extension germs and geometric
laws construct its native Liouville presentation. -/
theorem nativePresentation {P : BundlePrimitiveData (k := k) (M := M) E}
    (L : OriginalBundleLiouvilleLaws P)
    (c : {e : Trivialization M (π M E) // e ∈ trivializationAtlas M E})
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    Nonempty (NativeLiouvillePresentation (P.form c t)) :=
  exists_nativeLiouvillePresentation (P.form c t) ((P.smooth c).slice ht)
    (L.nondegenerate c t ht) (L.outward c t ht)

/-- Nondegeneracy in a compatible chart follows from an original local
Liouville primitive and the full differential of the actual chart transition. -/
theorem nondegenerate_in_compatible_chart {P : BundlePrimitiveData (k := k) (M := M) E}
    (L : OriginalBundleLiouvilleLaws P) (e : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (t : Parameter) (ht : t ∈ e.baseSet) (x : M) :
    Nondegenerate (exteriorDerivative (P.formInTrivialization e t)) x := by
  let c := trivializationAt M E t
  have hc : c ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  obtain ⟨Q⟩ := L.nativePresentation ⟨c, hc⟩ t htc
  rw [P.formInTrivialization_eq_pullback e he c hc ⟨ht, htc⟩]
  exact nondegenerate_nativePullbackForm_of_presentation Q (e.coordChange c t)
    ((he c hc).1.contMDiff ⟨ht, htc⟩)
    (fun y => bijective_mfderiv_coordChange_of_compatible e c he
      (compatibleTrivialization_of_mem hc) ⟨ht, htc⟩ y) x

/-- Outwardness, with the complete native defining-function extension
clause, is derived in a compatible chart from the original local law. -/
theorem outward_in_compatible_chart {P : BundlePrimitiveData (k := k) (M := M) E}
    (L : OriginalBundleLiouvilleLaws P) (e : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (t : Parameter) (ht : t ∈ e.baseSet) (b : IntrinsicBoundary.Point k M) :
    ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
      rho b.val = 0 ∧ (∀ᶠ y in 𝓝 b.val, rho y ≤ 0) ∧
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val ≠ 0 ∧
      ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val) ∧
      beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1)) b.val)]
        (rho ∘ ((IntrinsicBoundary.chartAt b).ambient.extend (𝓡∂ (k + 1))).symm) ∧
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho b.val
        (liouvilleVector (P.formInTrivialization e t)
          (exteriorDerivative (P.formInTrivialization e t)) b.val)) := by
  let c := trivializationAt M E t
  have hc : c ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  obtain ⟨Q⟩ := L.nativePresentation ⟨c, hc⟩ t htc
  rw [P.formInTrivialization_eq_pullback e he c hc ⟨ht, htc⟩]
  exact localDefiningFunction_nativePullbackForm_of_presentation Q
    (transitionDiffeomorphOfCompatible e c he (compatibleTrivialization_of_mem hc) ⟨ht, htc⟩) b

end OriginalBundleLiouvilleLaws
end OriginalLiouvilleLaws

section PositivePair

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]

/-- The remaining pair laws are literal original-atlas equations: a full
ribbon embedding and its witnessed primitive. In particular no equation
for a family in a constructed trivialization is a field of this structure. -/
structure OriginalBundlePairLaws
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) EM)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA) where
  embedding : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
    Topology.IsEmbedding (PJ.map cM cA t)
  immersion : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet → ∀ x,
    Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (PJ.map cM cA t) x)
  primitive : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet → ∀ x,
    ((PW.witness cA t (PJ.map cM cA t x) •
      IntrinsicBoundary.restrictForm (PA.form cA t) (PJ.map cM cA t x))).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (PJ.map cM cA t) x) = PM.form cM t x

/-- Original compact bundle pair data produce an actual completed pair
deformation. One chosen chart per bundle is used for all four families;
the full original local forms, ribbon points and witnesses are retained,
as are the native full core, coordinate germs and presentation coherence. -/
theorem exists_pairDeformation_of_original_bundle_data
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) EM)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
    (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
    (LP : OriginalBundlePairLaws PA PM PW PJ) :
    ∃ (cA : Trivialization A (π A EA)) (cM : Trivialization M (π M EM)),
      cA.baseSet = univ ∧ cM.baseSet = univ ∧
      ∃ (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA cA)
        (_heM : CompatibleTrivialization (𝓡∂ (k + 1)) EM cM),
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
        ∀ t : Parameter,
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
        HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => ((eMs t) x).val) := by
  obtain ⟨cM, cA, hbaseM, hbaseA, heM, heA, hj⟩ := PJ.exists_global_charts
  let lam := PA.formInTrivialization cA
  let μ := PM.formInTrivialization cM
  let j := PJ.mapInTrivializations cM cA heA
  let b := PW.witnessInTrivialization cA heA
  have hAt (t : Parameter) : t ∈ cA.baseSet := hbaseA ▸ mem_univ t
  have hMt (t : Parameter) : t ∈ cM.baseSet := hbaseM ▸ mem_univ t
  have hlam : IsLocallyExtendibleFormFamily lam := hasSmoothFormFamilyOn_univ_iff.mp
    (by simpa only [hbaseA] using PA.smooth_in_compatible_chart cA heA)
  have hμ : IsLocallyExtendibleFormFamily μ := hasSmoothFormFamilyOn_univ_iff.mp
    (by simpa only [hbaseM] using PM.smooth_in_compatible_chart cM heM)
  have hjs : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) j :=
    hj.native_map (IntrinsicBoundary.smoothManifold a A)
  have hb : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily b :=
    HasSmoothValueFamilyOn.native_scalar (IntrinsicBoundary.smoothManifold a A)
      (by simpa only [hbaseA] using PW.smooth_in_compatible_chart cA heA)
  have hjinj (t : Parameter) : Function.Injective (j t) := by
    let dM := trivializationAt M EM t
    let dA := trivializationAt A EA t
    have hdM : dM ∈ trivializationAtlas M EM := trivialization_mem_atlas _ _ _
    have hdA : dA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
    have htM : t ∈ dM.baseSet := mem_baseSet_trivializationAt _ _ _
    have htA : t ∈ dA.baseSet := mem_baseSet_trivializationAt _ _ _
    exact (PJ.isEmbedding_mapInTrivializations cM cA heA dM hdM dA hdA
      ⟨⟨hMt t, htM⟩, ⟨hAt t, htA⟩⟩ (LP.embedding ⟨dM, hdM⟩ ⟨dA, hdA⟩ t ⟨htM, htA⟩)).injective
  have hjimm (t : Parameter) (x : M) : Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x) := by
    let dM := trivializationAt M EM t
    let dA := trivializationAt A EA t
    have hdM : dM ∈ trivializationAtlas M EM := trivialization_mem_atlas _ _ _
    have hdA : dA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
    have htM : t ∈ dM.baseSet := mem_baseSet_trivializationAt _ _ _
    have htA : t ∈ dA.baseSet := mem_baseSet_trivializationAt _ _ _
    exact PJ.injective_mfderiv_mapInTrivializations cM heM cA heA dM hdM dA hdA
      ⟨⟨hMt t, htM⟩, ⟨hAt t, htA⟩⟩ (LP.immersion ⟨dM, hdM⟩ ⟨dA, hdA⟩ t ⟨htM, htA⟩) x
  have hribbon (t : Parameter) (x : M) :
      ((b t (j t x) • IntrinsicBoundary.restrictForm (lam t) (j t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x) = μ t x := by
    let dM := trivializationAt M EM t
    let dA := trivializationAt A EA t
    have hdM : dM ∈ trivializationAtlas M EM := trivialization_mem_atlas _ _ _
    have hdA : dA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
    have htM : t ∈ dM.baseSet := mem_baseSet_trivializationAt _ _ _
    have htA : t ∈ dA.baseSet := mem_baseSet_trivializationAt _ _ _
    exact PJ.primitive_eq_in_compatible_charts PA PM PW cM heM cA heA dM hdM dA hdA
      ⟨⟨hMt t, htM⟩, ⟨hAt t, htA⟩⟩ (LP.primitive ⟨dM, hdM⟩ ⟨dA, hdA⟩ t ⟨htM, htA⟩) x
  obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAsquare, hMsquare, hBsquare, hQ⟩ :=
    exists_intrinsic_pairDeformation_with_native_coherence_and_coordinates hdimA hdimM
      lam hlam (fun t => LA.nondegenerate_in_compatible_chart cA heA t (hAt t))
      (fun t => LA.outward_in_compatible_chart cA heA t (hAt t))
      μ hμ (fun t => LM.nondegenerate_in_compatible_chart cM heM t (hMt t))
      (fun t => LM.outward_in_compatible_chart cM heM t (hMt t))
      j hjs hjinj hjimm b hb (PW.witnessInTrivialization_positive cA heA) hribbon
  refine ⟨cA, cM, hbaseA, hbaseM, heA, heM, ?_, ?_, ?_, ?_,
    Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAsquare, hMsquare, hBsquare, hQ⟩
  · intro dA hdA t ht x vs
    exact PA.formInTrivialization_apply cA heA dA hdA ⟨hAt t, ht⟩ x vs
  · intro dM hdM t ht x vs
    exact PM.formInTrivialization_apply cM heM dM hdM ⟨hMt t, ht⟩ x vs
  · intro dA hdA t ht x
    exact PW.witnessInTrivialization_eq cA heA dA hdA ⟨hAt t, ht⟩ x
  · intro dM hdM dA hdA t ht x
    exact PJ.mapInTrivializations_eq_local_val cM cA heA dM hdM dA hdA
      ⟨⟨hMt t, ht.1⟩, ⟨hAt t, ht.2⟩⟩ x

end PositivePair

end FsFltz.Geometry.IntrinsicSmoothBundle
