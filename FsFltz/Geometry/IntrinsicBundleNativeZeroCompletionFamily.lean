import FsFltz.Geometry.IntrinsicBundleZeroPairFamily
import FsFltz.Geometry.IntrinsicNativeZeroFamilyEndpointIdentification
import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints

/-!
# Original zero-ribbon bundle data retain their native completed family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–199, `def:maslov`, lines 212–240, and `sec:lean`,
lines 788–814 and 825–830.
One compatible chart for each original bundle supplies the ambient primitive,
full zero-dimensional ribbon and positive witness. The native laws are derived
from the original atlas data. One invocation of the stronger native producer
retains its actual pair deformation, its ribbon completion and total comparison,
its ambient completion quotient family, strict slice maps and real coefficient
extensions. Original endpoint maps and supplied inclusion markings transport
through those same comparisons.
On the once-chosen ambient completion, every compatible nonvanishing original
total-family section with the source's smooth extension laws constructs the
slice Maslov representatives and a grading of this same pair deformation.
The complex-field and full tensor restrictions use its retained actual map.

The arbitrary zero-dimensional primitive is retained, including empty ribbons.
No collar or represented family is an input. Target-specific full-fiber markings,
chain existence and prescribed ambient grading remain separate obligations.
A section preselected on an independently presented original completed bundle
also needs a separate transport result.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing
open FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]

set_option maxHeartbeats 800000 in
/-- Original bundle data construct one native completed rank-one pair family.
The native ribbon total comparison, ambient quotient atlas and strict slice
comparisons are retained with the original chart identities; all conditional
endpoint identifications, marking constructions and original-section gradings
refer to that same family. No endpoint representatives are input. -/
theorem exists_zero_pairDeformation_with_native_completionFamily_of_original_bundle_data
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
    ∃ eMs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
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
        ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val) ∧
      (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
      (∀ t,
      let P := Q.pair t;
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eMs t x).val = eBs t (j t x)) ∧
        (∀ x, P.witness (eBs t x) = b t x) ∧
        P.embeddedCore = (eBs t) '' range (j t) ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = α t x) ∧
        (sourceManifold M).pullback P.ribbonDomain.domain.extension
          (fun x => (eMs t x).val) P.ribbonDomain.liouville.primitive = μ t ∧
        (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (α t) ∧
        IntrinsicLiouville.HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val)) ∧
    (∃ ribbonSlices : PairDeformation.NativeZeroRibbonCompletionSlices Q μ eMs,
      ∃ ribbonTotal : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
          (ℝ × M) (ℝ × Q.source.ribbonCompletion.ambient.manifold.Point) ∞,
        (∀ z, (ribbonTotal z).1 = z.1) ∧ (∀ z, (ribbonTotal.symm z).1 = z.1) ∧
        (∀ (t : Parameter) x, ribbonTotal (t.val, x) =
          (t.val, (Q.ribbonCompletionPresentation t).equiv.symm (ribbonSlices.comparison t x))) ∧
        (∀ (t : Parameter) y, ribbonTotal.symm (t.val, y) =
          (t.val, (ribbonSlices.comparison t).symm ((Q.ribbonCompletionPresentation t).equiv y))) ∧
        (∀ (t : Parameter) (Z : CompleteLiouvilleManifold 0)
          (i : M → Z.manifold.Point) (qmark : (sourceManifold M).SmoothEquiv Z.manifold),
          (sourceManifold M).pullback Z.manifold qmark Z.primitive = μ t →
          (∀ x, qmark x = i x) →
          ∃ m : InclusionMarking (Q.pair t).ribbonCompletion Z
              (fun y => i ((eMs t).symm y)),
            m.equiv = (ribbonSlices.comparison t).symm.trans qmark ∧
            (ribbonSlices.comparison t).trans m.equiv = qmark ∧
            (∀ x, m.equiv ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val) = i x))) ∧
    ∃ (δ : ℝ) (hδ : 0 < δ)
      (C : Parameter → ℝ × IntrinsicBoundary.Point 1 A → A)
      (hemb : ∀ t, IsOpenEmbedding
        (fun p : Half δ (IntrinsicBoundary.Point 1 A) => C t p.val))
      (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 1)) (𝓡∂ (1 + 1)) ∞
        (C t) (Half δ (IntrinsicBoundary.Point 1 A)))
      (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point 1 A)),
        (𝓡∂ (1 + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
      (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point 1 A) →
        ∃ g : A → ℝ × IntrinsicBoundary.Point 1 A,
          ContMDiffAt (𝓡∂ (1 + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 1)) ∞ g (C t p) ∧
            ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point 1 A)] p, g (C t q) = q)
      (hzero : ∀ t (b : IntrinsicBoundary.Point 1 A), C t (0, b) = b.val)
      (hjoint : IsOpenEmbedding (totalCollar
        (fun t (p : Half δ (IntrinsicBoundary.Point 1 A)) => C t p.val))),
    ∃ hmixed : HasRealMixedGerms (δ := δ) C,
      let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
        (hboundary t) (hinv t) (hzero t)
      let P := bandManifold δ (IntrinsicBoundary.smoothManifold 1 A)
      let c := fun t (p : Half δ (IntrinsicBoundary.Point 1 A)) => C t p.val
      letI := bandChartedSpace (k := 1) (B := IntrinsicBoundary.Point 1 A) δ
      letI := totalFamilyChartedSpace hδ C hzero hjoint
      letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmixed
      IsManifold (familyModel (1 + 1)) ∞ (TotalSpace c) ∧
        T2Space (TotalSpace c) ∧ SecondCountableTopology (TotalSpace c) ∧
        ContMDiff (familyModel (1 + 1)) (familyModel (1 + 1)) ∞ (totalInterior c) ∧
        ContMDiff (familyModel (1 + 1)) (familyModel (1 + 1)) ∞ (totalCylinder c) ∧
        ContMDiff (familyModel (1 + 1)) (𝓡∂ 1) ∞ (parameter c) ∧
        (∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
          (fun x => -IntrinsicLiouville.liouvilleVector (α t)
            (IntrinsicLiouville.exteriorDerivative (α t)) x) (Ico 0 δ)) ∧
        ∃ Λ : ∀ t, (X t).Form 1,
          (∀ t, (X t).IsSmoothForm (Λ t)) ∧
          (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            (fun x => (Λ t (original (c t) x)).compContinuousLinearMap
              (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, Model (1 + 1)) (original (c t)) x)) = α t) ∧
          (∀ t, P.pullback (X t) (cylinder (c t)) (Λ t) = cylinderPrimitive δ (α t)) ∧
          (∀ t x, (X t).Nondegenerate ((X t).exteriorDerivative (Λ t)) x) ∧
          (∀ t, Nonempty (CompleteLiouvilleFlow (X t) ((X t).liouvilleVector (Λ t)))) ∧
          P.IsSmoothIntervalFormFamily (fun t => P.pullback (X t) (cylinder (c t)) (Λ t)) ∧
        ∃ q : TotalSpace c → (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point,
          Continuous q ∧
          ContMDiff (familyModel 2) 𝓘(ℝ, Model 2) ∞ q ∧
          Function.Bijective (Q.ambientNativeTotalComparison C q) ∧
          (∀ t x, q (original (totalCollar c) (t, x)) = Q.ambientNativeReferenceMap eAs t x) ∧
          (∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point 1 A)),
            q (totalCylinder c (t, p)) =
              (Q.ambientCompletionPresentation t).prescribedEndMap
                (eBs parameterZero p.val.2, -p.val.1)) ∧
          ∃ F : Diffeomorph (familyModel (2)) (familyModel (2))
              (TotalSpace c) (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) ∞,
            (∀ z, F z = (parameter c z, q z)) ∧
          ∃ S : ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
              Diffeomorph 𝓘(ℝ, Model (2)) 𝓘(ℝ, Model (2))
                (X t).Point (Q.pair t).ambientCompletion.ambient.manifold.Point ∞,
            (∀ t x, S t x = (Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x))) ∧
            (∀ t x, S t (original (c t) x) =
              (Q.pair t).ambientCompletion.inclusion.map (eAs t x).val) ∧
            (∀ t (p : Band δ (IntrinsicBoundary.Point 1 A)),
              S t (cylinder (c t) p) =
                (Q.pair t).ambientCompletion.endMap (eBs t p.val.2, -p.val.1)) ∧
            (∀ t, (X t).pullback (Q.pair t).ambientCompletion.ambient.manifold (S t)
              (Q.pair t).ambientCompletion.ambient.primitive = Λ t) ∧
          (∀ (Jnative : ∀ s : Parameter, (X s).Point → Model 2 →L[ℝ] Model 2)
              (PI : Model 2 ≃L[ℝ] Model 2)
              (_PE : Model 2 ≃L[ℝ] (Model 1 × ℝ))
              (σ : OriginalNativeCanonicalSection (n := 1) C Jnative PI),
            (∀ s, IsCompatibleAlmostComplex (X s) ((X s).exteriorDerivative (Λ s)) (Jnative s)) →
            HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero Jnative →
            HasOriginalEndComplexExtensions hδ C hemb hboundary hzero Jnative →
            HasOriginalTotalLocalSectionExtensions (n := 1) hδ C hemb hboundary hzero Jnative PI σ →
            (∀ s x, σ s x ≠ 0) →
            ∃ endpoints : ∀ s, (Q.pair s).Maslov,
              (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
                ∀ x v, mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) (S s) x
                  (Jnative s x v) = (endpoints s).J (S s x)
                    (mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) (S s) x v)) ∧
              (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
                ∀ x, originalNativeSectionTensor (n := 1) C Jnative PI σ s x =
                  ((endpoints s).tensor (S s x)).compContinuousLinearMap
                    (fun _ => mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) (S s) x)) ∧
              ∃ g : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
                ∃ lift : NativeGradedComparisonStep (.deformation Q)
                    (endpoints parameterZero) (endpoints parameterOne),
                  lift = .deformation g ∧
                  (∀ s, g.family.J s.val = pullbackAlmostComplex Q.source.ambientManifold
                    (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv
                      (endpoints s).J) ∧
                  ∀ s, g.family.tensor s.val = pullbackSquaredTensor Q.source.ambientManifold
                    (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv
                      (endpoints s).tensor) ∧
          (∀ (t u : Parameter) (Ψ : (X t).SmoothEquiv (X u)),
            (X t).pullback (X u) Ψ (Λ u) = Λ t →
            ∀ (ψ : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
                (IntrinsicBoundary.smoothManifold 1 A))
              (shift : IntrinsicBoundary.Point 1 A → ℝ),
              ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ shift →
              (∀ x, ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r →
                ∀ (hr : 0 ≤ r) (hr' : 0 ≤ r + shift x),
                  Ψ (endIn hδ (c t) ⟨(r, x), hr, mem_univ _⟩) =
                    endIn hδ (c u) ⟨(r + shift x, ψ x), hr', mem_univ _⟩) →
              ∀ (h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞)
                (scale : ℝ), 0 < scale →
                (∀ x, ψ (j t x) = j u (h x)) →
                ∃ I : CompletionIdentification (Q.pair t) (Q.pair u),
                  I.ambientEquiv = ((S t).symm.trans Ψ).trans (S u) ∧
                  I.scale = scale ∧
                  I.boundaryEquiv = ((eBs t).symm.trans ψ).trans (eBs u) ∧
                  I.shift = shift ∘ (eBs t).symm ∧
                  (∀ x, I.ribbonEquiv.map (eMs t x).val = (eMs u (h x)).val) ∧
                  (∀ y, I.ribbonEquiv.inverse (eMs u y).val = (eMs t (h.symm y)).val)) ∧
          (∀ (t : Parameter) (Z : CompleteLiouvilleManifold 2)
            (i : A → Z.manifold.Point) (qmark : (X t).SmoothEquiv Z.manifold),
            (X t).pullback Z.manifold qmark Z.primitive = Λ t →
            (∀ x, qmark (original (c t) x) = i x) →
            ∃ m : InclusionMarking (Q.pair t).ambientCompletion Z
                (fun y => i ((eAs t).symm y)),
              m.equiv = (S t).symm.trans qmark ∧ (S t).trans m.equiv = qmark ∧
              (∀ x, m.equiv ((Q.pair t).ambientCompletion.inclusion.map (eAs t x).val) = i x) ∧
              (∀ x r, m.equiv ((Q.pair t).ambientCompletion.endMap (x, r)) =
                Z.completeFlow.flow r (i ((eAs t).symm
                  ⟨(Q.pair t).ambientDomain.domain.boundaryInclusion.map x,
                    (Q.pair t).ambientDomain.domain.boundaryInclusion_mem_carrier x⟩)))) ∧
          (∀ t, (X t).pullback Q.source.ambientCompletion.ambient.manifold
            (q ∘ sliceIn c t) (Q.completedPrimitive t) = Λ t) ∧
          (∃ Ξ : (z : TotalSpace c) → TangentSpace (familyModel (2)) z [⋀^Fin 2]→L[ℝ] ℝ,
            ContMDiff ((familyModel (2)).prod
              𝓘(ℝ, (Model 1 × Model (2)) × (Model 1 × Model (2)))) 𝓘(ℝ, ℝ) ∞
              (fun v : TangentPairBundle (familyModel (2)) (X := TotalSpace c) =>
                Ξ v.proj ![v.2.1, v.2.2]) ∧
            (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
              ∀ x, (Ξ (sliceIn c t x)).compContinuousLinearMap
                (mfderiv 𝓘(ℝ, Model (2)) (familyModel (2)) (sliceIn c t) x) =
                  (X t).exteriorDerivative (Λ t) x) ∧
            (IntrinsicInterior.smoothManifold 1 A).HasRealIntervalTwoFormCoefficientsOn
              (fun p => (Ξ (totalInterior c p)).compContinuousLinearMap
                (mfderiv (familyModel (2)) (familyModel (2)) (totalInterior c) p)) univ ∧
            ∃ cutoff : ℝ, cutoff < 0 ∧ P.HasRealIntervalTwoFormCoefficientsOn
              (fun p => (Ξ (totalCylinder c p)).compContinuousLinearMap
                (mfderiv (familyModel (2)) (familyModel (2)) (totalCylinder c) p))
              {p | cutoff < -p.val.1} ∧
              ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
                ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
          (∃ Ω : (z : TotalSpace c) → TangentSpace (familyModel (2)) z [⋀^Fin 1]→L[ℝ] ℝ,
            ContMDiff (familyModel (2)).tangent 𝓘(ℝ, ℝ) ∞
              (fun v : TangentBundle (familyModel (2)) (TotalSpace c) =>
                Ω v.proj (fun _ => v.2)) ∧
            (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
              ∀ x, (Ω (sliceIn c t x)).compContinuousLinearMap
                (mfderiv 𝓘(ℝ, Model (2)) (familyModel (2)) (sliceIn c t) x) = Λ t x) ∧
            HasRealOpenCovectorCoefficients (familyModel (2)) Ω ∧
            (IntrinsicInterior.smoothManifold 1 A).HasRealIntervalCovectorCoefficientsOn
              (fun p => (Ω (totalInterior c p)).compContinuousLinearMap
                (mfderiv (familyModel (2)) (familyModel (2)) (totalInterior c) p)) univ ∧
            ∃ cutoff : ℝ, cutoff < 0 ∧ P.HasRealIntervalCovectorCoefficientsOn
              (fun p => (Ω (totalCylinder c p)).compContinuousLinearMap
                (mfderiv (familyModel (2)) (familyModel (2)) (totalCylinder c) p))
              {p | cutoff < -p.val.1} ∧
              ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
                ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
          (∃ V : (z : TotalSpace c) → TangentSpace (familyModel (2)) z,
            ContMDiff (familyModel (2)) (familyModel (2)).tangent ∞
              (fun z => (⟨z, V z⟩ : TangentBundle (familyModel (2)) (TotalSpace c))) ∧
            (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
              ∀ x, mfderiv 𝓘(ℝ, Model (2)) (familyModel (2)) (sliceIn c t) x
                ((X t).liouvilleVector (Λ t) x) = V (sliceIn c t x)) ∧
            HasRealFieldCoefficientsInPatch (IntrinsicInterior.smoothManifold 1 A)
              V (totalInterior c) ∧
            ∃ cutoff : ℝ, cutoff < 0 ∧
              HasRealFieldCoefficientsInPatch
                (P.restrict (fieldCylinderStrip δ (IntrinsicBoundary.smoothManifold 1 A) cutoff))
                V (fun p => totalCylinder c (p.1, p.2.val)) ∧
              ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
                ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
          ∀ t x, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            mfderiv 𝓘(ℝ, Model (2)) 𝓘(ℝ, Model (2))
              ((Q.ambientCompletionPresentation t).equiv ∘ (q ∘ sliceIn c t)) x
              ((X t).liouvilleVector (Λ t) x) =
                (Q.pair t).ambientCompletion.ambient.field
                  ((Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x))) := by
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
    obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hpair,
        hribbonCompletion, δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
        hman, hT2, hcount, hInterior, hCylinder, hparameter, hode,
        Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnondegenerate, hΛcomplete, hΛend,
        q, hqcontinuous, hqsmooth, hqbijective, hqnative, hqend, F, hF,
        S, hS, hScompact, hSend, hSprimitive, htail⟩ :=
      exists_native_zero_pairDeformation_with_native_endpoint_identifications_and_markings
      (PA.formInTrivialization eA) hα
      (fun t x => LA.nondegenerate_in_compatible_chart eA heA t (by simp [hA]) x)
      (fun t x => LA.outward_in_compatible_chart eA heA t (by simp [hA]) x)
      μ (PJ.mapInTrivializations eM eA heA) hj hjs'
      (PW.witnessInTrivialization eA heA) hb (PW.witnessInTrivialization_positive eA heA)
    let α := PA.formInTrivialization eA
    have hpA (t : Parameter) := (hpair t).2.2.2.2.1
    have hcA (t : Parameter) := (hpair t).2.2.2.2.2.2.2
    have hbA (t : Parameter) := (hpair t).1
    have hbpA (t : Parameter) := (hpair t).2.2.2.2.2.2.1
    have hSeq (s : Parameter) : S s = Q.ambientNativeSliceCompletionDiffeomorph
        rfl α eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
        hjoint hmixed hode q hqnative hqend s := by
      let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      exact Diffeomorph.ext (hS s)
    refine ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hpair,
      hribbonCompletion, δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
      hman, hT2, hcount, hInterior, hCylinder, hparameter, hode,
      Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnondegenerate, hΛcomplete, hΛend,
      q, hqcontinuous, hqsmooth, hqbijective, hqnative, hqend, F, hF,
      S, hS, hScompact, hSend, hSprimitive, ?_, htail⟩
    intro Jnative PI PE σ hnative hJI hJE hσ hnσ
    obtain ⟨endpoints, hJnative, hTnative, hJrep, hTrep, g, lift, hLift, hgJ, hgT⟩ :=
      Q.exists_nativeGradedDeformation_with_endpoints_of_originalTotalSection
        rfl α eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
        hjoint hmixed hode q hqnative hqend Jnative PI PE σ
        hbpA Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder hΛsmooth hnative hJI hJE hσ hnσ
    refine ⟨endpoints, ?_, ?_, g, lift, hLift, ?_, ?_⟩
    · intro s
      let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      have hsfun : (fun x => S s x) = (fun x => Q.ambientNativeSliceCompletionDiffeomorph
          rfl α eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
          hjoint hmixed hode q hqnative hqend s x) := congrArg (fun f => fun x => f x) (hSeq s)
      have hpred := congrArg (fun f => ∀ x v,
        mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) f x (Jnative s x v) =
          (endpoints s).J (f x)
            (mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) f x v)) hsfun
      exact hpred.mpr (hJnative s)
    · intro s
      let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      have hsfun : (fun x => S s x) = (fun x => Q.ambientNativeSliceCompletionDiffeomorph
          rfl α eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
          hjoint hmixed hode q hqnative hqend s x) := congrArg (fun f => fun x => f x) (hSeq s)
      have hpred := congrArg (fun f => ∀ x, originalNativeSectionTensor (n := 1) C Jnative PI σ s x =
        ((endpoints s).tensor (f x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model 2) 𝓘(ℝ, Model 2) f x)) hsfun
      exact hpred.mpr (hTnative s)
    · intro s
      exact (hgJ s).trans (hJrep s)
    · intro s
      exact (funext (hgT s)).trans (hTrep s)

end FsFltz.Geometry.IntrinsicSmoothBundle
