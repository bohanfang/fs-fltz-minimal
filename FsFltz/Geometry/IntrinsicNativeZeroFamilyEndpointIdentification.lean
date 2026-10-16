import FsFltz.Geometry.IntrinsicNativeCompletedFamilyConstruction
import FsFltz.Geometry.IntrinsicCompletionBoundaryConjugation
import FsFltz.Geometry.NativeSliceInclusionMarking
import FsFltz.Geometry.NativeRibbonInclusionMarking

/-!
# Original shifted completion steps on one zero-ribbon pair family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–199, and `sec:lean`, lines 788–814 and 825–830.
The native completed-family producer is invoked once. Its exact pair deformation,
compact native maps, original completion atlas, slice comparisons and full total
tensor regularity are retained. On those same selected endpoints, an original
strict ambient map with an eventual shifted outward-end law and the original
whole-ribbon boundary square constructs a permitted completion identification.
The original zero-dimensional ribbon diffeomorphism constructs the compact map
and its inverse; its primitive scale follows from vanishing one-forms.

Only nonnegative native outward radii occur in the supplied end law. Strict
flow transport derives the represented all-real end law and contact relation.
Supplied original ambient and ribbon inclusion markings transport through the
exact same selected slice comparisons, with their original map recovered on the whole native source.
Empty ribbons are allowed. This foundational consumer proves no target-specific
full-fiber marking, comparison-chain existence or grading existence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold IntrinsicCompletionGluing

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- One original completed zero-ribbon family retains all constructor witnesses
and gives endpoint identifications and transported supplied markings on those
very same pairs and slice maps. No ribbon primitive-scale or coordinate-extension
hypothesis is added in dimension zero. -/
theorem exists_native_zero_pairDeformation_with_native_endpoint_identifications_and_markings
    (α : Parameter → IntrinsicLiouville.Form 1 A 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point 1 A),
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (α t)
            (IntrinsicLiouville.exteriorDerivative (α t)) x.val)))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → IntrinsicBoundary.Point 1 A)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : IsLocallyExtendibleRibbonMapFamily (IntrinsicBoundary.smoothManifold 1 A) j)
    (b : Parameter → IntrinsicBoundary.Point 1 A → ℝ)
    (hb : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x) :
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
  obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB,
    hQ, hRibbon, δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
    hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily,
    q, hq, hqsmooth, hqbij, hqnative, hqend, F, hF, S, hS, hSnative,
    hScylinder, hSprimitive, htransport, hΞ, hΩ, hV, hfield⟩ :=
    exists_native_zero_pairDeformation_with_native_completionFamily
      α hα hnd hout μ j hj hjs b hb hpositive
  obtain ⟨ribbonSlices, ribbonTotal, hRTparameter, hRTinverseParameter,
    hRTnative, hRTinverse⟩ := hRibbon
  let c := fun t (p : Half δ (IntrinsicBoundary.Point 1 A)) => C t p.val
  let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)
  refine ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB,
    hQ, ?_, δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
    hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily,
    q, hq, hqsmooth, hqbij, hqnative, hqend, F, hF, S, hS, hSnative,
    hScylinder, hSprimitive, ?_, ?_, htransport, hΞ, hΩ, hV, hfield⟩
  · refine ⟨ribbonSlices, ribbonTotal, hRTparameter, hRTinverseParameter,
      hRTnative, hRTinverse, ?_⟩
    intro t Z i qmark _ hqcompact
    obtain ⟨m, hm, hrecover, hnative, _⟩ :=
      ribbonSlices.exists_originalMarking_on_same_ribbonCompletion t Z i qmark hqcompact
    exact ⟨m, hm, hrecover, hnative⟩
  · intro t u Ψ hΨ ψ shift hshift hendΨ h scale hscalePos hsquare
    have hjt := (hQ t).2.1
    have hju := (hQ u).2.1
    obtain ⟨g, hgnative, hginverse, hgscale⟩ :=
      exists_originalNativeCompactDiffeomorph
        (Q.pair t).ribbonDomain (Q.pair u).ribbonDomain
        (Q.pair t).ribbonCompletion (Q.pair u).ribbonCompletion
        (eMs t) (eMs u) h scale
    -- The generic adapter takes total end functions. Every radius used by
    -- its eventual law is nonnegative and has the actual original cylinder value.
    let Et : IntrinsicBoundary.Point 1 A × ℝ → (X t).Point := fun p =>
      endIn hδ (c t) ⟨(max p.2 0, p.1),
        (show (0 : ℝ) ≤ max p.2 0 from le_max_right p.2 0), mem_univ _⟩
    let Eu : IntrinsicBoundary.Point 1 A × ℝ → (X u).Point := fun p =>
      endIn hδ (c u) ⟨(max p.2 0, p.1),
        (show (0 : ℝ) ≤ max p.2 0 from le_max_right p.2 0), mem_univ _⟩
    have het (x : IntrinsicBoundary.Point 1 A) (r : ℝ) (hr : 0 ≤ r) :
        S t (Et (x, r)) = (Q.pair t).ambientCompletion.endMap (eBs t x, r) := by
      simpa only [Et, endIn, endToBand, max_eq_left hr, neg_neg] using
        hScylinder t (endToBand hδ ⟨(r, x), hr, mem_univ _⟩)
    have heu (x : IntrinsicBoundary.Point 1 A) (r : ℝ) (hr : 0 ≤ r) :
        S u (Eu (x, r)) = (Q.pair u).ambientCompletion.endMap (eBs u x, r) := by
      simpa only [Eu, endIn, endToBand, max_eq_left hr, neg_neg] using
        hScylinder u (endToBand hδ ⟨(r, x), hr, mem_univ _⟩)
    have heΨ : ∀ x, ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r →
        Ψ (Et (x, r)) = Eu (ψ x, r + shift x) := by
      intro x
      obtain ⟨r₀, hr₀⟩ := hendΨ x
      refine ⟨max r₀ (max 0 (-shift x)), ?_⟩
      intro r hr
      have hrr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
      have hr0 : 0 ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
      have hrs : 0 ≤ r + shift x := by
        have hs := (le_max_right 0 (-shift x)).trans ((le_max_right _ _).trans hr)
        linarith
      simpa only [Et, Eu, max_eq_left hr0, max_eq_left hrs] using hr₀ r hrr₀ hr0 hrs
    obtain ⟨I, hIambient, hIg, hIscale, hIboundary, hIshift⟩ :=
      CompletionIdentification.exists_of_nativeBoundaryConjugation
        (Q.pair t) (Q.pair u) (X t) (X u)
        (IntrinsicBoundary.smoothManifold 1 A) (IntrinsicBoundary.smoothManifold 1 A)
        (Λ t) (Λ u) (S t) (S u) (hSprimitive t) (hSprimitive u) Ψ hΨ
        Et Eu (eBs t) (eBs u) het heu ψ shift hshift heΨ
        (eMs t) (eMs u) (eMs t).surjective h (j t) (j u)
        hjt hju hsquare g hgnative scale hscalePos hgscale
    exact ⟨I, hIambient, hIscale, hIboundary, hIshift,
      by simpa only [hIg] using hgnative, by simpa only [hIg] using hginverse⟩
  · intro t Z i qmark hqmark hqcompact
    let m := (Q.pair t).ambientCompletion.inclusionMarkingOfNativeSliceEquiv
      (X t) (Λ t) (S t) (hSprimitive t) (eAs t).toEquiv
      (original (c t)) (hSnative t) Z i qmark hqmark hqcompact
    exact ⟨m, rfl,
      (Q.pair t).ambientCompletion.inclusionMarkingOfNativeSliceEquiv_recovers_original
        (X t) (Λ t) (S t) (hSprimitive t) (eAs t).toEquiv
        (original (c t)) (hSnative t) Z i qmark hqmark hqcompact,
      (Q.pair t).ambientCompletion.inclusionMarkingOfNativeSliceEquiv_native
        (X t) (Λ t) (S t) (hSprimitive t) (eAs t).toEquiv
        (original (c t)) (hSnative t) Z i qmark hqmark hqcompact,
      (Q.pair t).ambientCompletion.inclusionMarkingOfNativeSliceEquiv_end
        (X t) (Λ t) (S t) (hSprimitive t) (eAs t).toEquiv
        (original (c t)) (hSnative t) Z i qmark hqmark hqcompact⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
