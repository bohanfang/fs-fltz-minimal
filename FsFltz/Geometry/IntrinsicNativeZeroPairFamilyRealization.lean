import FsFltz.Geometry.IntrinsicNativeZeroPairFamilyChain

/-!
# Original zero-ribbon realizations retaining completion data

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 127–160;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814 and 825–830.
A rank-one original family constructs one completed realization. Its output
retains the full original ambient total atlas, regularity and supplied-marking
capabilities, and the all-real zero-ribbon total comparison and supplied
ribbon-marking capability, on that same choice. This is output packaging
of the existing strong producer, not existence of the toric comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open IntrinsicCompletionGluing SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- Original rank-one family values and their defining properties. No
completed family, completion map, marking, chain or grading is input. -/
structure OriginalNativeZeroPairFamily where
  lam : Parameter → IntrinsicLiouville.Form 1 A 1
  hlam : IntrinsicLiouville.IsLocallyExtendibleFormFamily lam
  hnd : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (lam t)) x
  hout : ∀ t (x : IntrinsicBoundary.Point 1 A),
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (lam t)
            (IntrinsicLiouville.exteriorDerivative (lam t)) x.val))
  μ : Parameter → (sourceManifold M).Form 1
  j : Parameter → M → IntrinsicBoundary.Point 1 A
  hj : ∀ t, Function.Injective (j t)
  hjs : IsLocallyExtendibleRibbonMapFamily (IntrinsicBoundary.smoothManifold 1 A) j
  b : Parameter → IntrinsicBoundary.Point 1 A → ℝ
  hb : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily b
  hpositive : ∀ t x, 0 < b t x

/-- The full transparent completion and supplied-marking correspondence
of the existing strong zero-ribbon family producer, retained on its exact
chosen deformation and maps. -/
def NativeZeroPairFamilyCompletionData
    (D : OriginalNativeZeroPairFamily (A := A) (M := M))
    (Q : PairDeformation 1)
    (L : NativeZeroPairFamilyPresentation D.lam D.μ D.j D.b Q) : Prop :=
  let lam := D.lam
  let μ := D.μ
  let j := D.j
  let eAs := L.ambientEquiv
  let eMs := L.ribbonEquiv
  let eBs := L.boundaryEquiv
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
        (fun x => -IntrinsicLiouville.liouvilleVector (lam t)
          (IntrinsicLiouville.exteriorDerivative (lam t)) x) (Ico 0 δ)) ∧
      ∃ Λ : ∀ t, (X t).Form 1,
        (∀ t, (X t).IsSmoothForm (Λ t)) ∧
        (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
          (fun x => (Λ t (original (c t) x)).compContinuousLinearMap
            (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, Model (1 + 1)) (original (c t)) x)) = lam t) ∧
        (∀ t, P.pullback (X t) (cylinder (c t)) (Λ t) = cylinderPrimitive δ (lam t)) ∧
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
                ((Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x)))

/-- The same realized zero-ribbon family retains its compact maps and
entire original completed-family and supplied-marking correspondence. -/
structure OriginalNativeZeroPairFamilyRealization
    (D : OriginalNativeZeroPairFamily (A := A) (M := M)) where
  deformation : PairDeformation 1
  presentation : NativeZeroPairFamilyPresentation D.lam D.μ D.j D.b deformation
  completed : NativeZeroPairFamilyCompletionData D deformation presentation

/-- Preserve the full output of the original zero-ribbon family producer
without selecting another family or losing any original marking capability. -/
theorem OriginalNativeZeroPairFamily.exists_realization
    (D : OriginalNativeZeroPairFamily (A := A) (M := M)) :
    Nonempty (OriginalNativeZeroPairFamilyRealization D) := by
  obtain ⟨Q, eA, eM, eB, RA, RM, hRA, hRM, hA, hM, hB, hQ, hRibbon, hAmbient⟩ :=
    exists_native_zero_pairDeformation_with_native_endpoint_identifications_and_markings
      D.lam D.hlam D.hnd D.hout D.μ D.j D.hj D.hjs D.b D.hb D.hpositive
  let L : NativeZeroPairFamilyPresentation D.lam D.μ D.j D.b Q := {
    ambientEquiv := eA, ribbonEquiv := eM, boundaryEquiv := eB
    ambientTransport := RA, ribbonTransport := RM
    ambientTransport_smooth := hRA, ribbonTransport_smooth := hRM
    ambient_square := hA, ribbon_square := hM, boundary_square := hB
    presentation := fun t => by
      obtain ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩ := hQ t
      exact ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩
    ribbon_slices := ⟨hRibbon.choose⟩ }
  exact ⟨⟨Q, L, ⟨hRibbon, hAmbient⟩⟩⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
