import FsFltz.Geometry.IntrinsicNativePairFamilyChain
import Mathlib.Data.List.OfFn

/-!
# Original pair-family realizations retaining completion data

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The original compact family contains only its forms, full ribbon embedding,
witness, and defining regularity laws. Its realization is constructed once.
The output keeps the entire native ribbon and ambient completion conjunction
of the stronger family producer, including the original total atlases,
strict slice comparisons, real coefficient extensions and transport of
supplied inclusion markings on that same deformation. This is a fixed-source
foundation, not existence of the toric comparison or its grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville
open IntrinsicCompletionGluing SmoothManifold

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original native family data and its defining properties. No completed
presentation, marking, junction, chain or grading is a field. -/
structure OriginalNativePairFamily where
  lam : Parameter → Form a A 1
  hlam : IsLocallyExtendibleFormFamily lam
  hAnd : ∀ t x, Nondegenerate (exteriorDerivative (lam t)) x
  hAout : ∀ t, ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (lam t) (exteriorDerivative (lam t)) x.val))
  μ : Parameter → Form k M 1
  hμ : IsLocallyExtendibleFormFamily μ
  hMnd : ∀ t x, Nondegenerate (exteriorDerivative (μ t)) x
  hMout : ∀ t, ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μ t) (exteriorDerivative (μ t)) x.val))
  j : Parameter → M → IntrinsicBoundary.Point a A
  hjs : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) j
  hjinj : ∀ t, Function.Injective (j t)
  hjimm : ∀ t x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x)
  b : Parameter → IntrinsicBoundary.Point a A → ℝ
  hb : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily b
  hpositive : ∀ t x, 0 < b t x
  hribbon : ∀ t x,
      ((b t (j t x) • IntrinsicBoundary.restrictForm (lam t) (j t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x) = μ t x

/-- The full completion correspondence proved by the native producer.
This transparent output-only predicate retains its entire ribbon and ambient
conjunction on the exact chosen deformation and native maps. In particular,
unfolding it exposes both original total comparisons and the capabilities
transporting supplied original markings, without selecting another family. -/
def NativePairFamilyCompletionData
    (D : OriginalNativePairFamily (a := a) (k := k) (A := A) (M := M))
    (Q : PairDeformation n)
    (L : NativePairFamilyPresentation D.lam D.μ D.j D.b Q) : Prop :=
  let lam := D.lam
  let μ := D.μ
  let j := D.j
  let eAs := L.ambientEquiv
  let eMs := L.ribbonEquiv
  let eBs := L.boundaryEquiv
  (∃ ribbonSlices : PairDeformation.NativeRibbonCompletionSlices Q μ eMs,
    (∀ (t : Parameter),
      let XR := completionManifold ribbonSlices.width_pos (ribbonSlices.collar t)
        (ribbonSlices.collar_embedding t) (ribbonSlices.collar_smooth t)
        (ribbonSlices.collar_boundary t) (ribbonSlices.collar_inverse t) (ribbonSlices.collar_zero t)
      ∀ (Z : CompleteLiouvilleManifold (2 * n - 2)) (i : M → Z.manifold.Point)
          (qR : XR.SmoothEquiv Z.manifold),
        XR.pullback Z.manifold qR Z.primitive = ribbonSlices.primitive t →
        (∀ x, qR (original (fun p => ribbonSlices.collar t p.val) x) = i x) →
        ∃ m : InclusionMarking (Q.pair t).ribbonCompletion Z
            (fun y => i ((eMs t).symm y)),
          m.equiv = (ribbonSlices.comparison t).symm.trans qR ∧
          (ribbonSlices.comparison t).trans m.equiv = qR ∧
          (∀ x, m.equiv ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val) = i x) ∧
          ∀ (x : IntrinsicBoundary.Point k M) (r : ℝ),
            m.equiv ((Q.pair t).ribbonCompletion.endMap (ribbonSlices.boundary_comparison t x, r)) =
              Z.completeFlow.flow r (i x.val)) ∧
    ∃ ribbonBoundary : ℝ → (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
        Q.source.ribbonDomain.domain.boundary,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, Model ((2 * n - 2) - 1)) ∞
        (fun p : ℝ × IntrinsicBoundary.Point k M => ribbonBoundary p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model ((2 * n - 2) - 1))) 𝓘(ℝ, Model k) ∞
        (fun p : ℝ × Q.source.ribbonDomain.domain.boundary.Point => (ribbonBoundary p.1).symm p.2) ∧
      (∀ (t : Parameter) x, ribbonBoundary t.val x =
        (Q.ribbonPresentation t).boundaryEquiv.symm (ribbonSlices.boundary_comparison t x)) ∧
      (∀ (t : Parameter) y, (ribbonBoundary t.val).symm y =
        (ribbonSlices.boundary_comparison t).symm ((Q.ribbonPresentation t).boundaryEquiv y)) ∧
      (∀ (t : Parameter) (p : Band ribbonSlices.width (IntrinsicBoundary.Point k M)),
        (Q.ribbonCompletionPresentation t).equiv.symm
          (ribbonSlices.comparison t (cylinder (fun p => ribbonSlices.collar t p.val) p)) =
            (Q.ribbonCompletionPresentation t).prescribedEndMap (ribbonBoundary t.val p.val.2, -p.val.1)) ∧
    let c := fun t (p : Half ribbonSlices.width (IntrinsicBoundary.Point k M)) => ribbonSlices.collar t p.val
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) ribbonSlices.width
    letI := totalFamilyChartedSpace ribbonSlices.width_pos ribbonSlices.collar
      ribbonSlices.collar_zero ribbonSlices.collar_joint_embedding
    letI := totalFamily_isManifold ribbonSlices.width_pos ribbonSlices.collar
      ribbonSlices.collar_boundary ribbonSlices.collar_zero
      ribbonSlices.collar_joint_embedding ribbonSlices.mixed_germs
    ∃ ribbonTotal : Diffeomorph (familyModel (k + 1)) (familyModel (2 * n - 2))
        (TotalSpace c) (Parameter × Q.source.ribbonCompletion.ambient.manifold.Point) ∞,
      (∀ z, ribbonTotal z = (parameter c z, ribbonSlices.totalMap z)) ∧
      (∀ z, parameter c (ribbonTotal.symm z) = z.1) ∧
      (∀ t x, ribbonTotal (sliceIn c t x) =
        (t, (Q.ribbonCompletionPresentation t).equiv.symm (ribbonSlices.comparison t x))) ∧
      (∀ t y, ribbonTotal.symm (t, y) = sliceIn c t
        ((ribbonSlices.comparison t).symm ((Q.ribbonCompletionPresentation t).equiv y))) ∧
      (∀ t x, ribbonTotal (original (totalCollar c) (t, x)) =
        (t, (Q.ribbonCompletionPresentation t).equiv.symm
          ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val))) ∧
      (∀ (t : Parameter) (p : Band ribbonSlices.width (IntrinsicBoundary.Point k M)),
        ribbonTotal (totalCylinder c (t, p)) =
          (t, (Q.ribbonCompletionPresentation t).prescribedEndMap
            (ribbonBoundary t.val p.val.2, -p.val.1))) ∧
      (∃ f : ℝ × IntrinsicInterior.Point k M → Q.source.ribbonCompletion.ambient.manifold.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
          𝓘(ℝ, Model (2 * n - 2)) ∞ f ∧
        ∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
          f (t.val, u) = (ribbonTotal (totalInterior c (t, u))).2) ∧
      (∀ (t : Parameter) (u : IntrinsicInterior.Point k M),
        ∃ g : ℝ × Q.source.ribbonCompletion.ambient.manifold.Point → ℝ × IntrinsicInterior.Point k M,
          ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
            ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ g
            (t.val, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val) ∧
          (∀ p, (g p).1 = p.1) ∧
          ∀ᶠ p in 𝓝 (t, Q.source.ribbonCompletion.inclusion.map (eMs parameterZero u.val).val),
            ribbonTotal.symm p = totalInterior c (p.1, (g (p.1.val, p.2)).2)) ∧
      (∃ ribbonΩ : (z : TotalSpace c) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
        ribbonΩ = nativeTotalCovector (familyModel (k + 1))
          Q.source.ribbonCompletion.ambient.manifold (parameter c)
          ribbonSlices.totalMap Q.completedRibbonPrimitive ∧
        ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
          (fun v : TangentBundle (familyModel (k + 1)) (TotalSpace c) =>
            ribbonΩ v.proj (fun _ => v.2)) ∧
        HasRealOpenCovectorCoefficients (familyModel (k + 1)) ribbonΩ ∧
        ∀ t,
          letI := completionChartedSpace ribbonSlices.width_pos (ribbonSlices.collar t)
            (ribbonSlices.collar_embedding t) (ribbonSlices.collar_boundary t) (ribbonSlices.collar_zero t)
          ∀ x, (ribbonΩ (sliceIn c t x)).compContinuousLinearMap
            (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x) =
              ribbonSlices.primitive t x) ∧
      (∃ ribbonΞ : (z : TotalSpace c) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 2]→L[ℝ] ℝ,
        ribbonΞ = nativeTotalTwoForm (familyModel (k + 1))
          Q.source.ribbonCompletion.ambient.manifold (parameter c) ribbonSlices.totalMap
          (fun t => Q.source.ribbonCompletion.ambient.manifold.exteriorDerivative
            (Q.completedRibbonPrimitive t)) ∧
        ContMDiff ((familyModel (k + 1)).prod
            𝓘(ℝ, (Model 1 × Model (k + 1)) × (Model 1 × Model (k + 1)))) 𝓘(ℝ, ℝ) ∞
          (fun v : TangentPairBundle (familyModel (k + 1)) (X := TotalSpace c) =>
            ribbonΞ v.proj ![v.2.1, v.2.2]) ∧
        (IntrinsicInterior.smoothManifold k M).HasRealIntervalTwoFormCoefficientsOn
          (fun p => (ribbonΞ (totalInterior c p)).compContinuousLinearMap
            (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ ∧
        (∃ cutoff : ℝ, cutoff < 0 ∧
          (bandManifold ribbonSlices.width (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalTwoFormCoefficientsOn
            (fun p => (ribbonΞ (totalCylinder c p)).compContinuousLinearMap
              (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
            {p | cutoff < -p.val.1} ∧
          ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
            ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
        ∀ t,
          letI := completionChartedSpace ribbonSlices.width_pos (ribbonSlices.collar t)
            (ribbonSlices.collar_embedding t) (ribbonSlices.collar_boundary t) (ribbonSlices.collar_zero t)
          ∀ x, (ribbonΞ (sliceIn c t x)).compContinuousLinearMap
            (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x) =
              (completionManifold ribbonSlices.width_pos (ribbonSlices.collar t)
                (ribbonSlices.collar_embedding t) (ribbonSlices.collar_smooth t)
                (ribbonSlices.collar_boundary t) (ribbonSlices.collar_inverse t)
                (ribbonSlices.collar_zero t)).exteriorDerivative (ribbonSlices.primitive t) x) ∧
      (∃ ribbonV : (z : TotalSpace c) → TangentSpace (familyModel (k + 1)) z,
        ribbonV = pulledVerticalField Q.source.ribbonCompletion.ambient.manifold
          ribbonTotal Q.completedRibbonField ∧
        ContMDiff (familyModel (k + 1)) (familyModel (k + 1)).tangent ∞
          (fun z => (⟨z, ribbonV z⟩ : TangentBundle (familyModel (k + 1)) (TotalSpace c))) ∧
        HasRealFieldCoefficientsInPatch (IntrinsicInterior.smoothManifold k M)
          ribbonV (totalInterior c) ∧
        (∃ cutoff : ℝ, cutoff < 0 ∧
          HasRealFieldCoefficientsInPatch
            ((bandManifold ribbonSlices.width (IntrinsicBoundary.smoothManifold k M)).restrict
              (fieldCylinderStrip ribbonSlices.width (IntrinsicBoundary.smoothManifold k M) cutoff))
            ribbonV (fun p => totalCylinder c (p.1, p.2.val)) ∧
          ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
            ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
        ∀ t,
          letI := completionChartedSpace ribbonSlices.width_pos (ribbonSlices.collar t)
            (ribbonSlices.collar_embedding t) (ribbonSlices.collar_boundary t) (ribbonSlices.collar_zero t)
          ∀ x, mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x
            ((completionManifold ribbonSlices.width_pos (ribbonSlices.collar t)
              (ribbonSlices.collar_embedding t) (ribbonSlices.collar_smooth t)
              (ribbonSlices.collar_boundary t) (ribbonSlices.collar_inverse t)
              (ribbonSlices.collar_zero t)).liouvilleVector (ribbonSlices.primitive t) x) =
                ribbonV (sliceIn c t x)) ∧
      ∃ cutoff : ℝ, cutoff < 0 ∧
        ∃ β : ℝ → IntrinsicBoundary.Point k M × ℝ → Q.source.ribbonCompletion.ambient.manifold.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            𝓘(ℝ, Model (2 * n - 2)) ∞
            (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) ∧
          (∀ (t : Parameter) (p : Band ribbonSlices.width (IntrinsicBoundary.Point k M)),
            cutoff < -p.val.1 → β t.val (p.val.2, -p.val.1) =
              (ribbonTotal (totalCylinder c (t, p))).2) ∧
          (∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
            β t.val (x, r) = Q.source.ribbonCompletion.endMap (ribbonBoundary t.val x, r)) ∧
          ∀ (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
            IsLocalDiffeomorphAt
              ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
              ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
              (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (p.1, β p.1 p.2))
              (t.val, (x, r))) ∧
  ∃ (δ : ℝ) (hδ : 0 < δ)
    (C : Parameter → ℝ × IntrinsicBoundary.Point a A → A)
    (hemb : ∀ t, IsOpenEmbedding
      (fun p : Half δ (IntrinsicBoundary.Point a A) => C t p.val))
    (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model a)) (𝓡∂ (a + 1)) ∞
      (C t) (Half δ (IntrinsicBoundary.Point a A)))
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point a A)),
      (𝓡∂ (a + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point a A) →
      ∃ g : A → ℝ × IntrinsicBoundary.Point a A,
        ContMDiffAt (𝓡∂ (a + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model a)) ∞ g (C t p) ∧
          ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point a A)] p, g (C t q) = q)
    (hzero : ∀ t (b : IntrinsicBoundary.Point a A), C t (0, b) = b.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point a A)) => C t p.val))),
  ∃ hmixed : HasRealMixedGerms (δ := δ) C,
    let X := fun t => completionManifold hδ (C t) (hemb t) (hC t)
      (hboundary t) (hinv t) (hzero t)
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold a A)
    let c := fun t (p : Half δ (IntrinsicBoundary.Point a A)) => C t p.val
    letI := bandChartedSpace (k := a) (B := IntrinsicBoundary.Point a A) δ
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    letI := totalFamily_isManifold hδ C hboundary hzero hjoint hmixed
    IsManifold (familyModel (a + 1)) ∞ (TotalSpace c) ∧
      T2Space (TotalSpace c) ∧ SecondCountableTopology (TotalSpace c) ∧
      ContMDiff (familyModel (a + 1)) (familyModel (a + 1)) ∞ (totalInterior c) ∧
      ContMDiff (familyModel (a + 1)) (familyModel (a + 1)) ∞ (totalCylinder c) ∧
      ContMDiff (familyModel (a + 1)) (𝓡∂ 1) ∞ (parameter c) ∧
      (∀ t b, IsMIntegralCurveOn (fun s => C t (s, b))
        (fun x => -IntrinsicLiouville.liouvilleVector (lam t)
          (IntrinsicLiouville.exteriorDerivative (lam t)) x) (Ico 0 δ)) ∧
      ∃ Λ : ∀ t, (X t).Form 1,
        (∀ t, (X t).IsSmoothForm (Λ t)) ∧
        (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
          (fun x => (Λ t (original (c t) x)).compContinuousLinearMap
            (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) (original (c t)) x)) = lam t) ∧
        (∀ t, P.pullback (X t) (cylinder (c t)) (Λ t) = cylinderPrimitive δ (lam t)) ∧
        (∀ t x, (X t).Nondegenerate ((X t).exteriorDerivative (Λ t)) x) ∧
        (∀ t, Nonempty (CompleteLiouvilleFlow (X t) ((X t).liouvilleVector (Λ t)))) ∧
        P.IsSmoothIntervalFormFamily (fun t => P.pullback (X t) (cylinder (c t)) (Λ t)) ∧
      ∃ q : TotalSpace c → (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point,
        Continuous q ∧
        ContMDiff (familyModel (a + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q ∧
        Function.Bijective (Q.ambientNativeTotalComparison C q) ∧
        (∀ t x, q (original (totalCollar c) (t, x)) = Q.ambientNativeReferenceMap eAs t x) ∧
        (∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point a A)),
          q (totalCylinder c (t, p)) =
            (Q.ambientCompletionPresentation t).prescribedEndMap
              (eBs parameterZero p.val.2, -p.val.1)) ∧
        ∃ F : Diffeomorph (familyModel (a + 1)) (familyModel (2 * n))
            (TotalSpace c) (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) ∞,
          (∀ z, F z = (parameter c z, q z)) ∧
        ∃ S : ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            Diffeomorph 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n))
              (X t).Point (Q.pair t).ambientCompletion.ambient.manifold.Point ∞,
          (∀ t x, S t x = (Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x))) ∧
          (∀ t x, S t (original (c t) x) =
            (Q.pair t).ambientCompletion.inclusion.map (eAs t x).val) ∧
          (∀ t (p : Band δ (IntrinsicBoundary.Point a A)),
            S t (cylinder (c t) p) =
              (Q.pair t).ambientCompletion.endMap (eBs t p.val.2, -p.val.1)) ∧
          (∀ t, (X t).pullback (Q.pair t).ambientCompletion.ambient.manifold (S t)
            (Q.pair t).ambientCompletion.ambient.primitive = Λ t) ∧
        (∀ (t u : Parameter) (Ψ : (X t).SmoothEquiv (X u)),
          (X t).pullback (X u) Ψ (Λ u) = Λ t →
          ∀ (ψ : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
              (IntrinsicBoundary.smoothManifold a A))
            (shift : IntrinsicBoundary.Point a A → ℝ),
            ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, ℝ) ∞ shift →
            (∀ x, ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r →
              ∀ (hr : 0 ≤ r) (hr' : 0 ≤ r + shift x),
                Ψ (endIn hδ (c t) ⟨(r, x), hr, mem_univ _⟩) =
                  endIn hδ (c u) ⟨(r + shift x, ψ x), hr', mem_univ _⟩) →
            ∀ (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞),
              IsLocallyExtendibleNativeMap (k := k) h →
              ∀ (scale : ℝ), 0 < scale →
                (∀ x, (μ u (h x)).compContinuousLinearMap
                  (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = scale • μ t x) →
                (∀ x, ψ (j t x) = j u (h x)) →
                ∃ I : CompletionIdentification (Q.pair t) (Q.pair u),
                  I.ambientEquiv = ((S t).symm.trans Ψ).trans (S u) ∧
                  I.scale = scale ∧
                  I.boundaryEquiv = ((eBs t).symm.trans ψ).trans (eBs u) ∧
                  I.shift = shift ∘ (eBs t).symm ∧
                  (∀ x, I.ribbonEquiv.map (eMs t x).val = (eMs u (h x)).val) ∧
                  (∀ y, I.ribbonEquiv.inverse (eMs u y).val = (eMs t (h.symm y)).val)) ∧
        (∀ (t : Parameter) (Z : CompleteLiouvilleManifold (2 * n))
            (i : A → Z.manifold.Point) (q₀ : (X t).SmoothEquiv Z.manifold),
          (X t).pullback Z.manifold q₀ Z.primitive = Λ t →
          (∀ x, q₀ (original (c t) x) = i x) →
          ∃ m : InclusionMarking (Q.pair t).ambientCompletion Z
              (fun y => i ((eAs t).symm y)),
            m.equiv = (S t).symm.trans q₀ ∧
            (S t).trans m.equiv = q₀ ∧
            (∀ x, m.equiv ((Q.pair t).ambientCompletion.inclusion.map (eAs t x).val) = i x) ∧
            ∀ (x : IntrinsicBoundary.Point a A) (r : ℝ),
              m.equiv ((Q.pair t).ambientCompletion.endMap (eBs t x, r)) =
                Z.completeFlow.flow r (i x.val)) ∧
        (∀ t, (X t).pullback Q.source.ambientCompletion.ambient.manifold
          (q ∘ sliceIn c t) (Q.completedPrimitive t) = Λ t) ∧
        (∃ Ξ : (z : TotalSpace c) → TangentSpace (familyModel (a + 1)) z [⋀^Fin 2]→L[ℝ] ℝ,
          ContMDiff ((familyModel (a + 1)).prod
            𝓘(ℝ, (Model 1 × Model (a + 1)) × (Model 1 × Model (a + 1)))) 𝓘(ℝ, ℝ) ∞
            (fun v : TangentPairBundle (familyModel (a + 1)) (X := TotalSpace c) =>
              Ξ v.proj ![v.2.1, v.2.2]) ∧
          (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            ∀ x, (Ξ (sliceIn c t x)).compContinuousLinearMap
              (mfderiv 𝓘(ℝ, Model (a + 1)) (familyModel (a + 1)) (sliceIn c t) x) =
                (X t).exteriorDerivative (Λ t) x) ∧
          (IntrinsicInterior.smoothManifold a A).HasRealIntervalTwoFormCoefficientsOn
            (fun p => (Ξ (totalInterior c p)).compContinuousLinearMap
              (mfderiv (familyModel (a + 1)) (familyModel (a + 1)) (totalInterior c) p)) univ ∧
          ∃ cutoff : ℝ, cutoff < 0 ∧ P.HasRealIntervalTwoFormCoefficientsOn
            (fun p => (Ξ (totalCylinder c p)).compContinuousLinearMap
              (mfderiv (familyModel (a + 1)) (familyModel (a + 1)) (totalCylinder c) p))
            {p | cutoff < -p.val.1} ∧
            ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
              ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
        (∃ Ω : (z : TotalSpace c) → TangentSpace (familyModel (a + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
          ContMDiff (familyModel (a + 1)).tangent 𝓘(ℝ, ℝ) ∞
            (fun v : TangentBundle (familyModel (a + 1)) (TotalSpace c) =>
              Ω v.proj (fun _ => v.2)) ∧
          (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            ∀ x, (Ω (sliceIn c t x)).compContinuousLinearMap
              (mfderiv 𝓘(ℝ, Model (a + 1)) (familyModel (a + 1)) (sliceIn c t) x) = Λ t x) ∧
          HasRealOpenCovectorCoefficients (familyModel (a + 1)) Ω ∧
          (IntrinsicInterior.smoothManifold a A).HasRealIntervalCovectorCoefficientsOn
            (fun p => (Ω (totalInterior c p)).compContinuousLinearMap
              (mfderiv (familyModel (a + 1)) (familyModel (a + 1)) (totalInterior c) p)) univ ∧
          ∃ cutoff : ℝ, cutoff < 0 ∧ P.HasRealIntervalCovectorCoefficientsOn
            (fun p => (Ω (totalCylinder c p)).compContinuousLinearMap
              (mfderiv (familyModel (a + 1)) (familyModel (a + 1)) (totalCylinder c) p))
            {p | cutoff < -p.val.1} ∧
            ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
              ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
        (∃ V : (z : TotalSpace c) → TangentSpace (familyModel (a + 1)) z,
          ContMDiff (familyModel (a + 1)) (familyModel (a + 1)).tangent ∞
            (fun z => (⟨z, V z⟩ : TangentBundle (familyModel (a + 1)) (TotalSpace c))) ∧
          (∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
            ∀ x, mfderiv 𝓘(ℝ, Model (a + 1)) (familyModel (a + 1)) (sliceIn c t) x
              ((X t).liouvilleVector (Λ t) x) = V (sliceIn c t x)) ∧
          HasRealFieldCoefficientsInPatch (IntrinsicInterior.smoothManifold a A)
            V (totalInterior c) ∧
          ∃ cutoff : ℝ, cutoff < 0 ∧
            HasRealFieldCoefficientsInPatch
              (P.restrict (fieldCylinderStrip δ (IntrinsicBoundary.smoothManifold a A) cutoff))
              V (fun p => totalCylinder c (p.1, p.2.val)) ∧
            ∀ z : TotalSpace c, (∃ p, totalInterior c p = z) ∨
              ∃ p, cutoff < -p.2.val.1 ∧ totalCylinder c p = z) ∧
        ∀ t x, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
          mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n))
            ((Q.ambientCompletionPresentation t).equiv ∘ (q ∘ sliceIn c t)) x
            ((X t).liouvilleVector (Λ t) x) =
              (Q.pair t).ambientCompletion.ambient.field
                ((Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x)))

/-- A constructed family, its native compact correspondence, and the full
original completed-family and marking correspondence on that same choice. -/
structure OriginalNativePairFamilyRealization
    (D : OriginalNativePairFamily (a := a) (k := k) (A := A) (M := M)) (n : ℕ)
    [NeZero n] [NeZero (2 * n - 2)] where
  deformation : PairDeformation n
  presentation : NativePairFamilyPresentation D.lam D.μ D.j D.b deformation
  completed : NativePairFamilyCompletionData D deformation presentation

set_option maxHeartbeats 600000 in
/-- Construct one completed realization from the original data, preserving
all the strong producer's completion and supplied-marking capabilities. -/
theorem OriginalNativePairFamily.exists_realization
    (D : OriginalNativePairFamily (a := a) (k := k) (A := A) (M := M))
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2) :
    Nonempty (OriginalNativePairFamilyRealization D n) := by
  obtain ⟨Q, eA, eM, eB, RA, RM, hRA, hRM, hA, hM, hB, hQ, hRibbon, hAmbient⟩ :=
    exists_intrinsic_pairDeformation_with_native_endpoint_identifications_and_markings
      hdimA hdimM D.lam D.hlam D.hAnd D.hAout D.μ D.hμ D.hMnd D.hMout
      D.j D.hjs D.hjinj D.hjimm D.b D.hb D.hpositive D.hribbon
  let L : NativePairFamilyPresentation D.lam D.μ D.j D.b Q := {
    ambientEquiv := eA, ribbonEquiv := eM, boundaryEquiv := eB
    ambientTransport := RA, ribbonTransport := RM
    ambientTransport_smooth := hRA, ribbonTransport_smooth := hRM
    ambient_square := hA, ribbon_square := hM, boundary_square := hB
    presentation := fun t => by
      obtain ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩ := hQ t
      exact ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩
    ribbon_slices := ⟨hRibbon.choose⟩ }
  exact ⟨⟨Q, L, ⟨hRibbon, hAmbient⟩⟩⟩

end FsFltz.Geometry.IntrinsicLiouville
