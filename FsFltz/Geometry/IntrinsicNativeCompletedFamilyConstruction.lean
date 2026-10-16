import FsFltz.Geometry.IntrinsicNativeCompletionFamilySeam
import FsFltz.Geometry.IntrinsicNativeCompletionFamilySmooth
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverse
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseSmooth
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyPrimitive
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFields
import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVertical
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalField
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalExterior
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorGerms
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyExteriorGerms
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorAtlas
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFieldGerms
import FsFltz.Geometry.IntrinsicNativeZeroPairFamily
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas
import FsFltz.Geometry.IntrinsicNativeRibbonBoundaryFamily
import FsFltz.Geometry.IntrinsicNativeRibbonTotalComparisonInverse
import FsFltz.Geometry.IntrinsicNativeRibbonTotalCovector
import FsFltz.Geometry.IntrinsicNativeRibbonTotalCovectorGerms
import FsFltz.Geometry.IntrinsicNativeRibbonTotalTensors
import FsFltz.Geometry.IntrinsicNativeRibbonTotalTensorGerms

/-!
# Original native completion families mapped to the same completed pairs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–793 and 805–814.
Original native ambient and ribbon family data produce
one actual pair deformation with its retained compact coherence, and one
original ambient completion-family atlas with its retained native collar,
primitives and complete flows. A jointly smooth map from that very atlas quotient
to the fixed completed ambient of that very pair deformation retains every
native point and the entire half-infinite cylinder. Its parameter-preserving
comparison is a diffeomorphism, and its slice pullback preserves the exact primitive
chosen by the original quotient producer. Its strict slice diffeomorphisms
retain every native and full-cylinder point and the actual Liouville field.
The two producers are
invoked once and their witnesses are kept together.
Positive-dimensional and zero-dimensional ribbons have separate consumers.

The original primitives, spatial exterior derivatives and fields are restrictions
of actual smooth total covector, two-form and tangent sections. Their coefficients
extend to real open neighborhoods on covering native interior and cylinder
patches. The covector also has full coefficient extensions in actual smooth
charts around every original total-space point. The original ribbon quotient
has strict slice comparisons retaining its native points, cylinder, primitive,
flow and full core. The zero ribbon additionally has the same all-real total
comparison and inverse. The positive ribbon's reference boundary comparison
and inverse are jointly smooth for all real parameters, and retain the full
reference cylinder square. The positive ribbon now has a jointly smooth total
comparison and inverse on that original atlas, with exact retained slice maps.
Real interior extensions and inverse germs, and a real cylinder extension with
local inverses at the seam and all outward radii, retain both parameter endpoints.
The positive ribbon also has the canonical actual smooth total primitive
covector, whose spatial restriction is its exact retained slice primitive.
Its full coefficients extend to real open neighborhoods in actual total-space
charts. The same ribbon total map also carries the spatial exterior two-form
and Liouville field, with exact restrictions to the selected slice primitives.
Their real coefficients extend on covering native interior and cylinder patches.
Supplied marking and grading correspondence remain separate obligations.
The geometric target theorem is not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville
open IntrinsicCompletionGluing

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]


set_option maxHeartbeats 600000 in
/-- The original native compact pair-family hypotheses construct both the
same actual completed pair deformation and the original ambient quotient
atlas. Their natural jointly smooth comparison uses that exact atlas collar;
all compact primitive, boundary, witness, ribbon and core data are retained.
This theorem concerns positive-dimensional ribbons. -/
theorem exists_intrinsic_pairDeformation_with_native_completionFamily
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (lam : Parameter → Form a A 1) (hlam : IsLocallyExtendibleFormFamily lam)
    (hAnd : ∀ t x, Nondegenerate (exteriorDerivative (lam t)) x)
    (hAout : ∀ t, ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (lam t) (exteriorDerivative (lam t)) x.val)))
    (μ : Parameter → Form k M 1) (hμ : IsLocallyExtendibleFormFamily μ)
    (hMnd : ∀ t x, Nondegenerate (exteriorDerivative (μ t)) x)
    (hMout : ∀ t, ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μ t) (exteriorDerivative (μ t)) x.val)))
    (j : Parameter → M → IntrinsicBoundary.Point a A)
    (hjs : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) j)
    (hjinj : ∀ t, Function.Injective (j t))
    (hjimm : ∀ t x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x))
    (b : Parameter → IntrinsicBoundary.Point a A → ℝ)
    (hb : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x,
      ((b t (j t x) • IntrinsicBoundary.restrictForm (lam t) (j t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x) = μ t x) :
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
    (∃ ribbonSlices : PairDeformation.NativeRibbonCompletionSlices Q μ eMs,
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
                  ((Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x))) := by
  obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ⟩ :=
    exists_intrinsic_pairDeformation_with_native_coherence_and_coordinates
      hdimA hdimM lam hlam hAnd hAout μ hμ hMnd hMout
      j hjs hjinj hjimm b hb hpositive hribbon
  have hribbonPrimitiveQ : ∀ t x,
      ((Q.pair t).ribbonDomain.liouville.primitive (eMs t x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs t y).val) x) = μ t x := by
    intro t
    exact (hQ t).2.2.2.2.2.1
  have hribbonCoordinatesQ : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ribbonDomain.domain.extension (fun x => (eMs t x).val) := by
    intro t
    obtain ⟨_, _, _, _, _, _, _, _, _, hc⟩ := hQ t
    exact hc
  obtain ⟨ribbonSlices⟩ := Q.exists_nativeRibbonCompletionFamily_slice_comparisons
    hdimM μ hμ hMnd hMout eMs hribbonPrimitiveQ hribbonCoordinatesQ
  obtain ⟨ribbonBoundary, hRBsmooth, hRBinverseSmooth, hRBnative, hRBinverse, hRBcylinder⟩ :=
    ribbonSlices.exists_jointReferenceBoundaryComparison RM hRM hsquareM
  let ribbonC := fun t (p : Half ribbonSlices.width (IntrinsicBoundary.Point k M)) =>
    ribbonSlices.collar t p.val
  let := totalFamilyChartedSpace ribbonSlices.width_pos ribbonSlices.collar
    ribbonSlices.collar_zero ribbonSlices.collar_joint_embedding
  let := totalFamily_isManifold ribbonSlices.width_pos ribbonSlices.collar
    ribbonSlices.collar_boundary ribbonSlices.collar_zero
    ribbonSlices.collar_joint_embedding ribbonSlices.mixed_germs
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) ribbonSlices.width
  let ribbonTotal := ribbonSlices.totalDiffeomorph hdimM RM hRM hsquareM
  obtain ⟨ribbonΩ, hribbonΩeq, hribbonΩsmooth, hribbonΩrestriction⟩ :=
    ribbonSlices.exists_totalCovector_extension_eq RM hRM hsquareM
  have hribbonΩgerms := ribbonSlices.hasRealOpenCovectorCoefficients_totalCovector RM hRM hsquareM
  dsimp only at hribbonΩgerms
  rw [← hribbonΩeq] at hribbonΩgerms
  let ribbonΞ := nativeTotalTwoForm (familyModel (k + 1))
    Q.source.ribbonCompletion.ambient.manifold (parameter ribbonC) ribbonSlices.totalMap
    (fun t => Q.source.ribbonCompletion.ambient.manifold.exteriorDerivative
      (Q.completedRibbonPrimitive t))
  obtain ⟨hribbonΞsmooth, hribbonΞrestriction⟩ :=
    ribbonSlices.totalTwoForm_extension RM hRM hsquareM
  obtain ⟨ribbonV, hribbonVeq, hribbonVsmooth, hribbonVrestriction⟩ :=
    ribbonSlices.exists_totalField_extension_eq RM hRM hsquareM hdimM
  have hribbonΞinterior := ribbonSlices.interiorTwoForm_coefficients RM hRM hsquareM
  obtain ⟨ribbonCutoffΞ, hribbonCutoffΞ, hribbonΞcylinder⟩ :=
    ribbonSlices.exists_cylinderTwoForm_coefficients RM hRM hsquareM
  have hribbonΞcover := totalInterior_cylinder_strip_cover ribbonSlices.width_pos
    ribbonSlices.collar ribbonSlices.collar_boundary ribbonSlices.collar_zero
    ribbonCutoffΞ hribbonCutoffΞ
  have hribbonVinterior := ribbonSlices.interiorField_coefficients RM hRM hsquareM hdimM
  dsimp only at hribbonVinterior
  rw [← hribbonVeq] at hribbonVinterior
  have hribbonVgerms := ribbonSlices.exists_cylinderField_coefficients RM hRM hsquareM hdimM
  dsimp only at hribbonVgerms
  rw [← hribbonVeq] at hribbonVgerms
  obtain ⟨ribbonCutoffV, hribbonCutoffV, hribbonVcylinder⟩ := hribbonVgerms
  have hribbonVcover := totalInterior_cylinder_strip_cover ribbonSlices.width_pos
    ribbonSlices.collar ribbonSlices.collar_boundary ribbonSlices.collar_zero
    ribbonCutoffV hribbonCutoffV
  have hRTslice (t : Parameter) (x : Space (ribbonC t)) :
      ribbonTotal (sliceIn ribbonC t x) =
        (t, (Q.ribbonCompletionPresentation t).equiv.symm (ribbonSlices.comparison t x)) :=
    ribbonSlices.totalEquiv_sliceIn t x
  have hRTnative (t : Parameter) (x : M) :
      ribbonTotal (original (totalCollar ribbonC) (t, x)) =
        (t, (Q.ribbonCompletionPresentation t).equiv.symm
          ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val)) := by
    rw [← sliceIn_original ribbonC t x, hRTslice, ribbonSlices.comparison_native]
  have hRTcylinder (t : Parameter) (p : Band ribbonSlices.width (IntrinsicBoundary.Point k M)) :
      ribbonTotal (totalCylinder ribbonC (t, p)) =
        (t, (Q.ribbonCompletionPresentation t).prescribedEndMap
          (ribbonBoundary t.val p.val.2, -p.val.1)) := by
    rw [← sliceIn_cylinder ribbonC t p, hRTslice, hRBcylinder]
  obtain ⟨ribbonInterior, hRIsmooth, hRIeq⟩ :=
    ribbonSlices.exists_realInteriorExtension RM hRM hsquareM
  have hRIinverse := ribbonSlices.exists_realInteriorInverseGerm hdimM RM hRM hsquareM
  obtain ⟨cutoffRibbon, hcutoffRibbon, ribbonCylinder, hRCsmooth, hRCeq, hRCout, hRClocal⟩ :=
    ribbonSlices.exists_realCylinderExtension RM hRM hsquareM
  have hRCout' (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
      ribbonCylinder t.val (x, r) =
        Q.source.ribbonCompletion.endMap (ribbonBoundary t.val x, r) :=
    (hRCout t x r hr).trans (congrArg (fun b => Q.source.ribbonCompletion.endMap (b, r))
      (hRBnative t x).symm)
  obtain ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed, hatlas⟩ :=
    exists_native_completionFamily_atlas lam hlam hAnd hAout
  let c := fun t (p : Half δ (IntrinsicBoundary.Point a A)) => C t p.val
  let := bandChartedSpace (k := a) (B := IntrinsicBoundary.Point a A) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  obtain ⟨hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily⟩ := hatlas
  have hboundaryQ : ∀ t x,
      (Q.pair t).ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val :=
    fun t => (hQ t).1
  have hprimitiveQ : ∀ t x,
      ((Q.pair t).ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs t y).val) x) = lam t x :=
    fun t => (hQ t).2.1
  have hcoordinatesQ : ∀ t, HasNativeCoordinateExtensions (k := a)
      (Q.pair t).ambientDomain.domain.extension (fun x => (eAs t x).val) := by
    intro t
    obtain ⟨_, _, _, _, _, _, _, _, hcoordA, _⟩ := hQ t
    exact hcoordA
  obtain ⟨q, hq, hqnative, hqend⟩ :=
    Q.exists_continuous_ambientNativeTotalMap hdimA lam eAs hprimitiveQ hcoordinatesQ
      eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hjoint hode hzero
  have hqsmooth := Q.contMDiff_ambientNativeTotalMap hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hboundary hzero hjoint hmixed hode q hqnative hqend
  have hboundaryPrimitive : ∀ t, (IntrinsicBoundary.smoothManifold a A).pullback
      (Q.pair t).ambientDomain.domain.boundary (eBs t)
      ((Q.pair t).ambientDomain.domain.boundaryForm
        (Q.pair t).ambientDomain.liouville.primitive) = IntrinsicBoundary.restrictForm (lam t) :=
    fun t => (hQ t).2.2.1
  have hqbij := Q.bijective_ambientNativeTotalComparison eAs eBs RA hsquareA hδ C q hqnative hqend
  let F := Q.ambientNativeTotalDiffeomorph hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hboundary hzero hjoint hmixed hode q hqnative hqend
  let S := Q.ambientNativeSliceCompletionDiffeomorph hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hSnative := Q.ambientNativeSliceCompletionDiffeomorph_native hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hScylinder := Q.ambientNativeSliceCompletionDiffeomorph_cylinder hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hSprimitive := Q.ambientNativeSliceCompletionDiffeomorph_primitive hdimA lam eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
    hboundaryPrimitive Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder
  have htransport := Q.pullback_completedPrimitive_ambientNativeTotalMap
    lam eAs hprimitiveQ eBs hboundaryPrimitive hsquareB hδ C hemb hC hboundary hinv
    hzero hjoint hmixed Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder
    q hqsmooth hqnative hqend
  have hfield := Q.map_liouvilleVector_ambientNativeTotalMap hdimA
    hδ C hemb hC hboundary hinv hzero hjoint hmixed Λ q hqsmooth htransport hΛnd
  let Ξ := nativeTotalTwoForm (familyModel (a + 1))
    Q.source.ambientCompletion.ambient.manifold (parameter c) q
    (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t))
  obtain ⟨hΞsmooth, hΞrestriction⟩ := Q.ambientNativeTotalTwoForm_extension
    hδ C hemb hC hboundary hinv hzero hjoint hmixed Λ q hqsmooth htransport
  have hΞinterior := Q.ambientNativeInteriorTwoForm_coefficients eAs RA hRA hsquareA
    hδ C hboundary hzero hjoint hmixed q hqsmooth hqnative
  obtain ⟨cutoffΞ, hcutoffΞ, hΞcylinder⟩ :=
    Q.exists_ambientNativeCylinderTwoForm_coefficients hdimA
      lam eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB
      hδ C hboundary hzero hjoint hmixed hode q hqsmooth hqend
  have hΞcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoffΞ hcutoffΞ
  obtain ⟨Ω, hΩeq, hΩsmooth, hΩrestriction⟩ :=
    Q.exists_ambientNativeTotalCovector_extension_eq hδ C hemb hC hboundary hinv
    hzero hjoint hmixed Λ q hqsmooth htransport
  have hΩgerms := Q.exists_ambientNativeCylinderCovector_coefficients hdimA
    lam eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB
    hδ C hboundary hzero hjoint hmixed hode q hqsmooth hqend
  dsimp only at hΩgerms
  rw [← hΩeq] at hΩgerms
  have hΩinterior := Q.ambientNativeInteriorCovector_coefficients eAs RA hRA hsquareA
    hδ C hboundary hzero hjoint hmixed q hqsmooth hqnative
  dsimp only at hΩinterior
  rw [← hΩeq] at hΩinterior
  obtain ⟨cutoff, hcutoff, hΩcylinder⟩ := hΩgerms
  have hcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoff hcutoff
  have hΩatlas := hasRealOpenCovectorCoefficients_totalFamily_of_patches
    hδ C hboundary hzero hjoint hmixed cutoff hcutoff Ω hΩinterior hΩcylinder
  obtain ⟨V, hVeq, hVsmooth, hVrestriction⟩ :=
    Q.exists_ambientNativeTotalField_extension_eq hδ C hemb hC hboundary hinv
      hzero hjoint hmixed Λ q hqsmooth htransport hdimA hΛnd F (fun _ => rfl)
  have hVinterior := Q.ambientNativeInteriorField_coefficients
    hδ C hemb hC hboundary hinv hzero hjoint hmixed q F (fun _ => rfl)
    hdimA eAs RA hRA hsquareA hqnative
  dsimp only at hVinterior
  rw [← hVeq] at hVinterior
  have hVgerms := Q.exists_ambientNativeCylinderField_coefficients
    hδ C hemb hC hboundary hinv hzero hjoint hmixed q F (fun _ => rfl)
    hdimA lam eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB hode hqend
  dsimp only at hVgerms
  rw [← hVeq] at hVgerms
  obtain ⟨cutoffV, hcutoffV, hVcylinder⟩ := hVgerms
  have hVcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoffV hcutoffV
  exact ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ,
    ⟨ribbonSlices, ribbonBoundary, hRBsmooth, hRBinverseSmooth, hRBnative, hRBinverse, hRBcylinder,
      ribbonTotal, (fun _ => rfl), ribbonSlices.parameter_totalEquiv_symm, hRTslice,
      (fun _ _ => rfl), hRTnative, hRTcylinder, ⟨ribbonInterior, hRIsmooth, hRIeq⟩,
      hRIinverse, ⟨ribbonΩ, hribbonΩeq, hribbonΩsmooth, hribbonΩgerms, hribbonΩrestriction⟩,
      ⟨ribbonΞ, rfl, hribbonΞsmooth, hribbonΞinterior,
        ⟨ribbonCutoffΞ, hribbonCutoffΞ, hribbonΞcylinder, hribbonΞcover⟩, hribbonΞrestriction⟩,
      ⟨ribbonV, hribbonVeq, hribbonVsmooth, hribbonVinterior,
        ⟨ribbonCutoffV, hribbonCutoffV, hribbonVcylinder, hribbonVcover⟩, hribbonVrestriction⟩,
      cutoffRibbon, hcutoffRibbon, ribbonCylinder, hRCsmooth, hRCeq, hRCout', hRClocal⟩,
    δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
    hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily,
    q, hq, hqsmooth, hqbij, hqnative, hqend, F, (fun _ => rfl), S, (fun _ _ => rfl),
    hSnative, hScylinder, hSprimitive, htransport,
    ⟨Ξ, hΞsmooth, hΞrestriction, hΞinterior, cutoffΞ, hcutoffΞ, hΞcylinder, hΞcover⟩,
    ⟨Ω, hΩsmooth, hΩrestriction, hΩatlas, hΩinterior, cutoff, hcutoff, hΩcylinder, hcover⟩,
    ⟨V, hVsmooth, hVrestriction, hVinterior, cutoffV, hcutoffV, hVcylinder, hVcover⟩, hfield⟩


end FsFltz.Geometry.IntrinsicLiouville
namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold IntrinsicCompletionGluing

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- Original native rank-one pair data construct the exact completed pair
family, the exact native ambient atlas and their jointly smooth comparison.
The zero-dimensional ribbon, its full core and native primitive are retained
by the same rank-one pair producer. No artificial ribbon boundary is used. -/
theorem exists_native_zero_pairDeformation_with_native_completionFamily
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
        IntrinsicLiouville.HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val)) ∧
    (∃ ribbonSlices : PairDeformation.NativeZeroRibbonCompletionSlices Q μ eFs,
      ∃ ribbonTotal : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
          (ℝ × M) (ℝ × Q.source.ribbonCompletion.ambient.manifold.Point) ∞,
        (∀ z, (ribbonTotal z).1 = z.1) ∧ (∀ z, (ribbonTotal.symm z).1 = z.1) ∧
        (∀ (t : Parameter) x, ribbonTotal (t.val, x) =
          (t.val, (Q.ribbonCompletionPresentation t).equiv.symm (ribbonSlices.comparison t x))) ∧
        (∀ (t : Parameter) y, ribbonTotal.symm (t.val, y) =
          (t.val, (ribbonSlices.comparison t).symm ((Q.ribbonCompletionPresentation t).equiv y)))) ∧
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
  obtain ⟨Q, eAs, eFs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ⟩ :=
    exists_native_zero_pairDeformation_with_native_coherence_and_coordinates
      α hα hnd hout μ j hj hjs b hb hpositive
  obtain ⟨ribbonSlices⟩ := Q.exists_nativeZeroRibbonCompletionFamily_slice_comparisons μ eFs
  obtain ⟨ribbonTotal, hRTparam, hRTinverseParam, hRTnative, hRTinverse⟩ :=
    ribbonSlices.exists_totalComparison RM hRM hsquareM
  obtain ⟨δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed, hatlas⟩ :=
    exists_native_completionFamily_atlas α hα hnd hout
  let c := fun t (p : Half δ (IntrinsicBoundary.Point 1 A)) => C t p.val
  let := bandChartedSpace (k := 1) (B := IntrinsicBoundary.Point 1 A) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  obtain ⟨hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily⟩ := hatlas
  have hboundaryQ : ∀ t x,
      (Q.pair t).ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val :=
    fun t => (hQ t).1
  have hprimitiveQ : ∀ t x,
      ((Q.pair t).ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = α t x := by
    intro t
    obtain ⟨_, _, _, _, hp, _, _, _⟩ := hQ t
    exact hp
  have hcoordinatesQ : ∀ t, IntrinsicLiouville.HasNativeCoordinateExtensions (k := 1)
      (Q.pair t).ambientDomain.domain.extension (fun x => (eAs t x).val) := by
    intro t
    obtain ⟨_, _, _, _, _, _, _, hcoord⟩ := hQ t
    exact hcoord
  obtain ⟨q, hq, hqnative, hqend⟩ :=
    Q.exists_continuous_ambientNativeTotalMap rfl α eAs hprimitiveQ hcoordinatesQ
      eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hjoint hode hzero
  have hqsmooth := Q.contMDiff_ambientNativeTotalMap rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hboundary hzero hjoint hmixed hode q hqnative hqend
  have hboundaryPrimitive : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).pullback
      (Q.pair t).ambientDomain.domain.boundary (eBs t)
      ((Q.pair t).ambientDomain.domain.boundaryForm
        (Q.pair t).ambientDomain.liouville.primitive) = IntrinsicBoundary.restrictForm (α t) :=
    by
      intro t
      obtain ⟨_, _, _, _, _, _, hbp, _⟩ := hQ t
      exact hbp
  have hqbij := Q.bijective_ambientNativeTotalComparison eAs eBs RA hsquareA hδ C q hqnative hqend
  let F := Q.ambientNativeTotalDiffeomorph rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hboundary hzero hjoint hmixed hode q hqnative hqend
  let S := Q.ambientNativeSliceCompletionDiffeomorph rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hSnative := Q.ambientNativeSliceCompletionDiffeomorph_native rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hScylinder := Q.ambientNativeSliceCompletionDiffeomorph_cylinder rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
  have hSprimitive := Q.ambientNativeSliceCompletionDiffeomorph_primitive rfl α eAs hprimitiveQ hcoordinatesQ
    eBs hboundaryQ hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmixed
    hode q hqnative hqend
    hboundaryPrimitive Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder
  have htransport := Q.pullback_completedPrimitive_ambientNativeTotalMap
    α eAs hprimitiveQ eBs hboundaryPrimitive hsquareB hδ C hemb hC hboundary hinv
    hzero hjoint hmixed Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder
    q hqsmooth hqnative hqend
  have hfield := Q.map_liouvilleVector_ambientNativeTotalMap rfl
    hδ C hemb hC hboundary hinv hzero hjoint hmixed Λ q hqsmooth htransport hΛnd
  let Ξ := nativeTotalTwoForm (familyModel (2))
    Q.source.ambientCompletion.ambient.manifold (parameter c) q
    (fun t => Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive t))
  obtain ⟨hΞsmooth, hΞrestriction⟩ := Q.ambientNativeTotalTwoForm_extension
    hδ C hemb hC hboundary hinv hzero hjoint hmixed Λ q hqsmooth htransport
  have hΞinterior := Q.ambientNativeInteriorTwoForm_coefficients eAs RA hRA hsquareA
    hδ C hboundary hzero hjoint hmixed q hqsmooth hqnative
  obtain ⟨cutoffΞ, hcutoffΞ, hΞcylinder⟩ :=
    Q.exists_ambientNativeCylinderTwoForm_coefficients rfl
      α eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB
      hδ C hboundary hzero hjoint hmixed hode q hqsmooth hqend
  have hΞcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoffΞ hcutoffΞ
  obtain ⟨Ω, hΩeq, hΩsmooth, hΩrestriction⟩ :=
    Q.exists_ambientNativeTotalCovector_extension_eq hδ C hemb hC hboundary hinv
    hzero hjoint hmixed Λ q hqsmooth htransport
  have hΩgerms := Q.exists_ambientNativeCylinderCovector_coefficients rfl
    α eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB
    hδ C hboundary hzero hjoint hmixed hode q hqsmooth hqend
  dsimp only at hΩgerms
  rw [← hΩeq] at hΩgerms
  have hΩinterior := Q.ambientNativeInteriorCovector_coefficients eAs RA hRA hsquareA
    hδ C hboundary hzero hjoint hmixed q hqsmooth hqnative
  dsimp only at hΩinterior
  rw [← hΩeq] at hΩinterior
  obtain ⟨cutoff, hcutoff, hΩcylinder⟩ := hΩgerms
  have hcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoff hcutoff
  have hΩatlas := hasRealOpenCovectorCoefficients_totalFamily_of_patches
    hδ C hboundary hzero hjoint hmixed cutoff hcutoff Ω hΩinterior hΩcylinder
  obtain ⟨V, hVeq, hVsmooth, hVrestriction⟩ :=
    Q.exists_ambientNativeTotalField_extension_eq hδ C hemb hC hboundary hinv
      hzero hjoint hmixed Λ q hqsmooth htransport rfl hΛnd F (fun _ => rfl)
  have hVinterior := Q.ambientNativeInteriorField_coefficients
    hδ C hemb hC hboundary hinv hzero hjoint hmixed q F (fun _ => rfl)
    rfl eAs RA hRA hsquareA hqnative
  dsimp only at hVinterior
  rw [← hVeq] at hVinterior
  have hVgerms := Q.exists_ambientNativeCylinderField_coefficients
    hδ C hemb hC hboundary hinv hzero hjoint hmixed q F (fun _ => rfl)
    rfl α eAs hprimitiveQ hcoordinatesQ eBs hboundaryQ hsquareB hode hqend
  dsimp only at hVgerms
  rw [← hVeq] at hVgerms
  obtain ⟨cutoffV, hcutoffV, hVcylinder⟩ := hVgerms
  have hVcover := totalInterior_cylinder_strip_cover hδ C hboundary hzero cutoffV hcutoffV
  exact ⟨Q, eAs, eFs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ,
    ⟨ribbonSlices, ribbonTotal, hRTparam, hRTinverseParam, hRTnative, hRTinverse⟩,
    δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
    hmanifold, hT2, hSC, hinterior, hcylinder, hparameter, hode,
    Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnd, hΛflow, hΛfamily,
    q, hq, hqsmooth, hqbij, hqnative, hqend, F, (fun _ => rfl), S, (fun _ _ => rfl),
    hSnative, hScylinder, hSprimitive, htransport,
    ⟨Ξ, hΞsmooth, hΞrestriction, hΞinterior, cutoffΞ, hcutoffΞ, hΞcylinder, hΞcover⟩,
    ⟨Ω, hΩsmooth, hΩrestriction, hΩatlas, hΩinterior, cutoff, hcutoff, hΩcylinder, hcover⟩,
    ⟨V, hVsmooth, hVrestriction, hVinterior, cutoffV, hcutoffV, hVcylinder, hVcover⟩, hfield⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
