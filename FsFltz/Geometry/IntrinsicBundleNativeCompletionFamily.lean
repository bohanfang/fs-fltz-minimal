import FsFltz.Geometry.IntrinsicBundlePairFamily
import FsFltz.Geometry.IntrinsicNativeCompletionEndpointIdentification
import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints

/-!
# Original bundle pair data retain their native completed family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–199, and `sec:lean`, lines 788–814.
The original bundle primitives, ribbon map and positive witness are transported
through one compatible global chart for each compact bundle. Their native
Liouville and pair laws are derived from the original atlas laws. One invocation
of the native completed-family producer then retains its actual pair deformation,
its full ribbon completion, its ambient quotient family, strict slice maps and
real coefficient extensions, together with the conditional original endpoint
identification and inclusion-marking constructions on those same witnesses.
On this once-chosen original completed family, every supplied compatible
nonvanishing total-family section with the source's smooth extension laws
constructs all endpoint representatives and a grading of that same deformation.
The native restriction equations use its retained actual completion maps.

The conclusion does not assume collars, a represented family or represented
endpoint maps. It constructs the completed family and transports supplied
original strict maps and markings. Geometric chain existence and the prescribed
ambient grading in `thm:target`, lines 385–413, remain separate obligations.
Representing a preselected section of the original untrivialized bundle is
also separate: the grading capability below is on the chosen completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing
open FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]

set_option maxHeartbeats 800000 in
/-- Original compact bundle data construct one native completed pair family.
The source chart formulas and every witness returned by the native completion
producer, including endpoint-step and marking constructions, belong to the same
existential pair deformation. No independently selected deformation is used. -/
theorem exists_pairDeformation_with_native_completionFamily_of_original_bundle_data
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
            (∀ (Jnative : ∀ s : Parameter, (X s).Point → Model (a + 1) →L[ℝ] Model (a + 1))
                (PI : Model (2 * n) ≃L[ℝ] Model (a + 1))
                (_PE : Model (2 * n) ≃L[ℝ] (Model a × ℝ))
                (σ : OriginalNativeCanonicalSection C Jnative PI),
              (∀ s, IsCompatibleAlmostComplex (X s) ((X s).exteriorDerivative (Λ s)) (Jnative s)) →
              HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero Jnative →
              HasOriginalEndComplexExtensions hδ C hemb hboundary hzero Jnative →
              HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero Jnative PI σ →
              (∀ s x, σ s x ≠ 0) →
              ∃ endpoints : ∀ s, (Q.pair s).Maslov,
                (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
                  ∀ x v, mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) (S s) x
                    (Jnative s x v) = (endpoints s).J (S s x)
                      (mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) (S s) x v)) ∧
                (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
                  ∀ x, originalNativeSectionTensor C Jnative PI σ s x =
                    ((endpoints s).tensor (S s x)).compContinuousLinearMap
                      (fun _ => mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) (S s) x)) ∧
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
                    ((Q.ambientCompletionPresentation t).equiv (q (sliceIn c t x))) := by
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
  refine ⟨cA, cM, hbaseA, hbaseM, heA, heM, ?_, ?_, ?_, ?_, ?_⟩
  · intro dA hdA t ht x vs
    exact PA.formInTrivialization_apply cA heA dA hdA ⟨hAt t, ht⟩ x vs
  · intro dM hdM t ht x vs
    exact PM.formInTrivialization_apply cM heM dM hdM ⟨hMt t, ht⟩ x vs
  · intro dA hdA t ht x
    exact PW.witnessInTrivialization_eq cA heA dA hdA ⟨hAt t, ht⟩ x
  · intro dM hdM dA hdA t ht x
    exact PJ.mapInTrivializations_eq_local_val cM cA heA dM hdM dA hdA
      ⟨⟨hMt t, ht.1⟩, ⟨hAt t, ht.2⟩⟩ x
  · obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hpair,
        hribbonCompletion, δ, hδ, C, hemb, hC, hboundary, hinv, hzero, hjoint, hmixed,
        hman, hT2, hcount, hInterior, hCylinder, hparameter, hode,
        Λ, hΛsmooth, hΛnative, hΛcylinder, hΛnondegenerate, hΛcomplete, hΛend,
        q, hqcontinuous, hqsmooth, hqbijective, hqnative, hqend, F, hF,
        S, hS, hScompact, hSend, hSprimitive, htail⟩ :=
      exists_intrinsic_pairDeformation_with_native_endpoint_identifications_and_markings
      hdimA hdimM lam hlam
      (fun t => LA.nondegenerate_in_compatible_chart cA heA t (hAt t))
      (fun t => LA.outward_in_compatible_chart cA heA t (hAt t))
      μ hμ (fun t => LM.nondegenerate_in_compatible_chart cM heM t (hMt t))
      (fun t => LM.outward_in_compatible_chart cM heM t (hMt t))
      j hjs hjinj hjimm b hb (PW.witnessInTrivialization_positive cA heA) hribbon
    have hpA (t : Parameter) := (hpair t).2.1
    have hcA (t : Parameter) := (hpair t).2.2.2.2.2.2.2.2.1
    have hbA (t : Parameter) := (hpair t).1
    have hbpA (t : Parameter) := (hpair t).2.2.1
    have hSeq (s : Parameter) : S s = Q.ambientNativeSliceCompletionDiffeomorph
        hdimA lam eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
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
        hdimA lam eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
        hjoint hmixed hode q hqnative hqend Jnative PI PE σ
        hbpA Λ (fun t x => congrFun (hΛnative t) x) hΛcylinder hΛsmooth hnative hJI hJE hσ hnσ
    refine ⟨endpoints, ?_, ?_, g, lift, hLift, ?_, ?_⟩
    · intro s
      let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      have hsfun : (fun x => S s x) = (fun x => Q.ambientNativeSliceCompletionDiffeomorph
          hdimA lam eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
          hjoint hmixed hode q hqnative hqend s x) := congrArg (fun f => fun x => f x) (hSeq s)
      have hpred := congrArg (fun f => ∀ x v,
        mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) f x (Jnative s x v) =
          (endpoints s).J (f x)
            (mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) f x v)) hsfun
      exact hpred.mpr (hJnative s)
    · intro s
      let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      have hsfun : (fun x => S s x) = (fun x => Q.ambientNativeSliceCompletionDiffeomorph
          hdimA lam eAs hpA hcA eBs hbA hsquareB RA hRA hsquareA hδ C hemb hC hboundary hinv hzero
          hjoint hmixed hode q hqnative hqend s x) := congrArg (fun f => fun x => f x) (hSeq s)
      have hpred := congrArg (fun f => ∀ x, originalNativeSectionTensor C Jnative PI σ s x =
        ((endpoints s).tensor (f x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (a + 1)) 𝓘(ℝ, Model (2 * n)) f x)) hsfun
      exact hpred.mpr (hTnative s)
    · intro s
      exact (hgJ s).trans (hJrep s)
    · intro s
      exact (funext (hgT s)).trans (hTrep s)

end FsFltz.Geometry.IntrinsicSmoothBundle
