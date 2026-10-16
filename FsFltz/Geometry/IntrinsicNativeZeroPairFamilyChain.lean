import FsFltz.Geometry.IntrinsicNativePairFamilyChain
import FsFltz.Geometry.IntrinsicNativeZeroFamilyEndpointIdentification
import FsFltz.Geometry.NativeZeroPairCompletionCoherence

/-!
# Three comparison arrows from two original zero-ribbon families

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 127–160,
`def:chain`, lines 163–199, and `sec:lean`, lines 788–814 and 825–830.
Two original native rank-one families construct completed deformations.
Matching their ambient primitives, full finite embeddings and boundary
witnesses constructs a strict identification on the exact chosen endpoints.
The finite path retains those two deformations and that identification.

The ribbon one-forms vanish and the full ribbon is its core. Empty ribbons
are allowed by this foundation; the target's nonempty full-fiber assertion
remains a separate obligation. Arbitrary bundles, the toric chain and grading
are not constructed. The output retains native compact correspondences,
their smooth transport and native zero-ribbon-completion slices, without
exporting the larger constructor's total-atlas and marking capability tail.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Output correspondence with a chosen completed zero-ribbon pair. The
full embedded core is the full native ribbon, including the empty case. -/
structure NativeZeroPairPresentation
    (lam : IntrinsicLiouville.Form 1 A 1) (μ : (sourceManifold M).Form 1)
    (j : M → IntrinsicBoundary.Point 1 A) (b : IntrinsicBoundary.Point 1 A → ℝ)
    (P : WitnessedPair 1)
    (eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞)
    (eM : letI := P.ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv P.ambientDomain.domain.boundary) : Prop where
  boundary_inclusion : ∀ x,
    P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val
  ribbon_embedding : ∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x)
  witness : ∀ x, P.witness (eB x) = b x
  embedded_core : P.embeddedCore = eB '' range j
  ambient_primitive : ∀ x,
    (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eA y).val) x) = lam x
  ribbon_primitive : (sourceManifold M).pullback P.ribbonDomain.domain.extension
    (fun x => (eM x).val) P.ribbonDomain.liouville.primitive = μ
  boundary_primitive : (IntrinsicBoundary.smoothManifold 1 A).pullback
    P.ambientDomain.domain.boundary eB
    (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm lam
  ambient_coordinates : IntrinsicLiouville.HasNativeCoordinateExtensions (k := 1)
    P.ambientDomain.domain.extension (fun x => (eA x).val)

/-- Native output maps and smooth transport on one chosen rank-one
deformation. Its native zero-ribbon-completion slices use those same maps. -/
structure NativeZeroPairFamilyPresentation
    (lam : Parameter → IntrinsicLiouville.Form 1 A 1)
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → IntrinsicBoundary.Point 1 A)
    (b : Parameter → IntrinsicBoundary.Point 1 A → ℝ) (Q : PairDeformation 1) where
  ambientEquiv : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A (Q.pair t).ambientDomain.domain.Point ∞
  ribbonEquiv : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞
  boundaryEquiv : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary
  ambientTransport : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A A ∞
  ribbonTransport : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞
  ambientTransport_smooth : IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) ambientTransport
  ribbonTransport_smooth : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) ribbonTransport
  ambient_square : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    ((ambientEquiv parameterZero (ambientTransport t.val x)).val) = (ambientEquiv t x).val
  ribbon_square : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    ((ribbonEquiv parameterZero (ribbonTransport t.val x)).val) = (ribbonEquiv t x).val
  boundary_square : ∀ t x,
    (Q.ambientPresentation t).boundaryEquiv (boundaryEquiv parameterZero x) = boundaryEquiv t x
  presentation : ∀ t, NativeZeroPairPresentation (lam t) (μ t) (j t) (b t)
    (Q.pair t) (ambientEquiv t) (ribbonEquiv t) (boundaryEquiv t)
  ribbon_slices : Nonempty (PairDeformation.NativeZeroRibbonCompletionSlices Q μ ribbonEquiv)

set_option maxHeartbeats 600000 in
/-- The original native rank-one families construct their exact completed
pair deformations and strict junction, retaining every full ribbon point,
boundary witness, primitive and zero-dimensional core on the chosen families.
The three-arrow path uses those very deformations and that identification.
No represented family or completed map, and no ribbon regularity or primitive
matching certificate, is assumed. -/
theorem exists_native_zero_pairFamily_junctionChain
    (lamL : Parameter → IntrinsicLiouville.Form 1 A 1)
    (hlamL : IntrinsicLiouville.IsLocallyExtendibleFormFamily lamL)
    (hndL : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (lamL t)) x)
    (houtL : ∀ t (x : IntrinsicBoundary.Point 1 A),
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (lamL t)
            (IntrinsicLiouville.exteriorDerivative (lamL t)) x.val)))
    (μL : Parameter → (sourceManifold M).Form 1)
    (jL : Parameter → M → IntrinsicBoundary.Point 1 A)
    (hjL : ∀ t, Function.Injective (jL t))
    (hjsL : IsLocallyExtendibleRibbonMapFamily (IntrinsicBoundary.smoothManifold 1 A) jL)
    (bL : Parameter → IntrinsicBoundary.Point 1 A → ℝ)
    (hbL : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily bL)
    (hpositiveL : ∀ t x, 0 < bL t x)
    (lamR : Parameter → IntrinsicLiouville.Form 1 A 1)
    (hlamR : IntrinsicLiouville.IsLocallyExtendibleFormFamily lamR)
    (hndR : ∀ t x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative (lamR t)) x)
    (houtR : ∀ t (x : IntrinsicBoundary.Point 1 A),
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector (lamR t)
            (IntrinsicLiouville.exteriorDerivative (lamR t)) x.val)))
    (μR : Parameter → (sourceManifold M).Form 1)
    (jR : Parameter → M → IntrinsicBoundary.Point 1 A)
    (hjR : ∀ t, Function.Injective (jR t))
    (hjsR : IsLocallyExtendibleRibbonMapFamily (IntrinsicBoundary.smoothManifold 1 A) jR)
    (bR : Parameter → IntrinsicBoundary.Point 1 A → ℝ)
    (hbR : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily bR)
    (hpositiveR : ∀ t x, 0 < bR t x)
    (hlamJ : lamL parameterOne = lamR parameterZero)
    (hjJ : jL parameterOne = jR parameterZero)
    (hbJ : bL parameterOne = bR parameterZero) :
    ∃ (F G : PairDeformation 1),
    ∃ (L : NativeZeroPairFamilyPresentation lamL μL jL bL F)
      (R : NativeZeroPairFamilyPresentation lamR μR jR bR G),
    ∃ I : CompletionIdentification F.target G.source,
      I.scale = 1 ∧
      (∀ x, I.ribbonEquiv.map (L.ribbonEquiv parameterOne x).val =
        (R.ribbonEquiv parameterZero x).val) ∧
      (∀ x, I.ribbonEquiv.inverse (R.ribbonEquiv parameterZero x).val =
        (L.ribbonEquiv parameterOne x).val) ∧
      (∀ x, I.boundaryEquiv (L.boundaryEquiv parameterOne x) =
        R.boundaryEquiv parameterZero x) ∧
      (∀ x, I.shift x = 0) ∧
      (∀ x, G.source.witness (I.boundaryEquiv x) = F.target.witness x) ∧
      (∀ x, I.ambientEquiv
        (F.target.ambientCompletion.inclusion.map (L.ambientEquiv parameterOne x).val) =
          G.source.ambientCompletion.inclusion.map (R.ambientEquiv parameterZero x).val) ∧
      (∀ x, I.ambientEquiv.symm
        (G.source.ambientCompletion.inclusion.map (R.ambientEquiv parameterZero x).val) =
          F.target.ambientCompletion.inclusion.map (L.ambientEquiv parameterOne x).val) ∧
      (∀ x r, I.ambientEquiv
        (F.target.ambientCompletion.endMap (L.boundaryEquiv parameterOne x, r)) =
          G.source.ambientCompletion.endMap (R.boundaryEquiv parameterZero x, r)) ∧
    ∃ path : ComparisonChain F.source G.target,
      path = F.junctionChain G I ∧ path.length = 3 ∧
      path.vertices = [F.source, F.target, G.source, G.target] := by
  obtain ⟨F, eAL, eML, eBL, RAL, RML, hRAL, hRML, hAL, hML, hBL, hF, hRibbonL, _⟩ :=
    exists_native_zero_pairDeformation_with_native_endpoint_identifications_and_markings
      lamL hlamL hndL houtL μL jL hjL hjsL bL hbL hpositiveL
  obtain ⟨G, eAR, eMR, eBR, RAR, RMR, hRAR, hRMR, hAR, hMR, hBR, hG, hRibbonR, _⟩ :=
    exists_native_zero_pairDeformation_with_native_endpoint_identifications_and_markings
      lamR hlamR hndR houtR μR jR hjR hjsR bR hbR hpositiveR
  obtain ⟨ribbonSlicesL, _⟩ := hRibbonL
  obtain ⟨ribbonSlicesR, _⟩ := hRibbonR
  let L : NativeZeroPairFamilyPresentation lamL μL jL bL F := {
    ambientEquiv := eAL
    ribbonEquiv := eML
    boundaryEquiv := eBL
    ambientTransport := RAL
    ribbonTransport := RML
    ambientTransport_smooth := hRAL
    ribbonTransport_smooth := hRML
    ambient_square := hAL
    ribbon_square := hML
    boundary_square := hBL
    presentation := fun t => by
      obtain ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩ := hF t
      exact ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩
    ribbon_slices := ⟨ribbonSlicesL⟩ }
  let R : NativeZeroPairFamilyPresentation lamR μR jR bR G := {
    ambientEquiv := eAR
    ribbonEquiv := eMR
    boundaryEquiv := eBR
    ambientTransport := RAR
    ribbonTransport := RMR
    ambientTransport_smooth := hRAR
    ribbonTransport_smooth := hRMR
    ambient_square := hAR
    ribbon_square := hMR
    boundary_square := hBR
    presentation := fun t => by
      obtain ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩ := hG t
      exact ⟨hB, hj, hb, hcore, hpA, hpM, hpB, hcA⟩
    ribbon_slices := ⟨ribbonSlicesR⟩ }
  have hLeft := L.presentation parameterOne
  have hRight := R.presentation parameterZero
  obtain ⟨I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend⟩ := CompletionIdentification.exists_of_same_native_zero_pair
      F.target G.source
      (lamL parameterOne) (hlamL.slice parameterOne) (hndL parameterOne) (houtL parameterOne)
      (L.ambientEquiv parameterOne) (R.ambientEquiv parameterZero)
      (L.ribbonEquiv parameterOne) (R.ribbonEquiv parameterZero)
      (L.boundaryEquiv parameterOne) (R.boundaryEquiv parameterZero)
      hLeft.ambient_primitive
      (by simpa only [PairDeformation.source, hlamJ] using hRight.ambient_primitive)
      hLeft.ambient_coordinates hRight.ambient_coordinates
      hLeft.boundary_inclusion hRight.boundary_inclusion
      (jL parameterOne) hLeft.ribbon_embedding
      (by simpa only [PairDeformation.source, hjJ] using hRight.ribbon_embedding)
      (bL parameterOne) hLeft.witness
      (by simpa only [PairDeformation.source, hbJ] using hRight.witness)
  exact ⟨F, G, L, R, I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend, F.junctionChain G I, rfl, rfl, rfl⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
