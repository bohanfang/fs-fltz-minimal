import FsFltz.Geometry.IntrinsicNativeCompletionEndpointIdentification
import FsFltz.Geometry.NativePairCompletionCoherence

/-!
# Three comparison arrows from two original native pair families

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–199, `g:chain`, lines 385–413, and
`sec:lean`, lines 788–814. Two original families on fixed native manifolds
produce their actual completed pair deformations. Equality of the native
endpoint primitives, full embeddings and witnesses then constructs a strict
completion identification on those exact deformations. The finite path keeps
the two chosen deformations and their constructed identification literally.

This is a positive-dimensional, fixed-source foundation. It supplies neither
an arbitrary bundle itinerary nor the toric target's chain or grading. The
output retains native compact correspondences, their smooth transport, and
native ribbon-completion slices; it does not export the larger constructor's
entire total-atlas and inclusion-marking capability conjunction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

namespace PairDeformation

/-- The exact two deformations and their intervening identification form
three permitted arrows, with literal endpoint matching. -/
def junctionChain {n : ℕ} (F G : PairDeformation n)
    (I : CompletionIdentification F.target G.source) : ComparisonChain F.source G.target :=
  ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons
    (ComparisonStep.identification I)).cons (ComparisonStep.deformation G)

@[simp] theorem junctionChain_length {n : ℕ} (F G : PairDeformation n)
    (I : CompletionIdentification F.target G.source) :
    (F.junctionChain G I).length = 3 := rfl

/-- The native junction remains an explicit intermediate pair change. -/
@[simp] theorem junctionChain_vertices {n : ℕ} (F G : PairDeformation n)
    (I : CompletionIdentification F.target G.source) :
    (F.junctionChain G I).vertices = [F.source, F.target, G.source, G.target] := rfl

end PairDeformation

namespace IntrinsicLiouville

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Output correspondence between an original native pair and its chosen
completed presentation. Every law concerns that same pair and its full data.
This predicate is concluded by the native-family producer, not assumed as
input to the original-family chain theorem. -/
structure NativePairPresentation
    (lam : Form a A 1) (μ : Form k M 1)
    (j : M → IntrinsicBoundary.Point a A)
    (b : IntrinsicBoundary.Point a A → ℝ) (P : WitnessedPair n)
    (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A P.ambientDomain.domain.Point ∞)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv P.ambientDomain.domain.boundary) : Prop where
  boundary_inclusion : ∀ x,
    P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val
  ambient_primitive : ∀ x,
    (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA y).val) x) = lam x
  boundary_primitive : (IntrinsicBoundary.smoothManifold a A).pullback
    P.ambientDomain.domain.boundary eB
    (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm lam
  ribbon_embedding : ∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x)
  witness : ∀ x, P.witness (eB x) = b x
  ribbon_primitive : ∀ x,
    (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ x
  ribbon_image : P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = eB '' range j
  embedded_core : P.embeddedCore = (fun x => eB (j x)) ''
    {x | ∀ s : ℝ, 0 ≤ s → P.ribbonCompletion.ambient.completeFlow.flow s
      (P.ribbonCompletion.inclusion.map (eM x).val) ∈
        range (fun y => P.ribbonCompletion.inclusion.map (eM y).val)}
  ambient_coordinates : HasNativeCoordinateExtensions (k := a)
    P.ambientDomain.domain.extension (fun x => (eA x).val)
  ribbon_coordinates : HasNativeCoordinateExtensions (k := k)
    P.ribbonDomain.domain.extension (fun x => (eM x).val)

/-- The output maps and native compact transport on one actual constructed
deformation. Native ribbon-completion slices are retained on that same choice.
The original-family theorem constructs this output from raw native germs. -/
structure NativePairFamilyPresentation
    (lam : Parameter → Form a A 1) (μ : Parameter → Form k M 1)
    (j : Parameter → M → IntrinsicBoundary.Point a A)
    (b : Parameter → IntrinsicBoundary.Point a A → ℝ) (Q : PairDeformation n) where
  ambientEquiv : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
    (Q.pair t).ambientDomain.domain.Point ∞
  ribbonEquiv : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞
  boundaryEquiv : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary
  ambientTransport : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A ∞
  ribbonTransport : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞
  ambientTransport_smooth : IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) ambientTransport
  ribbonTransport_smooth : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) ribbonTransport
  ambient_square : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    ((ambientEquiv parameterZero (ambientTransport t.val x)).val) = (ambientEquiv t x).val
  ribbon_square : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    ((ribbonEquiv parameterZero (ribbonTransport t.val x)).val) = (ribbonEquiv t x).val
  boundary_square : ∀ t x,
    (Q.ambientPresentation t).boundaryEquiv (boundaryEquiv parameterZero x) = boundaryEquiv t x
  presentation : ∀ t, NativePairPresentation (lam t) (μ t) (j t) (b t)
    (Q.pair t) (ambientEquiv t) (ribbonEquiv t) (boundaryEquiv t)
  ribbon_slices : Nonempty (PairDeformation.NativeRibbonCompletionSlices Q μ ribbonEquiv)

set_option maxHeartbeats 600000 in
/-- Construct two completed deformations from their original native families,
then construct the strict junction from matching native endpoint data. Ribbon
primitive matching follows from the two defining pullback laws. The output
retains the original full data at every chosen slice and the exact three-arrow
path. No represented deformation, completion map, end square, or grading lift
is supplied by the caller. -/
theorem exists_intrinsic_pairFamily_junctionChain
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (lamL : Parameter → Form a A 1) (hlamL : IsLocallyExtendibleFormFamily lamL)
    (hAndL : ∀ t x, Nondegenerate (exteriorDerivative (lamL t)) x)
    (hAoutL : ∀ t, ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (lamL t) (exteriorDerivative (lamL t)) x.val)))
    (μL : Parameter → Form k M 1) (hμL : IsLocallyExtendibleFormFamily μL)
    (hMndL : ∀ t x, Nondegenerate (exteriorDerivative (μL t)) x)
    (hMoutL : ∀ t, ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μL t) (exteriorDerivative (μL t)) x.val)))
    (jL : Parameter → M → IntrinsicBoundary.Point a A)
    (hjsL : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) jL)
    (hjinjL : ∀ t, Function.Injective (jL t))
    (hjimmL : ∀ t x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (jL t) x))
    (bL : Parameter → IntrinsicBoundary.Point a A → ℝ)
    (hbL : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily bL)
    (hpositiveL : ∀ t x, 0 < bL t x)
    (hribbonL : ∀ t x,
      ((bL t (jL t x) • IntrinsicBoundary.restrictForm (lamL t) (jL t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (jL t) x) = μL t x)
    (lamR : Parameter → Form a A 1) (hlamR : IsLocallyExtendibleFormFamily lamR)
    (hAndR : ∀ t x, Nondegenerate (exteriorDerivative (lamR t)) x)
    (hAoutR : ∀ t, ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (lamR t) (exteriorDerivative (lamR t)) x.val)))
    (μR : Parameter → Form k M 1) (hμR : IsLocallyExtendibleFormFamily μR)
    (hMndR : ∀ t x, Nondegenerate (exteriorDerivative (μR t)) x)
    (hMoutR : ∀ t, ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (μR t) (exteriorDerivative (μR t)) x.val)))
    (jR : Parameter → M → IntrinsicBoundary.Point a A)
    (hjsR : IsLocallyExtendibleMapFamily (k := k) (IntrinsicBoundary.smoothManifold a A) jR)
    (hjinjR : ∀ t, Function.Injective (jR t))
    (hjimmR : ∀ t x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (jR t) x))
    (bR : Parameter → IntrinsicBoundary.Point a A → ℝ)
    (hbR : (IntrinsicBoundary.smoothManifold a A).IsLocallyExtendibleIntervalScalarFamily bR)
    (hpositiveR : ∀ t x, 0 < bR t x)
    (hribbonR : ∀ t x,
      ((bR t (jR t x) • IntrinsicBoundary.restrictForm (lamR t) (jR t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (jR t) x) = μR t x)
    (hlamJ : lamL parameterOne = lamR parameterZero)
    (hjJ : jL parameterOne = jR parameterZero)
    (hbJ : bL parameterOne = bR parameterZero) :
    ∃ (F G : PairDeformation n),
    ∃ (L : NativePairFamilyPresentation lamL μL jL bL F)
      (R : NativePairFamilyPresentation lamR μR jR bR G),
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
    exists_intrinsic_pairDeformation_with_native_endpoint_identifications_and_markings
      hdimA hdimM lamL hlamL hAndL hAoutL μL hμL hMndL hMoutL
      jL hjsL hjinjL hjimmL bL hbL hpositiveL hribbonL
  obtain ⟨G, eAR, eMR, eBR, RAR, RMR, hRAR, hRMR, hAR, hMR, hBR, hG, hRibbonR, _⟩ :=
    exists_intrinsic_pairDeformation_with_native_endpoint_identifications_and_markings
      hdimA hdimM lamR hlamR hAndR hAoutR μR hμR hMndR hMoutR
      jR hjsR hjinjR hjimmR bR hbR hpositiveR hribbonR
  obtain ⟨ribbonSlicesL, _⟩ := hRibbonL
  obtain ⟨ribbonSlicesR, _⟩ := hRibbonR
  let L : NativePairFamilyPresentation lamL μL jL bL F := {
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
      obtain ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩ := hF t
      exact ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩
    ribbon_slices := ⟨ribbonSlicesL⟩ }
  let R : NativePairFamilyPresentation lamR μR jR bR G := {
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
      obtain ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩ := hG t
      exact ⟨hB, hpA, hpB, hj, hb, hpM, himage, hcore, hcA, hcM⟩
    ribbon_slices := ⟨ribbonSlicesR⟩ }
  have hμJ : μL parameterOne = μR parameterZero := by
    funext x
    rw [← hribbonL parameterOne x, ← hribbonR parameterZero x, hlamJ, hjJ, hbJ]
  have hLeft := L.presentation parameterOne
  have hRight := R.presentation parameterZero
  obtain ⟨I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend⟩ := CompletionIdentification.exists_of_same_native_pair
      F.target G.source hdimA hdimM
      (lamL parameterOne) (hlamL.slice parameterOne) (hAndL parameterOne) (hAoutL parameterOne)
      (μL parameterOne) (hμL.slice parameterOne) (hMndL parameterOne) (hMoutL parameterOne)
      (L.ambientEquiv parameterOne) (R.ambientEquiv parameterZero)
      (L.ribbonEquiv parameterOne) (R.ribbonEquiv parameterZero)
      (L.boundaryEquiv parameterOne) (R.boundaryEquiv parameterZero)
      hLeft.ambient_primitive
      (by simpa only [PairDeformation.source, hlamJ] using hRight.ambient_primitive)
      hLeft.ribbon_primitive
      (by simpa only [PairDeformation.source, hμJ] using hRight.ribbon_primitive)
      hLeft.ambient_coordinates hRight.ambient_coordinates
      hLeft.ribbon_coordinates hRight.ribbon_coordinates
      hLeft.boundary_inclusion hRight.boundary_inclusion
      (jL parameterOne) hLeft.ribbon_embedding
      (by simpa only [PairDeformation.source, hjJ] using hRight.ribbon_embedding)
      (bL parameterOne) hLeft.witness
      (by simpa only [PairDeformation.source, hbJ] using hRight.witness)
  exact ⟨F, G, L, R, I, hscale, hribbon, hribbon_inv, hboundary, hshift, hwitness,
    hambient, hambient_inv, hend, F.junctionChain G I, rfl, rfl, rfl⟩

end IntrinsicLiouville

end FsFltz.Geometry
