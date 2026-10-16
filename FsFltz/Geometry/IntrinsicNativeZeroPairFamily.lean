import FsFltz.Geometry.IntrinsicLiouvilleBoundaryFamily
import FsFltz.Geometry.IntrinsicLiouvilleBoundaryPresentation
import FsFltz.Geometry.IntrinsicZeroNativeRibbonFamily
import FsFltz.Geometry.IntrinsicPairFamilyTransport
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation

/-!
# Fully native rank-one pair families

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–814 and 825–830.
Original joint native ambient primitive germs and the Liouville inequalities
construct one compact and boundary presentation for the whole interval.
Original zero-dimensional ribbon-map and boundary-witness germs are then
transported through that same constructed boundary equivalence. The actual
pair-family producer constructs both completed families.

The output retains the native compact diffeomorphisms, ribbon maps,
witness values, primitives in every tangent direction, and each full core.
No compact presentation, extended family, collar, completion or compatibility
certificate is supplied by the caller. Domain-bundle trivialization and the
target-specific full-fiber markings and endpoint comparison remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

omit [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [IsManifold 𝓘(ℝ, Model 0) ∞ M] in
/-- Fixed smooth postcomposition transports the actual target-valued native
joint germs, with exact agreement at each interval point. -/
theorem IsLocallyExtendibleRibbonMapFamily.comp_contMDiff
    {d e : ℕ} (N : SmoothManifold d) (P : SmoothManifold e)
    (j : Parameter → M → N.Point) (hj : IsLocallyExtendibleRibbonMapFamily N j)
    (f : N.Point → P.Point) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f) :
    IsLocallyExtendibleRibbonMapFamily P (fun t x => f (j t x)) := by
  intro t x
  obtain ⟨U, hpU, g, hg, heq⟩ := hj t x
  exact ⟨U, hpU, f ∘ g, hf.comp hg, fun s y h => congrArg f (heq s y h)⟩

variable {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- Original native ambient and ribbon families construct actual rank-one
pair deformations. The one constructed boundary equivalence transports
every parameter's ribbon and witness, and the native compact
diffeomorphisms preserve the original forms and full embedded cores.
Both completion families are part of the constructed deformation. -/
theorem exists_native_zero_pairDeformation_with_native_coherence_and_coordinates
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
        IntrinsicLiouville.HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val) := by
  obtain ⟨D, i, e, L, eB, he, hi, _, _, _, _, hL, _, hpull, _, _, _, _, hcoordA,
    hBinclusion, hpullB⟩ :=
    IntrinsicLiouville.exists_liouvilleFamily_with_native_boundary_presentation_and_coordinates
      α hα hnd hout
  have hjs' := hjs.comp_contMDiff (IntrinsicBoundary.smoothManifold 1 A)
    D.boundary j eB eB.contMDiff
  have hbG := hb.comp_contMDiff D.boundary (IntrinsicBoundary.smoothManifold 1 A)
    b eB.symm eB.symm.contMDiff
  let hb' := D.boundary.isSmoothIntervalScalarFamily_of_local_germs
    (fun t x => b t (eB.symm x)) hbG
  obtain ⟨hjs, hprimitive, ambient, ribbon, Q, hQdef, hQ, hcore⟩ :=
    exists_native_zero_pairDeformation_of_local_germs_with_presentations
    D L hL μ (fun t => eB ∘ j t) (fun t => eB.injective.comp (hj t))
    hjs' (fun t x => b t (eB.symm x)) hbG (fun t x => hpositive t (eB.symm x))
  subst Q
  let CA := ambient.collars
  let CF := ribbon.collars
  let Qassembled := D.localizedPairDeformation (n := 1) (compactDomain M) L (liouvilleFamily μ)
    (fun t => nativeRibbonEmbedding D (eB ∘ j t) (eB.injective.comp (hj t)))
    (fun t x => b t (eB.symm x)) hL (primitiveFamily_smooth μ) hjs
    hb' (fun t x => hpositive t (eB.symm x)) ambient ribbon hprimitive
  let eAs := fun t : Parameter => e.trans (CA t).originalPointDiffeomorph.symm
  let eFs := fun t : Parameter => localizedRibbonCarrierDiffeomorph (μ t) (CF t)
  let eBs := fun _ : Parameter => eB
  let RA := ambient.transportedNativeDiffeomorph (𝓡∂ 2) e
  let RM := ribbon.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) (carrierDiffeomorph (μ parameterZero))
  refine ⟨Qassembled, eAs, eFs, eBs, RA, RM,
    ambient.jointlySmooth_transportedNativeDiffeomorph _ e,
    ribbon.jointlySmooth_zeroTransportedNativeDiffeomorph _ _,
    ambient.transportedNativeDiffeomorph_square _ e,
    ribbon.zeroTransportedNativeDiffeomorph_square _ _, ?_, ?_⟩
  · intro t x
    change (ambient.compactPresentation t).boundaryEquiv (eB x) = eB x
    rw [ambient.boundary_compactPresentation]
    rfl
  · intro t
    let P := localizedZeroWitnessedPair ⟨D, L t⟩ (μ t) (CA t) (CF t)
      (eB ∘ j t) (eB.injective.comp (hj t)) (fun x => b t (eB.symm x))
      (hb'.contMDiff_slice t) (fun x => hpositive t (eB.symm x))
    let C := CA t
    let eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞ :=
      e.trans C.originalPointDiffeomorph.symm
    let := P.ribbonDomain.domain.zeroChartedSpace
    let eF : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞ :=
      localizedRibbonCarrierDiffeomorph (μ t) (CF t)
    have heA (x : A) : (eA x).val.val.val = i x := he x
    have hboundary (x : IntrinsicBoundary.Point 1 A) :
        P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val := by
      apply C.originalInclusion.embedding.injective
      change D.boundaryInclusion.map (eB x) = (eA x.val).val.val.val
      rw [heA]
      exact hBinclusion x
    refine ⟨hboundary, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      change b t (eB.symm (eB x)) = b t x
      rw [eB.symm_apply_apply]
    · have hrange : range (eB ∘ j t) = eB '' range (j t) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨j t x, mem_range_self x, rfl⟩
        · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, rfl⟩
      exact (hcore t).trans hrange
    · apply IntrinsicLiouville.native_primitive_localizedDomain ⟨D, L t⟩ C e (α t)
      intro x
      rw [show (fun y => (e y).val) = i from funext he, he]
      exact congrFun (hpull t) x
    · exact localizedZeroWitnessedPair_primitive ⟨D, L t⟩ (μ t) (CA t) (CF t)
        (eB ∘ j t) (eB.injective.comp (hj t)) (fun x => b t (eB.symm x))
        (hb'.contMDiff_slice t) (fun x => hpositive t (eB.symm x))
    · change (IntrinsicBoundary.smoothManifold 1 A).pullback D.boundary eB
        (C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive) = _
      rw [C.localized_boundaryForm]
      exact hpullB t
    · exact hcoordA.of_smooth_square D.extension C.localizedDomain.domain.extension i
        (fun x => (eA x).val) C.originalInclusion.map C.originalInclusion.map.contMDiff heA

/-- The coherence interface forgetting only the retained endpoint coordinate germs. -/
theorem exists_native_zero_pairDeformation_with_native_coherence
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
            IntrinsicBoundary.restrictForm (α t) := by
  obtain ⟨Q, eA, eF, eB, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ⟩ :=
    exists_native_zero_pairDeformation_with_native_coherence_and_coordinates
      α hα hnd hout μ j hj hjs b hb hpositive
  refine ⟨Q, eA, eF, eB, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, ?_⟩
  intro t
  obtain ⟨hB, hjQ, hbQ, hcore, hA, hM, hBA, _⟩ := hQ t
  exact ⟨hB, hjQ, hbQ, hcore, hA, hM, hBA⟩

/-- Original native ambient and ribbon families construct actual rank-one
pair deformations. The one constructed boundary equivalence transports
every parameter's ribbon and witness, and the native compact
diffeomorphisms preserve the original forms and full embedded cores.
Both completion families are part of the constructed deformation. -/
theorem exists_native_zero_pairDeformation
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
    ∃ (D : CompactDomain 2) (i : A → D.extension.Point)
      (e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A D.Point ∞)
      (L : Parameter → LiouvilleStructure D)
      (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv D.boundary),
      (∀ x, (e x).val = i x) ∧
      (∀ t, (fun x => ((L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) i x)) = α t) ∧
      (∀ x, D.boundaryInclusion.map (eB x) = i x.val) ∧
      (∀ t, (IntrinsicBoundary.smoothManifold 1 A).pullback D.boundary eB
        (D.boundaryForm (L t).primitive) = IntrinsicBoundary.restrictForm (α t)) ∧
      ∃ hb' : D.boundary.IsSmoothIntervalScalarFamily (fun t x => b t (eB.symm x)),
        ∃ CA : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain 2),
          ∃ CF : (t : Parameter) → LiouvilleDomain.FlowCollar (liouvilleDomain M (μ t)),
            ∃ Q : PairDeformation 1,
              (Q.pair = fun t => localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
                (CA t) (CF t) (eB ∘ j t) (eB.injective.comp (hj t))
                (fun x => b t (eB.symm x)) (hb'.contMDiff_slice t)
                (fun x => hpositive t (eB.symm x))) ∧
              ∀ t,
                let P := localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
                  (CA t) (CF t) (eB ∘ j t) (eB.injective.comp (hj t))
                  (fun x => b t (eB.symm x)) (hb'.contMDiff_slice t)
                  (fun x => hpositive t (eB.symm x))
                ∃ eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞,
                  letI := P.ribbonDomain.domain.zeroChartedSpace
                  ∃ eF : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
                    P.ribbonDomain.domain.Point ∞,
                    (∀ x, (eA x).val.val.val = i x) ∧
                    (∀ x, (eF x).val.val.val = x) ∧
                    (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val) ∧
                    (∀ x, P.ribbonEmbedding.map (eF x).val = eB (j t x)) ∧
                    (∀ x, P.witness (eB x) = b t x) ∧
                    P.embeddedCore = eB '' range (j t) ∧
                    (∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
                      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eA y).val) x) = α t x) ∧
                    (sourceManifold M).pullback P.ribbonDomain.domain.extension
                      (fun x => (eF x).val) P.ribbonDomain.liouville.primitive = μ t ∧
                    (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary eB
                      (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
                        IntrinsicBoundary.restrictForm (α t) := by
  obtain ⟨D, i, e, L, eB, he, hi, _, _, _, _, hL, _, hpull, _, _, _, _, _,
    hBinclusion, hpullB⟩ :=
    IntrinsicLiouville.exists_liouvilleFamily_with_native_boundary_presentation_and_coordinates
      α hα hnd hout
  have hjs' := hjs.comp_contMDiff (IntrinsicBoundary.smoothManifold 1 A)
    D.boundary j eB eB.contMDiff
  have hbG := hb.comp_contMDiff D.boundary (IntrinsicBoundary.smoothManifold 1 A)
    b eB.symm eB.symm.contMDiff
  let hb' := D.boundary.isSmoothIntervalScalarFamily_of_local_germs
    (fun t x => b t (eB.symm x)) hbG
  obtain ⟨CA, CF, Q, hQ, hcore⟩ := exists_native_zero_pairDeformation_of_local_germs
    D L hL μ (fun t => eB ∘ j t) (fun t => eB.injective.comp (hj t))
    hjs' (fun t x => b t (eB.symm x)) hbG (fun t x => hpositive t (eB.symm x))
  refine ⟨D, i, e, L, eB, he, hpull, hBinclusion, hpullB, hb', CA, CF, Q, hQ, ?_⟩
  intro t
  let P := localizedZeroWitnessedPair ⟨D, L t⟩ (μ t) (CA t) (CF t)
    (eB ∘ j t) (eB.injective.comp (hj t)) (fun x => b t (eB.symm x))
    (hb'.contMDiff_slice t) (fun x => hpositive t (eB.symm x))
  let C := CA t
  let eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞ :=
    e.trans C.originalPointDiffeomorph.symm
  let := P.ribbonDomain.domain.zeroChartedSpace
  let eF : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞ :=
    localizedRibbonCarrierDiffeomorph (μ t) (CF t)
  have heA (x : A) : (eA x).val.val.val = i x := he x
  have hboundary (x : IntrinsicBoundary.Point 1 A) :
      P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val := by
    apply C.originalInclusion.embedding.injective
    change D.boundaryInclusion.map (eB x) = (eA x.val).val.val.val
    rw [heA]
    exact hBinclusion x
  refine ⟨eA, eF, heA, fun _ => rfl, hboundary, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change b t (eB.symm (eB x)) = b t x
    rw [eB.symm_apply_apply]
  · have hrange : range (eB ∘ j t) = eB '' range (j t) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨j t x, mem_range_self x, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    exact (hcore t).trans hrange
  · apply IntrinsicLiouville.native_primitive_localizedDomain ⟨D, L t⟩ C e (α t)
    intro x
    rw [show (fun y => (e y).val) = i from funext he, he]
    exact congrFun (hpull t) x
  · exact localizedZeroWitnessedPair_primitive ⟨D, L t⟩ (μ t) (CA t) (CF t)
      (eB ∘ j t) (eB.injective.comp (hj t)) (fun x => b t (eB.symm x))
      (hb'.contMDiff_slice t) (fun x => hpositive t (eB.symm x))
  · change (IntrinsicBoundary.smoothManifold 1 A).pullback D.boundary eB
      (C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive) = _
    rw [C.localized_boundaryForm]
    exact hpullB t


end FsFltz.Geometry.IntrinsicZeroLiouville
