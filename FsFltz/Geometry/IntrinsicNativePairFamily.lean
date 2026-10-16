import FsFltz.Geometry.IntrinsicLiouvilleBoundaryFamily
import FsFltz.Geometry.IntrinsicRibbonFamily
import FsFltz.Geometry.IntrinsicPairFamilyTransport
import FsFltz.Geometry.IntrinsicLiouvilleBoundaryPresentation

/-!
# Completed pair families from original native ambient and ribbon data

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–814.
Both native primitive families, native ribbon map germs and native positive
boundary witness germs produce one actual smooth pair deformation. Fixed
boundary transport is derived from the same ambient compact inclusion.
The final compact presentations preserve both original primitives on full
native tangent spaces, the boundary inclusion square, every ribbon point,
every boundary witness value and the full core of the constructed completion.

This is a foundation on fixed native manifolds. Arbitrary bundle
trivialization and the target-specific geometric comparison remain pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original joint native data construct an actual completed pair family.
The two full native primitives, boundary square, witness and ribbon map are
retained on the same produced pairs, with no supplied extension presentation
or completion-family certificate. -/
theorem exists_intrinsic_pairDeformation_with_native_coherence_and_coordinates
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
  have hpresentation : ∀ (r : ℕ) [NeZero r], a + 1 = r →
      ∃ (D : CompactDomain r) (iA : A → D.extension.Point)
        (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ r) A D.Point ∞)
        (L : Parameter → LiouvilleStructure D)
        (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv D.boundary),
        (∀ x, (eA x).val = iA x) ∧
        D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
        (∀ t, (fun x => ((L t).primitive (iA x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model r) iA x)) = lam t) ∧
        (∀ x, D.boundaryInclusion.map (eB x) = iA x.val) ∧
        (∀ t, (IntrinsicBoundary.smoothManifold a A).pullback D.boundary eB
          (D.boundaryForm (L t).primitive) = IntrinsicBoundary.restrictForm (lam t)) ∧
        HasNativeCoordinateExtensions (k := a) D.extension iA := by
    intro r _ hr
    subst r
    obtain ⟨D, iA, eA, L, eB, heA, _, _, _, _, _, hL, _, hpullA, _, _, _, _, hcoordA, hBinclusion, hpullB⟩ :=
      exists_liouvilleFamily_with_native_boundary_presentation_and_coordinates lam hlam hAnd hAout
    exact ⟨D, iA, eA, L, eB, heA, hL, hpullA, hBinclusion, hpullB, hcoordA⟩
  obtain ⟨D, iA, eA, L, eB, heA, hL, hpullA, hBinclusion, hpullB, hcoordA⟩ :=
    hpresentation (2 * n) hdimA
  let j' : Parameter → M → D.boundary.Point := fun t => eB ∘ j t
  let b' : Parameter → D.boundary.Point → ℝ := fun t => b t ∘ eB.symm
  have hjs' : IsLocallyExtendibleMapFamily (k := k) D.boundary j' :=
    hjs.comp_contMDiff (IntrinsicBoundary.smoothManifold a A) D.boundary j eB eB.contMDiff
  have hjinj' (t : Parameter) : Function.Injective (j' t) := eB.injective.comp (hjinj t)
  have hjimm' (t : Parameter) (x : M) : Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j' t) x) := by
    rw [mfderiv_comp x (eB.contMDiff.mdifferentiableAt (by simp))
      ((hjs.contMDiff_slice (IntrinsicBoundary.smoothManifold a A) j t).mdifferentiableAt (by simp))]
    exact (eB.mfderivToContinuousLinearEquiv (by simp) (j t x)).injective.comp (hjimm t x)
  have hb' : D.boundary.IsLocallyExtendibleIntervalScalarFamily b' :=
    hb.comp_contMDiff D.boundary (IntrinsicBoundary.smoothManifold a A) b eB.symm eB.symm.contMDiff
  have hpositive' (t : Parameter) (x : D.boundary.Point) : 0 < b' t x := hpositive t (eB.symm x)
  have hribbon' (t : Parameter) (x : M) :
      ((b' t (j' t x) • D.boundaryForm (L t).primitive (j' t x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j' t) x) = μ t x := by
    have hd := mfderiv_comp (f := j t) (g := eB) x
      (eB.contMDiff.mdifferentiableAt (by simp))
      ((hjs.contMDiff_slice (IntrinsicBoundary.smoothManifold a A) j t).mdifferentiableAt (by simp))
    have hform := congrFun (hpullB t) (j t x)
    rw [← hribbon t x]
    ext vs
    change b t (eB.symm (eB (j t x))) * D.boundaryForm (L t).primitive (eB (j t x))
        (fun u => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (eB ∘ j t) x (vs u)) =
      b t (j t x) * IntrinsicBoundary.restrictForm (lam t) (j t x)
        (fun u => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) (j t) x (vs u))
    rw [eB.symm_apply_apply, hd, ← hform]
    rfl
  obtain ⟨Q, aA, RA₀, hRA₀, hAsquare, aB, hBsquare, eMs, RM, hRM, hMsquare, hQ⟩ :=
    exists_native_pairDeformation_on_fixed_ambient_with_native_coherence_and_coordinates
    hdimM D L hL μ hμ hMnd hMout j' hjs' hjinj' hjimm' b' hb' hpositive' hribbon'
  let eAs := fun t => eA.trans (aA t)
  let eBs := fun t => eB.trans (aB t)
  let RA := fun t : ℝ => (eA.trans (RA₀ t)).trans eA.symm
  refine ⟨Q, eAs, eMs, eBs, RA, RM, hRA₀.conjugate eA RA₀, hRM, ?_, hMsquare, ?_, ?_⟩
  · intro t x
    change (Q.ambientPresentation t).extensionEquiv
      ((aA parameterZero (eA (eA.symm (RA₀ t.val (eA x))))).val) = (aA t (eA x)).val
    rw [eA.apply_symm_apply]
    exact hAsquare t (eA x)
  · intro t x
    exact hBsquare t (eB x)
  · intro t
    obtain ⟨C, hC, hAQ, hBQ, aQ, haQ, hQB, hjM, himage, hwitness, hboundary, hμP, hcore, hcoordM⟩ := hQ t
    dsimp only [eAs, eBs]
    generalize haAt : aA t = aAt at *
    generalize hbAt : aB t = aBt at *
    generalize hmAt : eMs t = eM at *
    change let P := Q.pair t;
      (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eB.trans aBt) x) = ((eA.trans aAt) x.val).val) ∧
      (∀ x, (P.ambientDomain.liouville.primitive ((eA.trans aAt) x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eA.trans aAt) y).val) x) = lam t x) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary (eB.trans aBt)
        (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
          IntrinsicBoundary.restrictForm (lam t) ∧
      (∀ x, P.ribbonEmbedding.map (eM x).val = (eB.trans aBt) (j t x)) ∧
      (∀ x, P.witness ((eB.trans aBt) x) = b t x) ∧
      (∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ t x) ∧
      P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eB.trans aBt) '' range (j t) ∧
      P.embeddedCore = (fun x => (eB.trans aBt) (j t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
        P.ribbonCompletion.ambient.completeFlow.flow s
          (P.ribbonCompletion.inclusion.map (eM x).val) ∈
            range (fun y => P.ribbonCompletion.inclusion.map (eM y).val)} ∧
      HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eA.trans aAt) x).val) ∧
      HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => (eM x).val)
    clear hQ hAsquare hBsquare hMsquare haAt hbAt hmAt eAs eBs aA aB eMs
    generalize hPt : Q.pair t = P at *
    cases P
    dsimp only at hC
    cases hC
    have haQ' := eq_of_heq haQ
    subst aQ
    have hAQ' := eq_of_heq hAQ
    have hBQ' := eq_of_heq hBQ
    let eAP := eA.trans C.originalPointDiffeomorph.symm
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    rw [hAQ', hBQ']
    have heAP (x : A) : (eAP x).val.val.val = iA x := by
      have h := congrArg Subtype.val (C.originalPointDiffeomorph.apply_symm_apply (eA x))
      exact h.trans (heA x)
    have hprimitiveAP : ∀ x,
        (C.localizedDomain.liouville.primitive (eAP x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAP y).val) x) = lam t x := by
      apply native_primitive_localizedDomain ⟨D, L t⟩ C eA (lam t)
      intro x
      rw [heA x, show (fun y => (eA y).val) = iA from funext heA]
      exact congrFun (hpullA t) x
    refine ⟨?_, hprimitiveAP, ?_, hjM, ?_, hμP, ?_, ?_, ?_, hcoordM⟩
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      exact (hBinclusion x).trans (heAP x.val).symm
    · change (IntrinsicBoundary.smoothManifold a A).pullback D.boundary eB
        (C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive) = _
      rw [C.localized_boundaryForm]
      exact hpullB t
    · intro x
      exact (congrFun hwitness (eB x)).trans (congrArg (b t) (eB.symm_apply_apply x))
    · change id ∘ _ '' _ = _ at himage
      rw [Function.id_comp] at himage
      rw [himage]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨j t x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    · change id '' _ = _ at hcore
      rw [image_id] at hcore
      exact hcore
    · exact hcoordA.of_smooth_square D.extension C.localizedDomain.domain.extension iA
        (fun x => (eAP x).val) C.originalInclusion.map C.originalInclusion.map.contMDiff heAP

/-- The coherence interface forgetting only the retained endpoint coordinate germs. -/
theorem exists_intrinsic_pairDeformation_with_native_coherence
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
            range (fun y => P.ribbonCompletion.inclusion.map ((eMs t) y).val)} := by
  obtain ⟨Q, eA, eM, eB, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ⟩ :=
    exists_intrinsic_pairDeformation_with_native_coherence_and_coordinates
      hdimA hdimM lam hlam hAnd hAout μ hμ hMnd hMout j hjs hjinj hjimm b hb hpositive hribbon
  refine ⟨Q, eA, eM, eB, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, ?_⟩
  intro t
  obtain ⟨hB, hA, hBA, hjQ, hbQ, hM, himage, hcore, _, _⟩ := hQ t
  exact ⟨hB, hA, hBA, hjQ, hbQ, hM, himage, hcore⟩

/-- Original joint native data construct an actual completed pair family.
The two full native primitives, boundary square, witness and ribbon map are
retained on the same produced pairs, with no supplied extension presentation
or completion-family certificate. -/
theorem exists_intrinsic_pairDeformation
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
    ∃ Q : PairDeformation n, ∀ t : Parameter,
    let P := Q.pair t
    ∃ (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A P.ambientDomain.domain.Point ∞)
      (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv P.ambientDomain.domain.boundary),
      (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val) ∧
      (∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA y).val) x) = lam t x) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary eB
        (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
          IntrinsicBoundary.restrictForm (lam t) ∧
      (∀ x, P.ribbonEmbedding.map (eM x).val = eB (j t x)) ∧
      (∀ x, P.witness (eB x) = b t x) ∧
      (∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ t x) ∧
      P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = eB '' range (j t) ∧
      P.embeddedCore = (fun x => eB (j t x)) '' {x | ∀ t : ℝ, 0 ≤ t →
        P.ribbonCompletion.ambient.completeFlow.flow t
          (P.ribbonCompletion.inclusion.map (eM x).val) ∈
            range (fun y => P.ribbonCompletion.inclusion.map (eM y).val)} := by
  obtain ⟨Q, eA, eM, eB, RA, RM, hRA, hRM, hsquareA, hsquareM, hsquareB, hQ⟩ :=
    exists_intrinsic_pairDeformation_with_native_coherence hdimA hdimM lam hlam hAnd hAout
      μ hμ hMnd hMout j hjs hjinj hjimm b hb hpositive hribbon
  exact ⟨Q, fun t => ⟨eA t, eM t, eB t, hQ t⟩⟩

end FsFltz.Geometry.IntrinsicLiouville
