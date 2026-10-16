import FsFltz.Geometry.NativePairCompletionCoherence

/-!
# Completion coherence for original rank-one pairs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 127–160, especially
159–160; `def:chain`, lines 163–199; and `sec:lean`, lines 788–814 and
825–830. The same native ambient primitive constructs the strict ambient
comparison on two independently prescribed pairs. Their original native
boundary and entire finite-ribbon squares determine the boundary/ribbon
compatibility, zero radial shift and equality of the full boundary witness.

The finite ribbon has zero one-form, so neither ribbon primitive laws nor
ribbon coordinate germs need to be supplied. Empty ribbons are allowed.
These are conditional changes of presentation on exact original pairs;
they do not prove the target's full-fiber markings, chain or grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.CompletionIdentification
open IntrinsicLiouville SmoothManifold

variable {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]
  [TopologicalSpace M] [ChartedSpace (Model 0) M]

/-- The independently prescribed rank-one pairs represent the same native
ambient, entire zero-dimensional ribbon and boundary witness. Construct a
permitted identification on those exact pairs with scale one and zero shift,
retaining the ambient compact and all-real end squares. No completed map,
ribbon primitive or ribbon coordinate extension is supplied as a premise. -/
theorem exists_of_same_native_zero_pair
    (P Q : WitnessedPair 1)
    (lam : Form 1 A 1) (hlam : IsLocallyExtendibleForm lam)
    (hAnd : ∀ x, Nondegenerate (exteriorDerivative lam) x)
    (hAout : ∀ x : IntrinsicBoundary.Point 1 A,
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector lam (exteriorDerivative lam) x.val)))
    (eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞)
    (eA' : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A Q.ambientDomain.domain.Point ∞)
    (eM : letI := P.ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞)
    (eM' : letI := Q.ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M Q.ribbonDomain.domain.Point ∞)
    (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv P.ambientDomain.domain.boundary)
    (eB' : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv Q.ambientDomain.domain.boundary)
    (hpA : ∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eA y).val) x) = lam x)
    (hpA' : ∀ x, (Q.ambientDomain.liouville.primitive (eA' x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eA' y).val) x) = lam x)
    (hcA : HasNativeCoordinateExtensions (k := 1)
      P.ambientDomain.domain.extension (fun x => (eA x).val))
    (hcA' : HasNativeCoordinateExtensions (k := 1)
      Q.ambientDomain.domain.extension (fun x => (eA' x).val))
    (hB : ∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val)
    (hB' : ∀ x, Q.ambientDomain.domain.boundaryInclusion.map (eB' x) = (eA' x.val).val)
    (j : M → IntrinsicBoundary.Point 1 A)
    (hj : ∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x))
    (hj' : ∀ x, Q.ribbonEmbedding.map (eM' x).val = eB' (j x))
    (b : IntrinsicBoundary.Point 1 A → ℝ)
    (hb : ∀ x, P.witness (eB x) = b x)
    (hb' : ∀ x, Q.witness (eB' x) = b x) :
    ∃ I : CompletionIdentification P Q,
      I.scale = 1 ∧
      (∀ x, I.ribbonEquiv.map (eM x).val = (eM' x).val) ∧
      (∀ x, I.ribbonEquiv.inverse (eM' x).val = (eM x).val) ∧
      (∀ x, I.boundaryEquiv (eB x) = eB' x) ∧
      (∀ x, I.shift x = 0) ∧
      (∀ x, Q.witness (I.boundaryEquiv x) = P.witness x) ∧
      (∀ x, I.ambientEquiv (P.ambientCompletion.inclusion.map (eA x).val) =
        Q.ambientCompletion.inclusion.map (eA' x).val) ∧
      (∀ x, I.ambientEquiv.symm (Q.ambientCompletion.inclusion.map (eA' x).val) =
        P.ambientCompletion.inclusion.map (eA x).val) ∧
      (∀ x r, I.ambientEquiv (P.ambientCompletion.endMap (eB x, r)) =
        Q.ambientCompletion.endMap (eB' x, r)) := by
  obtain ⟨f, hf, hcompact, hinverse, hend⟩ :=
    exists_strictNativeComparison_with_boundary_square rfl
      P.ambientDomain Q.ambientDomain P.ambientCompletion Q.ambientCompletion
      lam hlam hAnd hAout eA eA' hpA hpA' hcA hcA' eB eB' hB hB'
  obtain ⟨g, hg, hgi, hgp⟩ := IntrinsicZeroLiouville.exists_originalNativeCompactDiffeomorph
    P.ribbonDomain Q.ribbonDomain P.ribbonCompletion Q.ribbonCompletion eM eM'
    (Diffeomorph.refl 𝓘(ℝ, Model 0) M ∞) 1
  have htrajectory (z : P.ribbonDomain.domain.extension.Point)
      (hz : z ∈ P.ribbonDomain.domain.carrier) : ∃ r : ℝ,
      f (P.ambientCompletion.endMap (P.ribbonEmbedding.map z, 0)) =
        Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (g.map z), r) := by
    obtain ⟨x, hx⟩ := eM.surjective ⟨z, hz⟩
    have hx' : (eM x).val = z := congrArg Subtype.val hx
    refine ⟨0, ?_⟩
    rw [← hx', hg]
    change f (P.ambientCompletion.endMap (P.ribbonEmbedding.map (eM x).val, 0)) =
      Q.ambientCompletion.endMap (Q.ribbonEmbedding.map (eM' x).val, 0)
    rw [hj, hj']
    exact hend (j x) 0
  obtain ⟨I, hIf, hIg, hc⟩ := exists_of_ribbon_trajectory_square P Q f hf g 1
    (by norm_num) hgp htrajectory
  have hboundary (x : IntrinsicBoundary.Point 1 A) : I.boundaryEquiv (eB x) = eB' x := by
    obtain ⟨r0, hr⟩ := I.induced_at_infinity (eB x)
    have he := hr r0 le_rfl
    rw [hIf, hend] at he
    exact (congrArg Prod.fst (Q.ambientCompletion.endMap_injective he)).symm
  have hshift (z : P.ambientDomain.domain.boundary.Point) : I.shift z = 0 := by
    obtain ⟨x, rfl⟩ := eB.surjective z
    obtain ⟨r0, hr⟩ := I.induced_at_infinity (eB x)
    have he := hr r0 le_rfl
    rw [hIf, hend] at he
    have hs := congrArg Prod.snd (Q.ambientCompletion.endMap_injective he)
    dsimp only at hs
    change I.shift (eB x) = 0
    linarith
  refine ⟨I, hc, ?_, ?_, hboundary, hshift, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hIg]
    exact hg x
  · intro x
    rw [hIg]
    exact hgi x
  · intro z
    obtain ⟨x, rfl⟩ := eB.surjective z
    change Q.witness (I.boundaryEquiv (eB x)) = P.witness (eB x)
    rw [hboundary, hb, hb']
  · simpa only [hIf] using hcompact
  · simpa only [hIf] using hinverse
  · simpa only [hIf] using hend

end FsFltz.Geometry.CompletionIdentification

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open IntrinsicLiouville SmoothManifold

variable {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Original native zero-ribbon families construct one actual completed pair
deformation. Every prescribed original slice with the same full native data
is identified with that very generated slice. The original producer's joint
native coherence, primitives, full cores and ambient coordinates are retained.
The two endpoint identifications and this same deformation give an explicit
three-step comparison chain on the original endpoints.

The identifications are pointwise in the parameter. Their joint regularity
on the original completed total spaces and ambient grading transport remain
separate foundations. -/
theorem exists_native_zero_pairDeformation_with_original_slice_identifications
    (α : Parameter → Form 1 A 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point 1 A),
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → IntrinsicBoundary.Point 1 A)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : IsLocallyExtendibleRibbonMapFamily (IntrinsicBoundary.smoothManifold 1 A) j)
    (b : Parameter → IntrinsicBoundary.Point 1 A → ℝ)
    (hb : (IntrinsicBoundary.smoothManifold 1 A).IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (O : Parameter → WitnessedPair 1)
    (eAO : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A (O t).ambientDomain.domain.Point ∞)
    (eMO : ∀ t, letI := (O t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (O t).ribbonDomain.domain.Point ∞)
    (eBO : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
      (O t).ambientDomain.domain.boundary)
    (hpAO : ∀ t x, ((O t).ambientDomain.liouville.primitive (eAO t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAO t y).val) x) = α t x)
    (hcAO : ∀ t, HasNativeCoordinateExtensions (k := 1)
      (O t).ambientDomain.domain.extension (fun x => (eAO t x).val))
    (hBO : ∀ t x, (O t).ambientDomain.domain.boundaryInclusion.map (eBO t x) = (eAO t x.val).val)
    (hjO : ∀ t x, (O t).ribbonEmbedding.map (eMO t x).val = eBO t (j t x))
    (hbO : ∀ t x, (O t).witness (eBO t x) = b t x) :
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
        HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val) ∧
        ∃ I : CompletionIdentification (O t) P,
          I.scale = 1 ∧
          (∀ x, I.ribbonEquiv.map (eMO t x).val = (eMs t x).val) ∧
          (∀ x, I.ribbonEquiv.inverse (eMs t x).val = (eMO t x).val) ∧
          (∀ x, I.boundaryEquiv (eBO t x) = eBs t x) ∧
          (∀ x, I.shift x = 0) ∧
          (∀ x, P.witness (I.boundaryEquiv x) = (O t).witness x) ∧
          (∀ x, I.ambientEquiv ((O t).ambientCompletion.inclusion.map (eAO t x).val) =
            P.ambientCompletion.inclusion.map (eAs t x).val) ∧
          (∀ x, I.ambientEquiv.symm (P.ambientCompletion.inclusion.map (eAs t x).val) =
            (O t).ambientCompletion.inclusion.map (eAO t x).val) ∧
          (∀ x r, I.ambientEquiv ((O t).ambientCompletion.endMap (eBO t x, r)) =
            P.ambientCompletion.endMap (eBs t x, r))) ∧
      ∃ (I₀ : CompletionIdentification (O parameterZero) Q.source)
        (I₁ : CompletionIdentification (O parameterOne) Q.target)
        (path : ComparisonChain (O parameterZero) (O parameterOne)),
        path = Q.originalEndpointChain I₀ I₁ ∧ path.length = 3 ∧
        I₀.scale = 1 ∧ I₁.scale = 1 ∧
        (∀ x, Q.source.witness (I₀.boundaryEquiv x) = (O parameterZero).witness x) ∧
        (∀ x, Q.target.witness (I₁.boundaryEquiv x) = (O parameterOne).witness x) := by
  obtain ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAs, hMs, hBs, hQ⟩ :=
    exists_native_zero_pairDeformation_with_native_coherence_and_coordinates
      α hα hnd hout μ j hj hjs b hb hpositive
  have hslice (t : Parameter) :=
    let ⟨hB, hjQ, hbQ, _, hA, _, _, hcA⟩ := hQ t
    CompletionIdentification.exists_of_same_native_zero_pair (O t) (Q.pair t)
      (α t) (hα.slice t) (hnd t) (hout t)
      (eAO t) (eAs t) (eMO t) (eMs t) (eBO t) (eBs t)
      (hpAO t) hA (hcAO t) hcA (hBO t) hB (j t) (hjO t) hjQ (b t) (hbO t) hbQ
  refine ⟨Q, eAs, eMs, eBs, RA, RM, hRA, hRM, hAs, hMs, hBs, ?_, ?_⟩
  · intro t
    obtain ⟨hB, hjQ, hbQ, hcore, hA, hM, hBA, hcA⟩ := hQ t
    exact ⟨hB, hjQ, hbQ, hcore, hA, hM, hBA, hcA, hslice t⟩
  · obtain ⟨I₀, hI₀⟩ := hslice parameterZero
    obtain ⟨I₁, hI₁⟩ := hslice parameterOne
    exact ⟨I₀, I₁, Q.originalEndpointChain I₀ I₁, rfl, rfl,
      hI₀.1, hI₁.1, hI₀.2.2.2.2.2.1, hI₁.2.2.2.2.2.1⟩

end FsFltz.Geometry.IntrinsicZeroLiouville
