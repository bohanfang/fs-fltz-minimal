import FsFltz.Geometry.IntrinsicLiouvilleFamilyExtension
import FsFltz.Geometry.IntrinsicBoundaryPresentation

/-!
# One native boundary presentation for a Liouville family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The original native primitive family constructs one compact presentation,
one inclusion, and its fixed boundary equivalence. The full varying boundary
primitive is transported through that same equivalence at every parameter.
All interval geometric and smoothness assertions retain the original family.

The family presentation and localized completions are conclusions; no
completed presentation, boundary equivalence, or boundary-form identity is
supplied as a hypothesis. This does not trivialize arbitrary domain bundles
or assert the target-specific markings or geometric comparison chain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Original native ambient primitives construct one compact and boundary
presentation for the whole interval. The fixed boundary map transports the
actual restricted primitive at every parameter, including all tangents. -/
theorem exists_liouvilleFamily_with_native_boundary_presentation_and_coordinates
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞)
      (L : Parameter → LiouvilleStructure D)
      (eB : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, (fun x => ((L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α t) ∧
      (∀ t, (fun x => (D.extension.exteriorDerivative (L t).primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative (α t)) ∧
      (∀ t x, (L t).field (i x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector (α t) (exteriorDerivative (α t)) x)) ∧
      (∀ t, D.extension.IsSymplecticOn
        (D.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D L) ∧
      HasNativeCoordinateExtensions (k := k) D.extension i ∧
      (∀ x, D.boundaryInclusion.map (eB x) = i x.val) ∧
      (∀ t, (IntrinsicBoundary.smoothManifold k M).pullback D.boundary eB
        (D.boundaryForm (L t).primitive) = IntrinsicBoundary.restrictForm (α t)) := by
  obtain ⟨D, i, e, L, he, hi, hemb, hbij, hrange, hfrontier,
    hL, hF, hpull, hderiv, hfield, hglobal, hcompletion, hcoord⟩ :=
    exists_liouvilleFamily_with_native_presentation_and_coordinates α hα hnd hout
  let eB := boundaryPresentationEquiv D i hi hemb.injective (fun x => (hbij x).1) hfrontier
  refine ⟨D, i, e, L, eB, he, hi, hemb, hbij, hrange, hfrontier,
    hL, hF, hpull, hderiv, hfield, hglobal, hcompletion, hcoord, ?_, ?_⟩
  · exact boundaryPresentationEquiv_inclusion D i hi hemb.injective
      (fun x => (hbij x).1) hfrontier
  · intro t
    exact pullback_boundaryForm D i hi hemb.injective (fun x => (hbij x).1)
      hfrontier (α t) (L t).primitive (hpull t)

end FsFltz.Geometry.IntrinsicLiouville
