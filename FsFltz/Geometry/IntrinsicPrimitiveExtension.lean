import FsFltz.Geometry.IntrinsicLiouvilleGluing
import FsFltz.Geometry.IntrinsicCollarDomain
import FsFltz.Geometry.IntrinsicGluedFormRestriction

/-!
# Smooth primitive extension produced from the compact intrinsic source

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. A single collar produced from the source primitive and its
outwardness determines the smooth extension, compact-domain presentation,
and globally smooth primitive. The original primitive is preserved on the
entire native manifold, including its boundary. This finite result does not
assert symplecticity or a Liouville field on the extension.
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

/-- The original locally smooth primitive, nondegenerate derivative, and
outward local defining functions produce an actual compact-domain
presentation with a globally smooth primitive extending the entire source
primitive. No collar, atlas, primitive matching law, or domain presentation
is required as input. -/
theorem exists_compactDomain_with_smooth_primitive_extension
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1),
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, _, _⟩ :=
    exists_topological_extension_with_primitive_collar α hα hnd hout
  let c : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) → M :=
    fun p => C p.val
  have hb : ∀ p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  let D := IntrinsicCollarGluing.compactDomain hδ C hemb hC hb hinv hzero
  let i : M → D.extension.Point := IntrinsicCollarGluing.original c
  let lam : D.extension.Form 1 :=
    IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hb hinv hzero α
  have hZ := contraction_liouvilleVector α (exteriorDerivative α) hnd
  refine ⟨D, i, lam,
    IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hb hinv hzero,
    IntrinsicCollarGluing.isClosedEmbedding_original hδ c hemb,
    IntrinsicCollarGluing.bijective_mfderiv_original hδ C hemb hC hb hinv hzero,
    rfl,
    IntrinsicCollarGluing.frontier_range_original hδ c hemb hb hzero,
    IntrinsicCollarGluing.isSmoothForm_gluedPrimitive hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode,
    IntrinsicCollarGluing.pullback_gluedPrimitive_original hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode⟩

end FsFltz.Geometry.IntrinsicLiouville
