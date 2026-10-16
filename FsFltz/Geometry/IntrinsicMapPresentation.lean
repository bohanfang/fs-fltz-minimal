import FsFltz.Geometry.IntrinsicMapExtension

/-!
# Native compact presentations carrying manifold-valued map extensions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–161, and
`sec:lean`, lines 783–814. The compact presentation is constructed from
the native primitive before choosing any additional source-smooth map.
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

/-- Source primitive and outwardness data select a single actual compact
domain presentation with its native carrier diffeomorphism before any additional
map or scalar is chosen. Every source-smooth scalar extends globally, and
every source-smooth map to any finite-dimensional target extends on an open
neighborhood of the whole carrier in this same presentation. The neighborhood
may depend on the map; no global target-valued extension is asserted.
This finite foundation result asserts no completion or comparison chain. -/
theorem exists_compactDomain_with_native_primitive_and_map_extensions
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧ frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      (∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : D.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x) ∧
      ∀ (d : ℕ) (N : SmoothManifold d) (f : M → N.Point),
        IsLocallyExtendibleMap (k := k) (F := Model d) f →
        ∃ (W : TopologicalSpace.Opens D.extension.Point) (hW : range i ⊆ W)
          (g : W → N.Point),
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ g ∧
          ∀ x, g ⟨i x, hW ⟨x, rfl⟩⟩ = f x := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, _, _⟩ :=
    exists_topological_extension_with_primitive_collar α hα hnd hout
  let c : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) → M := fun p => C p.val
  have hb : ∀ p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  let D := IntrinsicCollarGluing.compactDomain hδ C hemb hC hb hinv hzero
  let i : M → D.extension.Point := IntrinsicCollarGluing.original c
  let lam : D.extension.Form 1 :=
    IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hb hinv hzero α
  have hZ := contraction_liouvilleVector α (exteriorDerivative α) hnd
  refine ⟨D, i, lam,
    IntrinsicCollarGluing.originalDiffeomorph hδ C hemb hC hb hinv hzero, fun _ => rfl,
    IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hb hinv hzero,
    IntrinsicCollarGluing.isClosedEmbedding_original hδ c hemb,
    IntrinsicCollarGluing.bijective_mfderiv_original hδ C hemb hC hb hinv hzero,
    rfl, IntrinsicCollarGluing.frontier_range_original hδ c hemb hb hzero,
    IntrinsicCollarGluing.isSmoothForm_gluedPrimitive hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode,
    IntrinsicCollarGluing.pullback_gluedPrimitive_original hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode, ?_⟩
  have houtnorm (b : IntrinsicBoundary.Point k M) :
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (liouvilleVector α (exteriorDerivative α) b.val)) := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, heq, hp⟩ := hout b
    have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    have hn := (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hx b.property rho hz hs hr hbeta heq
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hp
    rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas hx]
    exact neg_pos.mpr hn
  constructor
  · intro f hf
    exact IntrinsicCollarGluing.exists_scalarExtension_of_primitive_collar
      hδ C hemb hC hb hinv hzero α hα hnd houtnorm hode hf
  · intro d N f hf
    obtain ⟨W, hW, g, hg, heq⟩ :=
      IntrinsicCollarGluing.exists_mapExtension_of_primitive_collar
        hδ C hemb hC hb hinv hzero α hα hnd houtnorm hode hf
    exact ⟨W, hW, g, hg, fun x => heq x (hW ⟨x, rfl⟩)⟩


end FsFltz.Geometry.IntrinsicLiouville
