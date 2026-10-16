import FsFltz.Geometry.IntrinsicBoundaryCollarPrimitive
import FsFltz.Geometry.IntrinsicCollarCarrier

/-!
# Topological extension from the original intrinsic Liouville primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The source primitive and outwardness produce the same native
collar used to attach the boundary strip. Smooth gluing of the primitive and
a regular sublevel presentation are separate foundation results.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The original compact source data construct a Hausdorff second-countable
extension with its actual closed compact carrier. The collar and its full
primitive identity are exactly the witnesses used in the quotient; no
extension, topology, collar, or primitive identity is supplied as input. -/
theorem exists_topological_extension_with_primitive_collar
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
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y))
        (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      (∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q) ∧
      (∀ t ∈ Ico 0 δ, ∀ y : IntrinsicBoundary.Point k M, ∀ r : ℝ,
        ∀ v : TangentSpace 𝓘(ℝ, Model k) y,
          α (C (t, y)) (fun _ =>
            mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) C
              (Ico 0 δ ×ˢ univ) (t, y) (r, v)) =
            Real.exp (-t) * α y.val (fun _ =>
              mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
                (Subtype.val : IntrinsicBoundary.Point k M → M) y v)) ∧
      let c : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) → M :=
        fun p => C p.val
      T2Space (IntrinsicCollarGluing.Extension c) ∧
      SecondCountableTopology (IntrinsicCollarGluing.Extension c) ∧
      Topology.IsClosedEmbedding (IntrinsicCollarGluing.original c) ∧
      IsCompact (range (IntrinsicCollarGluing.original c)) ∧
      Topology.IsOpenEmbedding (IntrinsicCollarGluing.cylinder c) ∧
      Topology.IsOpenEmbedding (IntrinsicCollarGluing.interiorIn c) ∧
      interior (range (IntrinsicCollarGluing.original c)) =
        range (IntrinsicCollarGluing.interiorIn c) ∧
      frontier (range (IntrinsicCollarGluing.original c)) =
        IntrinsicCollarGluing.original c '' (𝓡∂ (k + 1)).boundary M := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, hprim⟩ :=
    exists_uniform_collar_with_primitive_of_localDefiningFunction_outward α hα hnd hout
  refine ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, hprim, ?_⟩
  let c : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) → M :=
    fun p => C p.val
  have hb : ∀ p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (c p) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  exact ⟨IntrinsicCollarGluing.t2Space_extension hδ c hemb,
    IntrinsicCollarGluing.secondCountableTopology_extension hδ c hemb hb hzero,
    IntrinsicCollarGluing.isClosedEmbedding_original hδ c hemb,
    IntrinsicCollarGluing.isCompact_range_original c,
    IntrinsicCollarGluing.isOpenEmbedding_cylinder hδ c hemb,
    IntrinsicCollarGluing.isOpenEmbedding_interiorIn hδ c hemb hb,
    IntrinsicCollarGluing.interior_range_original hδ c hemb hb hzero,
    IntrinsicCollarGluing.frontier_range_original hδ c hemb hb hzero⟩

end FsFltz.Geometry.IntrinsicLiouville
