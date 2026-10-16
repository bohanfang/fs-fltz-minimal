import FsFltz.Geometry.IntrinsicLiouvilleCoefficients
import FsFltz.Geometry.IntrinsicLiouvilleOutward
import FsFltz.Geometry.IntrinsicExteriorDerivative
import FsFltz.Geometry.IntrinsicCollarCompact

/-!
# Compact native collars from intrinsic Liouville primitives

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Local smooth primitive extensions determine the
actual exterior derivative and the unique native Liouville field. Smooth
field coefficient germs and the positive-width compact collar are produced.
Outwardness here uses the specified canonical local defining function in
the preferred chart. Equivalence with arbitrary regular defining functions
is a separate sign-conversion lemma.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [T2Space M] in
/-- A locally extendible primitive and its pointwise nondegenerate actual
exterior derivative produce the inward scalar extension germs required
by the native compact collar theorem. -/
theorem inward_liouvilleVector_scalar_extensions_of_primitive
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x) :
    ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
      e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∀ i : Fin (k + 1),
        ∃ (f : Model (k + 1) → ℝ) (V : Set (Model (k + 1))),
          IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
          f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target] (e.extend (𝓡∂ (k + 1)) x)]
            (fun y => (show Model (k + 1) from
              mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
                (e.extend (𝓡∂ (k + 1))) ((e.extend (𝓡∂ (k + 1))).symm y)
                  (-liouvilleVector α (exteriorDerivative α)
                    ((e.extend (𝓡∂ (k + 1))).symm y))) i) :=
  inward_liouvilleVector_scalar_extensions α (exteriorDerivative α) hα
    (hasExteriorDerivative_exteriorDerivative α hα) hnd

/-- Actual primitive data construct a compact native collar for the negative
Liouville field once its preferred native normal coefficient is positive.
No field germ, flow, collar, inverse, or injectivity data are hypotheses. -/
theorem exists_uniform_collar_of_primitive
    [CompactSpace (IntrinsicBoundary.Point k M)]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hin : ∀ x : IntrinsicBoundary.Point k M,
      0 < (show Model (k + 1) from
        chartTangentMap (IntrinsicBoundary.chartAt x).ambient x.val
          (-liouvilleVector α (exteriorDerivative α) x.val)) 0) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y))
        (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      ∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q :=
  IntrinsicCollar.exists_uniform_native_collar_of_scalar_extensions
    (fun x => -liouvilleVector α (exteriorDerivative α) x)
    (inward_liouvilleVector_scalar_extensions_of_primitive α hα hnd) hin

/-- The source's outward inequality, measured using the canonical genuine
local defining function in the preferred chart, constructs the same compact
native collar. The inward coefficient inequality is derived. -/
theorem exists_uniform_collar_of_normal_outward
    [CompactSpace (IntrinsicBoundary.Point k M)]
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
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
      ∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q := by
  apply exists_uniform_collar_of_primitive α hα hnd
  intro x
  let c := IntrinsicBoundary.chartAt x
  have hx : x.val ∈ c.ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source x
    rw [c.source_eq] at h
    exact h
  exact inward_of_normalDefiningFunction_outward c.mem_atlas hx
    (liouvilleVector α (exteriorDerivative α)) (hout x)

end FsFltz.Geometry.IntrinsicLiouville
