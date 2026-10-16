import FsFltz.Geometry.IntrinsicLiouvilleCollar
import FsFltz.Geometry.IntrinsicCollarSeam

/-!
# Scalar seam extension from native Liouville source data

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–127, `def:pair`, lines 132–160, and `sec:lean`, lines 783–814.
An actually extendible primitive and its nondegenerate exterior derivative
produce the field coefficient germs. The canonical source outward
inequality produces inwardness. Applying the same-collar seam theorem then
extends an additional source scalar smoothly across the seam.

This is a local foundation producer; it does not assert primitive gluing,
a complete flow, or any geometric endpoint conclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native primitive smoothness, actual exterior nondegeneracy, and the
source outward inequality supply the scalar extension germ on the same
Liouville collar. Field coefficient extensions and matching two-sided
collar germs are proved rather than assumed. Smoothness holds at order
infinity on one explicit open neighborhood. -/
theorem exists_seam_scalar_germ_of_primitive
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ z, Nondegenerate (exteriorDerivative α) z)
    (x : IntrinsicBoundary.Point k M)
    (hout : 0 < (show ℝ from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ y, C (0, y) = y.val)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y))
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (φ : M → ℝ)
    (hφ : ∃ (β : Model (k + 1) → ℝ) (A : Set (Model (k + 1))),
      IsOpen A ∧ (IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val ∈ A ∧
      ContDiffOn ℝ ∞ β A ∧
      β =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
        ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
        (fun z => φ (((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm z))) :
    ∃ (a : ℝ × IntrinsicBoundary.Point k M → ℝ)
      (W : Set (ℝ × IntrinsicBoundary.Point k M)),
      IsOpen W ∧ (0, x) ∈ W ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ) ∞ a W ∧
      EqOn a (fun p => φ (C p)) (W ∩ (Ico 0 δ ×ˢ univ)) := by
  let c := IntrinsicBoundary.chartAt x
  have hx : x ∈ c.chart.source := IntrinsicBoundary.mem_chartAt_source x
  have hex : x.val ∈ c.ambient.source := by
    have h := hx
    rwa [c.source_eq] at h
  apply IntrinsicCollar.exists_seam_scalar_germ_of_scalar_extensions c hx
    (fun z => -liouvilleVector α (exteriorDerivative α) z) C hδ hzero hode
  · exact inward_liouvilleVector_scalar_extensions_of_primitive α hα hnd
      c.ambient c.mem_atlas x.val hex
  · exact inward_of_normalDefiningFunction_outward c.mem_atlas hex
      (liouvilleVector α (exteriorDerivative α)) hout
  · exact hφ

end FsFltz.Geometry.IntrinsicLiouville
