import FsFltz.Geometry.Smooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Chartwise vector fields as native tangent-bundle sections

The smooth vector fields of `geoemtric-part-fsf.tex`, `def:pair`, lines
119–158, are represented using actual chart derivatives. This bridge to the
native tangent bundle supports the flow foundations in `sec:lean`, 805–814.
-/

noncomputable section
open scoped Manifold ContDiff
open Topology

namespace FsFltz.Geometry.SmoothManifold

/-- The chartwise smoothness predicate implies smoothness as a section of
Mathlib's actual tangent bundle. -/
theorem IsSmoothVectorField.contMDiff_section {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (hZ : M.IsSmoothVectorField Z) :
    ContMDiff (𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d))) ∞
      (fun x => (⟨x, Z x⟩ : TangentBundle (𝓘(ℝ, Model d)) M.Point)) := by
  intro a
  rw [Bundle.contMDiffAt_section]
  have ha := mem_chart_source (Model d) a
  have ht := (chartAt (Model d) a).map_source ha
  have hcoeff := (hZ a).contDiffAt ((chartAt (Model d) a).open_target.mem_nhds ht)
  have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
    ((chartAt (Model d) a).open_source.mem_nhds ha)
  apply (hcoeff.contMDiffAt.comp a hchart).congr_of_eventuallyEq
  filter_upwards [(chartAt (Model d) a).open_source.mem_nhds ha] with x hx
  dsimp only [Function.comp_def, vectorInChart]
  rw [(chartAt (Model d) a).left_inv hx]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ) (trivializationAt (Model d) (TangentSpace (𝓘(ℝ, Model d))) a) hx]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

/-- Conversely, a native smooth section has the prescribed smooth chart
coefficients on every chart target. -/
theorem isSmoothVectorField_of_contMDiff_section {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x}
    (hZ : ContMDiff (𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d))) ∞
      (fun x => (⟨x, Z x⟩ : TangentBundle (𝓘(ℝ, Model d)) M.Point))) :
    M.IsSmoothVectorField Z := by
  intro a y hy
  let e := trivializationAt (Model d) (TangentSpace (𝓘(ℝ, Model d))) a
  have hx := (chartAt (Model d) a).map_target hy
  have hcoeff := (e.contMDiffAt_section_iff hx).mp (hZ ((chartAt (Model d) a).symm y))
  have hchart := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (n := ∞) (x := a)).contMDiffAt
    ((chartAt (Model d) a).open_target.mem_nhds hy)
  apply ((hcoeff.comp y hchart).contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(chartAt (Model d) a).open_target.mem_nhds hy] with z hz
  dsimp only [Function.comp_def, vectorInChart]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℝ) e ((chartAt (Model d) a).map_target hz)]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    ((chartAt (Model d) a).map_target hz)]
  rfl

/-- Exact agreement of the project and native meanings of a smooth field. -/
theorem isSmoothVectorField_iff_contMDiff_section {d : ℕ} {M : SmoothManifold d}
    (Z : (x : M.Point) → M.Tangent x) :
    M.IsSmoothVectorField Z ↔
      ContMDiff (𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).prod (𝓘(ℝ, Model d))) ∞
        (fun x => (⟨x, Z x⟩ : TangentBundle (𝓘(ℝ, Model d)) M.Point)) :=
  ⟨IsSmoothVectorField.contMDiff_section, isSmoothVectorField_of_contMDiff_section⟩

end FsFltz.Geometry.SmoothManifold
