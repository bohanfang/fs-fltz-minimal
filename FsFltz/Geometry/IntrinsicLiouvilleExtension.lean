import FsFltz.Geometry.IntrinsicLiouvilleCoordinates

/-!
# Local extension of intrinsic exterior derivatives

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–130, and `sec:lean`, lines 783–814. Differentiating local open
extensions of a primitive produces actual smooth derivative coefficient germs
within each native half-space chart, including its boundary.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Differentiating the actual local primitive extension gives a local smooth
extension of the exterior-derivative coefficients, including boundary points. -/
theorem exists_exteriorDerivative_extension {r : ℕ}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {α : Form k M r} {omega : Form k M (r + 1)} (hd : HasExteriorDerivative α omega)
    {x : M}
    {β : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ}
    {U : Set (Model (k + 1))} (hU : IsOpen U)
    (haU : e.extend (𝓡∂ (k + 1)) x ∈ U) (hβ : ContDiffOn ℝ ∞ β U)
    (hag : β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) x)] formInChart e α) :
    ContDiffOn ℝ ∞ (extDeriv β) U ∧
      extDeriv β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
        (e.extend (𝓡∂ (k + 1)) x)] formInChart e omega := by
  have hD : ContDiffOn ℝ ∞ (extDeriv β) U := by
    have halt : ContDiff ℝ ∞
        (ContinuousAlternatingMap.alternatizeUncurryFinCLM
          (n := r) ℝ (Model (k + 1)) ℝ :
            (Model (k + 1) →L[ℝ] Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ) →
              Model (k + 1) [⋀^Fin (r + 1)]→L[ℝ] ℝ) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := Model (k + 1) →L[ℝ] Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ)
        (F := Model (k + 1) [⋀^Fin (r + 1)]→L[ℝ] ℝ)
        (ContinuousAlternatingMap.alternatizeUncurryFinCLM
          (n := r) ℝ (Model (k + 1)) ℝ)
    exact halt.comp_contDiffOn (hβ.fderiv_of_isOpen hU (by simp))
  refine ⟨hD, ?_⟩
  filter_upwards [hag.extDerivWithin,
    mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU), self_mem_nhdsWithin] with y hy hyU hyt
  rw [hd e he y hyt, ← hy]
  unfold extDerivWithin extDeriv
  rw [((hβ.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).fderivWithin
    (uniqueDiffOn_chart_target e y hyt)]

end FsFltz.Geometry.IntrinsicLiouville
