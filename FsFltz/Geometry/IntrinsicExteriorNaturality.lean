import FsFltz.Geometry.IntrinsicExteriorDerivative
import FsFltz.Geometry.ExteriorDerivative

/-!
# Exterior naturality from a boundaryless manifold to a native domain

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Pullback uses the actual manifold differential. At native
boundary points the chain rule and exterior derivative are computed within
the half-space chart range, whose derivatives are unique. No derivative
witness is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native coefficients of actual pullback from a boundaryless manifold.
The coordinate differential is taken within the native half-space range. -/
theorem formInChart_pullback_from_boundaryless {d r : ℕ}
    (N : SmoothManifold d) (f : M → N.Point) (eta : N.Form r)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (a : N.Point)
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hx : f ((e.extend (𝓡∂ (k + 1))).symm y) ∈ (chartAt (Model d) a).source)
    (hf : MDifferentiableAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f
      ((e.extend (𝓡∂ (k + 1))).symm y)) :
    formInChart e (fun x => (eta (f x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x)) y =
      (N.formInChart a eta ((chartAt (Model d) a ∘ f ∘
        (e.extend (𝓡∂ (k + 1))).symm) y)).compContinuousLinearMap
          (fderivWithin ℝ (chartAt (Model d) a ∘ f ∘
            (e.extend (𝓡∂ (k + 1))).symm) (range (𝓡∂ (k + 1))) y) := by
  have hci := mdifferentiableWithinAt_extend_symm
    (IsManifold.subset_maximalAtlas (n := (1 : WithTop ℕ∞)) he) hy
  have hce := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt hx
  have hs := uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr
    ((𝓡∂ (k + 1)).uniqueDiffOn y (e.extend_target_subset_range hy))
  rw [← mfderivWithin_eq_fderivWithin,
    mfderiv_comp_mfderivWithin y hce (hf.comp_mdifferentiableWithinAt y hci) hs,
    mfderiv_comp_mfderivWithin y hf hci hs]
  ext vs
  exact (congrArg (fun A => A (fun j =>
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f
      ((e.extend (𝓡∂ (k + 1))).symm y) (inverseChartTangentMap e y (vs j))))
    (N.formInChart_comp_chartTangentMap eta a
      (f ((e.extend (𝓡∂ (k + 1))).symm y)) hx)).symm

/-- Exterior derivative commutes with pullback along a smooth map from a
native manifold with boundary to a boundaryless manifold. The formula includes
all tangents based at the native boundary. -/
theorem exteriorDerivative_pullback_from_boundaryless {d r : ℕ}
    (N : SmoothManifold d) (f : M → N.Point)
    (hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ f)
    (eta : N.Form r) (heta : N.IsSmoothForm eta) :
    exteriorDerivative (fun x => (eta (f x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x)) =
      (fun x => (N.exteriorDerivative eta (f x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x)) := by
  funext x
  let e := chartAt (EuclideanHalfSpace (k + 1)) x
  let b := chartAt (Model d) (f x)
  let y := e.extend (𝓡∂ (k + 1)) x
  let g := b ∘ f ∘ (e.extend (𝓡∂ (k + 1))).symm
  have he := chart_mem_atlas (EuclideanHalfSpace (k + 1)) x
  have hx : x ∈ e.source := mem_chart_source _ _
  have hy : y ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have hys : y ∈ range (𝓡∂ (k + 1)) := e.extend_target_subset_range hy
  have hey : (e.extend (𝓡∂ (k + 1))).symm y = x := e.extend_left_inv hx
  have hey' : ((chartAt (EuclideanHalfSpace (k + 1)) x).extend
      (𝓡∂ (k + 1))).symm y = x := hey
  have hbx : f x ∈ b.source := mem_chart_source _ _
  have hby : b (f x) ∈ b.target := b.map_source hbx
  have hgy : g y = b (f x) := by simp only [g, Function.comp_apply, hey]
  have hg : ContDiffWithinAt ℝ ∞ g (range (𝓡∂ (k + 1))) y := by
    have hci := contMDiffWithinAt_extChartAt_symm_range_self
      (n := ∞) (I := 𝓡∂ (k + 1)) x
    have hce : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ b
        (f ((e.extend (𝓡∂ (k + 1))).symm y)) := by
      rw [hey]
      exact (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := f x)).contMDiffAt
        (b.open_source.mem_nhds hbx)
    exact (hce.comp_contMDiffWithinAt y
      (hf.contMDiffAt.comp_contMDiffWithinAt y hci)).contDiffWithinAt
  have hcoeff : DifferentiableAt ℝ (N.formInChart (f x) eta) (g y) := by
    rw [hgy]
    exact ((heta (f x)).contDiffAt (b.open_target.mem_nhds hby)).differentiableAt (by simp)
  have hnb : ∀ᶠ z in 𝓝[range (𝓡∂ (k + 1))] y,
      f ((e.extend (𝓡∂ (k + 1))).symm z) ∈ b.source := by
    have hc := (hf.continuous.continuousAt
      (x := (e.extend (𝓡∂ (k + 1))).symm y)).comp_continuousWithinAt
      ((contMDiffWithinAt_extChartAt_symm_range_self (n := ∞) (I := 𝓡∂ (k + 1)) x).continuousWithinAt)
    exact hc.preimage_mem_nhdsWithin
      (by simpa only [Function.comp_apply, hey] using b.open_source.mem_nhds hbx)
  have hlocal : formInChart e (fun z => (eta (f z)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f z)) =ᶠ[𝓝[range (𝓡∂ (k + 1))] y]
      (fun z => (N.formInChart (f x) eta (g z)).compContinuousLinearMap
        (fderivWithin ℝ g (range (𝓡∂ (k + 1))) z)) := by
    filter_upwards [e.extend_target_mem_nhdsWithin hx, hnb] with z hz hzb
    exact formInChart_pullback_from_boundaryless N f eta he (f x) hz hzb
      (hf.mdifferentiableAt (by simp))
  change (extDerivWithin (formInChart e (fun z => (eta (f z)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f z)))
      (e.extend (𝓡∂ (k + 1))).target y).compContinuousLinearMap (chartTangentMap e x) = _
  have hdoma : ∀ (beta : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ),
      extDerivWithin beta (e.extend (𝓡∂ (k + 1))).target y =
        extDerivWithin beta (range (𝓡∂ (k + 1))) y := by
    intro beta
    unfold extDerivWithin
    rw [fderivWithin_congr_set (e.extend_target_eventuallyEqSet hx)]
  rw [hdoma, hlocal.extDerivWithin_eq_of_mem hys]
  rw [extDerivWithin_pullback hcoeff.differentiableWithinAt hg (by simp)
    (𝓡∂ (k + 1)).uniqueDiffOn
    ((𝓡∂ (k + 1)).range_subset_closure_interior hys) hys (mapsTo_univ _ _),
    extDerivWithin_univ, hgy]
  have hd := mfderiv_comp_mfderivWithin y
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) (f x)).mdifferentiableAt
      (by simpa only [Function.comp_apply, hey'] using hbx))
    ((hf.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt y
      (mdifferentiableWithinAt_extend_symm
        (IsManifold.subset_maximalAtlas (n := (1 : WithTop ℕ∞)) he) hy))
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((𝓡∂ (k + 1)).uniqueDiffOn y hys))
  rw [mfderiv_comp_mfderivWithin y (hf.mdifferentiableAt (by simp))
    (mdifferentiableWithinAt_extend_symm
      (IsManifold.subset_maximalAtlas (n := (1 : WithTop ℕ∞)) he) hy)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((𝓡∂ (k + 1)).uniqueDiffOn y hys))] at hd
  simp only [Function.comp_apply] at hd
  erw [hey'] at hd
  rw [← mfderivWithin_eq_fderivWithin, hd]
  ext vs
  apply congrArg (extDeriv (N.formInChart (f x) eta) (b (f x)))
  funext j
  exact congrArg
    (fun v => N.chartTangentMap (f x) (f x)
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x v))
    (inverseChartTangentMap_chartTangentMap he hx (vs j))

end FsFltz.Geometry.IntrinsicLiouville
