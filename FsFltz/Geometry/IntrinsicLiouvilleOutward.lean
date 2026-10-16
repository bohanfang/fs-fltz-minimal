import FsFltz.Geometry.IntrinsicLiouvilleForms

/-!
# Defining functions and native inward signs

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–130, and `def:pair`, lines 132–160. The canonical local defining
function is the negative normal coordinate of an actual native atlas chart.
Its scalar derivative is the negative normal field coefficient. This connects
the source's defining-function outward inequality to inward collar integration.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The local sublevel convention is `rho ≤ 0`, whereas native half-space
normal coordinates are nonnegative. -/
def normalDefiningFunction
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))) (x : M) : ℝ :=
  -(e.extend (𝓡∂ (k + 1)) x) 0

theorem smooth_normalDefiningFunction
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) :
    ContMDiffOn (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) ∞ (normalDefiningFunction e) e.source := by
  exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).contMDiff).comp_contMDiffOn
    (e.contMDiffOn_extend (IsManifold.subset_maximalAtlas he))).neg

omit [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem normalDefiningFunction_nonpos
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))) (x : M) :
    normalDefiningFunction e x ≤ 0 := neg_nonpos.mpr (e x).property

theorem normalDefiningFunction_zero_iff
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source) :
    normalDefiningFunction e x = 0 ↔ (𝓡∂ (k + 1)).IsBoundaryPoint x := by
  rw [IntrinsicBoundary.isBoundaryPoint_iff_chart_zero he hx]
  exact neg_eq_zero

theorem normalDefiningFunction_derivative
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (v : TangentSpace (𝓡∂ (k + 1)) x) :
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (normalDefiningFunction e) x v =
      -(show Model (k + 1) from chartTangentMap e x v) 0 := by
  let P := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))
  have he' : e ∈ IsManifold.maximalAtlas (𝓡∂ (k + 1)) ∞ M := IsManifold.subset_maximalAtlas he
  have hed : MDifferentiableAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (e.extend (𝓡∂ (k + 1))) x :=
    (e.contMDiffAt_extend he' hx).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, ℝ)) x (((-P).contMDiff (n := ∞)).mdifferentiable (by simp) _)
      hed
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc
  exact congrArg (fun L => (show TangentSpace (𝓡∂ (k + 1)) x →L[ℝ] ℝ from L) v) hc

theorem normalDefiningFunction_regular
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source) :
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (normalDefiningFunction e) x ≠ 0 := by
  let a := e.extend (𝓡∂ (k + 1)) x
  have ha : a ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  let v := inverseChartTangentMap e a (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ))
  have hv := normalDefiningFunction_derivative he hx v
  have hinv := chartTangentMap_inverseChartTangentMap he ha
    (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ))
  rw [(e.extend (𝓡∂ (k + 1))).left_inv
    (by simpa only [e.extend_source] using hx)] at hinv
  change (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
    (normalDefiningFunction e) x v) =
      -(show Model (k + 1) from chartTangentMap e x v) 0 at hv
  have hinv' : (show Model (k + 1) from chartTangentMap e x v) =
      EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ) := hinv
  rw [hinv'] at hv
  intro hz
  rw [hz] at hv
  simp at hv

/-- The defining-function outward inequality yields the strictly positive
normal coefficient of the negative native field. -/
theorem inward_of_normalDefiningFunction_outward
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hout : 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
      (normalDefiningFunction e) x (Z x))) :
    0 < (show Model (k + 1) from chartTangentMap e x (-Z x)) 0 := by
  rw [normalDefiningFunction_derivative he hx] at hout
  have hn : (show Model (k + 1) from chartTangentMap e x (-Z x)) =
      -(show Model (k + 1) from chartTangentMap e x (Z x)) := map_neg _ _
  rw [hn]
  exact hout

end FsFltz.Geometry.IntrinsicLiouville
