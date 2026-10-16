import FsFltz.Geometry.IntrinsicLiouvilleForms

/-!
# Native chart transport of contraction and exterior derivatives

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The chart differential and its within-half-space
inverse transport the actual native forms and fields.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem uniqueDiffOn_chart_target
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))) :
    UniqueDiffOn ℝ (e.extend (𝓡∂ (k + 1))).target := by
  rw [OpenPartialHomeomorph.extend_target]
  exact (𝓡∂ (k + 1)).uniqueDiffOn_preimage e.open_target

/-- Nondegeneracy is preserved by genuine native inverse-chart tangent transport. -/
theorem nondegenerate_formInChart
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (omega : Form k M 2)
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hnd : Nondegenerate omega ((e.extend (𝓡∂ (k + 1))).symm y)) :
    ∀ v, (∀ w, formInChart e omega y ![v, w] = 0) → v = 0 := by
  intro v hv
  let x := (e.extend (𝓡∂ (k + 1))).symm y
  have hx : x ∈ e.source := by
    simpa only [e.extend_source] using (e.extend (𝓡∂ (k + 1))).map_target hy
  have hxy : e.extend (𝓡∂ (k + 1)) x = y :=
    (e.extend (𝓡∂ (k + 1))).right_inv hy
  have hz : inverseChartTangentMap e y v = 0 := by
    apply hnd
    intro w
    have hw := hv (chartTangentMap e x w)
    change omega x (fun i => inverseChartTangentMap e y (![v, chartTangentMap e x w] i)) = 0 at hw
    have hwi : inverseChartTangentMap e y (chartTangentMap e x w) = w := by
      rw [← hxy]
      exact inverseChartTangentMap_chartTangentMap he hx w
    convert hw using 1
    apply congrArg (omega x)
    funext i
    fin_cases i
    · rfl
    · exact hwi.symm
  have hi := chartTangentMap_inverseChartTangentMap he hy v
  rw [hz, map_zero] at hi
  exact hi.symm

/-- Contraction of native forms transports to the actual chart-pushed field. -/
theorem contraction_inChart
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (α : Form k M 1) (omega : Form k M 2)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) (hZ : Contraction α omega Z)
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target) :
    (formInChart e omega y).curryLeft (vectorInChart e Z y) = formInChart e α y := by
  let x := (e.extend (𝓡∂ (k + 1))).symm y
  have hx : x ∈ e.source := by
    simpa only [e.extend_source] using (e.extend (𝓡∂ (k + 1))).map_target hy
  have hxy : e.extend (𝓡∂ (k + 1)) x = y :=
    (e.extend (𝓡∂ (k + 1))).right_inv hy
  have hZi : inverseChartTangentMap e y (vectorInChart e Z y) = Z x := by
    change inverseChartTangentMap e y (chartTangentMap e x (Z x)) = Z x
    rw [← hxy]
    exact inverseChartTangentMap_chartTangentMap he hx (Z x)
  ext vs
  have hvs : vs = ![vs 0] := by
    funext i
    fin_cases i
    rfl
  rw [hvs]
  change omega x (fun i => inverseChartTangentMap e y (![vectorInChart e Z y, vs 0] i)) =
    α x (fun i => inverseChartTangentMap e y (![vs 0] i))
  convert hZ x (inverseChartTangentMap e y (vs 0)) using 1
  · apply congrArg (omega x)
    funext i
    fin_cases i
    · exact hZi
    · rfl
  · apply congrArg (α x)
    funext i
    fin_cases i
    rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- A local smooth primitive extension differentiates to the intrinsic exterior
derivative at every point where its germ agrees. Uniqueness of differentiation
within the half-space includes the seam. -/
theorem extDeriv_extension_eq {r : ℕ}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {α : Form k M r} {omega : Form k M (r + 1)} (hd : HasExteriorDerivative α omega)
    {β : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ}
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hβ : DifferentiableAt ℝ β y)
    (hag : β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target] y] formInChart e α) :
    extDeriv β y = formInChart e omega y := by
  rw [hd e he y hy, ← hag.extDerivWithin_eq_of_mem hy]
  unfold extDerivWithin extDeriv
  rw [hβ.fderivWithin (uniqueDiffOn_chart_target e y hy)]


end FsFltz.Geometry.IntrinsicLiouville
