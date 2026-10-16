import FsFltz.Geometry.IntrinsicLiouvilleForms

/-!
# Smooth intrinsic boundary restriction of native forms

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The restriction is the actual pullback by the inclusion of
the literal intrinsic boundary. Its smoothness follows from local open
extensions of the native coefficients; smooth boundary coefficients are
not supplied as an additional hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicBoundary

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Pull back a native tangent form by the actual boundary inclusion. -/
def restrictForm {r : ℕ} (α : IntrinsicLiouville.Form k M r)
    (x : Point k M) : TangentSpace 𝓘(ℝ, Model k) x [⋀^Fin r]→L[ℝ] ℝ :=
  (α x.val).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) (Subtype.val : Point k M → M) x)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Native ambient coordinates of an inverse boundary chart are precisely
the zero-normal-coordinate insertion. -/
theorem Chart.extend_val_symm (c : Chart k M) {y : Model k} (hy : y ∈ c.chart.target) :
    c.ambient.extend (𝓡∂ (k + 1)) (c.chart.symm y).val = boundaryInsert k y := by
  have he : halfSpaceInsert k y ∈ c.ambient.target := by rwa [c.target_eq] at hy
  rw [c.invFun_eq y hy, c.ambient.extend_coe]
  change (c.ambient (c.ambient.symm (halfSpaceInsert k y))).val = _
  rw [c.ambient.right_inv he]
  rfl

/-- The boundary inclusion and inverse boundary-chart differentials,
followed by the ambient chart differential, give linear hyperplane insertion. -/
theorem Chart.chartTangentMap_val_inverseChart (c : Chart k M)
    {y : Model k} (hy : y ∈ c.chart.target) :
    (IntrinsicLiouville.chartTangentMap c.ambient (c.chart.symm y).val).comp
      ((mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
        (Subtype.val : Point k M → M) (c.chart.symm y)).comp
          (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm y)) =
      boundaryInsert k := by
  have hcs : c.chart.symm y ∈ c.chart.source := c.chart.map_target hy
  have hes : (c.chart.symm y).val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
  have he := c.ambient.contMDiffAt_extend
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := ∞) c.mem_atlas) hes
  have hc : c.chart ∈ atlas (Model k) (Point k M) := ⟨c, rfl⟩
  have hi := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Model k)) (n := ∞) hc) hy
  have hv := contMDiff_val (k := k) (M := M)
  have hdv := mfderiv_comp (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, Model k))
    (I'' := 𝓡∂ (k + 1)) (f := c.chart.symm)
    (g := (Subtype.val : Point k M → M)) y
    (hv.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  have hde := mfderiv_comp (I := 𝓘(ℝ, Model k)) (I' := 𝓡∂ (k + 1))
    (I'' := 𝓘(ℝ, Model (k + 1))) (f := Subtype.val ∘ c.chart.symm)
    (g := c.ambient.extend (𝓡∂ (k + 1))) y
    (he.mdifferentiableAt (by simp))
    ((hv.contMDiffAt.comp y hi).mdifferentiableAt (by simp))
  have heq : (c.ambient.extend (𝓡∂ (k + 1)) ∘
      (Subtype.val : Point k M → M) ∘ c.chart.symm) =ᶠ[𝓝 y] boundaryInsert k := by
    filter_upwards [c.chart.open_target.mem_nhds hy] with z hz
    exact c.extend_val_symm hz
  rw [hdv] at hde
  change mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
    (c.ambient.extend (𝓡∂ (k + 1)) ∘
      (Subtype.val : Point k M → M) ∘ c.chart.symm) y = _ at hde
  rw [heq.mfderiv_eq] at hde
  rw [(boundaryInsert k).hasMFDerivAt.mfderiv] at hde
  exact hde.symm

/-- Restricted boundary coefficients are the native coefficients on the
zero-normal-coordinate hyperplane, transported by its linear insertion. -/
theorem Chart.restrictForm_coefficients (c : Chart k M) {r : ℕ}
    (α : IntrinsicLiouville.Form k M r) {y : Model k} (hy : y ∈ c.chart.target) :
    (restrictForm α (c.chart.symm y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm y) =
    (IntrinsicLiouville.formInChart c.ambient α (boundaryInsert k y)).compContinuousLinearMap
      (boundaryInsert k) := by
  have hcs : c.chart.symm y ∈ c.chart.source := c.chart.map_target hy
  have hes : (c.chart.symm y).val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
  have hrec := IntrinsicLiouville.formInChart_comp_chartTangentMap c.mem_atlas α hes
  rw [c.extend_val_symm hy] at hrec
  have hd := c.chartTangentMap_val_inverseChart hy
  ext vs
  change α (c.chart.symm y).val (fun i =>
      mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1)) Subtype.val (c.chart.symm y)
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm y (vs i))) = _
  rw [← hrec]
  apply congrArg (IntrinsicLiouville.formInChart c.ambient α (boundaryInsert k y))
  funext i
  exact congrArg (fun A => A (vs i)) hd

variable [T2Space M] [SecondCountableTopology M]

/-- The actual restriction of a locally extendible native form is smooth on
the boundaryless intrinsic boundary, in every form degree. -/
theorem isSmoothForm_restrictForm {r : ℕ} (α : IntrinsicLiouville.Form k M r)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) :
    (smoothManifold k M).IsSmoothForm (restrictForm α) := by
  intro a y hy
  let c := chartAt a
  change y ∈ c.chart.target at hy
  have hcs : c.chart.symm y ∈ c.chart.source := c.chart.map_target hy
  have hes : (c.chart.symm y).val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
  obtain ⟨β, U, hU, hUy, hβ, hEq⟩ := hα c.ambient c.mem_atlas _ hes
  have hcoord := c.extend_val_symm hy
  rw [hcoord] at hUy hEq
  have hβy : ContDiffAt ℝ ∞ β (boundaryInsert k y) :=
    hβ.contDiffAt (hU.mem_nhds hUy)
  let L : (Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ]
      (Model k [⋀^Fin r]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (boundaryInsert k)
  have hsm : ContDiffAt ℝ ∞ (L ∘ β ∘ boundaryInsert k) y :=
    L.contDiff.contDiffAt.comp y (hβy.comp y (boundaryInsert k).contDiff.contDiffAt)
  have ht : Tendsto (boundaryInsert k) (𝓝 y)
      (𝓝[(c.ambient.extend (𝓡∂ (k + 1))).target] (boundaryInsert k y)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(boundaryInsert k).continuous.continuousAt, ?_⟩
    filter_upwards [c.chart.open_target.mem_nhds hy] with z hz
    have hzs : (c.chart.symm z).val ∈ c.ambient.source := by
      have hs := c.chart.map_target hz
      rwa [c.source_eq] at hs
    rw [← c.extend_val_symm hz]
    exact (c.ambient.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [c.ambient.extend_source] using hzs)
  apply (hsm.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hEq.comp_tendsto ht, c.chart.open_target.mem_nhds hy] with z hz hzt
  change (restrictForm α (c.chart.symm z)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) c.chart.symm z) = L (β (boundaryInsert k z))
  rw [c.restrictForm_coefficients α hzt]
  exact congrArg L hz.symm

end FsFltz.Geometry.IntrinsicBoundary
