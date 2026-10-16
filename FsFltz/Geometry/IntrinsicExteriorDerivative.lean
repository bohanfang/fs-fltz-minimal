import FsFltz.Geometry.IntrinsicLiouvilleForms

/-!
# Actual exterior derivatives on native manifolds with boundary

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. A native derivative is computed from the actual coefficients
in a preferred chart. The results below establish covariance under every
native atlas chart using local open extension germs, including boundary points.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual differential of an extended coordinate transition. -/
theorem fderivWithin_chartChange
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hy' : (e.extend (𝓡∂ (k + 1))).symm y ∈ e'.source) :
    fderivWithin ℝ ((𝓡∂ (k + 1)).extendCoordChange e e')
      (range (𝓡∂ (k + 1))) y =
      (chartTangentMap e' ((e.extend (𝓡∂ (k + 1))).symm y)).comp
        (inverseChartTangentMap e y) := by
  rw [← mfderivWithin_eq_fderivWithin]
  exact mfderiv_comp_mfderivWithin y
    ((e'.contMDiffAt_extend (IsManifold.subset_maximalAtlas (n := ∞) he') hy').mdifferentiableAt
      (by simp))
    (mdifferentiableWithinAt_extend_symm
      (IsManifold.subset_maximalAtlas (n := (1 : WithTop ℕ∞)) he) hy)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr
      ((𝓡∂ (k + 1)).uniqueDiffOn y (e.extend_target_subset_range hy)))

/-- Coefficients in overlapping native charts transform by the actual
differential of the coordinate transition. -/
theorem formInChart_change {r : ℕ}
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (α : Form k M r) {y : Model (k + 1)}
    (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hy' : (e.extend (𝓡∂ (k + 1))).symm y ∈ e'.source) :
    formInChart e α y =
      (formInChart e' α ((𝓡∂ (k + 1)).extendCoordChange e e' y)).compContinuousLinearMap
        (fderivWithin ℝ ((𝓡∂ (k + 1)).extendCoordChange e e')
          (range (𝓡∂ (k + 1))) y) := by
  rw [fderivWithin_chartChange he he' hy hy']
  change formInChart e α y =
    (formInChart e' α (e'.extend (𝓡∂ (k + 1))
      ((e.extend (𝓡∂ (k + 1))).symm y))).compContinuousLinearMap
      ((chartTangentMap e' ((e.extend (𝓡∂ (k + 1))).symm y)).comp
        (inverseChartTangentMap e y))
  have h := formInChart_comp_chartTangentMap he' α hy'
  apply ContinuousAlternatingMap.ext
  intro vs
  exact (congrArg (fun A => A (fun i => inverseChartTangentMap e y (vs i))) h).symm

/-- A native, form-determined derivative; no derivative witness is supplied
to this definition. Covariance is a theorem for locally extendible forms. -/
def exteriorDerivative {r : ℕ} (α : Form k M r) : Form k M (r + 1) :=
  fun x =>
    (extDerivWithin (formInChart (chartAt (EuclideanHalfSpace (k + 1)) x) α)
      (extChartAt (𝓡∂ (k + 1)) x).target (extChartAt (𝓡∂ (k + 1)) x x)).compContinuousLinearMap
        (chartTangentMap (chartAt (EuclideanHalfSpace (k + 1)) x) x)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Within a native chart target, a smooth open extension has precisely the
same actual exterior derivative. This includes boundary points. -/
theorem extDerivWithin_eq_extension {r : ℕ}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    {α : Form k M r}
    {β : Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ}
    {y : Model (k + 1)} (hy : y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hβ : DifferentiableAt ℝ β y)
    (hag : β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target] y] formInChart e α) :
    extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target y =
      extDeriv β y := by
  rw [← hag.extDerivWithin_eq_of_mem hy]
  unfold extDerivWithin extDeriv
  apply congrArg ContinuousAlternatingMap.alternatizeUncurryFin
  apply hβ.fderivWithin
  rw [e.extend_target]
  exact (𝓡∂ (k + 1)).uniqueDiffOn_preimage e.open_target y
    (by simpa only [e.extend_target] using hy)

/-- Differentiating the coefficients commutes with a change of native chart.
Local open extension is used only for the form coefficients; transition
smoothness and boundary derivative uniqueness come from the native atlas. -/
theorem extDerivWithin_formInChart_change {r : ℕ}
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (he' : e' ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (α : Form k M r) (hα : IsLocallyExtendibleForm α)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target
        (e.extend (𝓡∂ (k + 1)) x) =
      (extDerivWithin (formInChart e' α) (e'.extend (𝓡∂ (k + 1))).target
        (e'.extend (𝓡∂ (k + 1)) x)).compContinuousLinearMap
        (fderivWithin ℝ ((𝓡∂ (k + 1)).extendCoordChange e e')
          (range (𝓡∂ (k + 1))) (e.extend (𝓡∂ (k + 1)) x)) := by
  let a := e.extend (𝓡∂ (k + 1)) x
  let b := e'.extend (𝓡∂ (k + 1)) x
  let T := (𝓡∂ (k + 1)).extendCoordChange e e'
  have hax : (e.extend (𝓡∂ (k + 1))).symm a = x := e.extend_left_inv hx
  have hTa : T a = b := by
    simp only [T, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply, hax]
    rfl
  have ha : a ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have hb : b ∈ (e'.extend (𝓡∂ (k + 1))).target :=
    (e'.extend (𝓡∂ (k + 1))).map_source (by simpa only [e'.extend_source] using hx')
  have hS : a ∈ T.source := by
    simpa only [T, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, e'.extend_source, mem_inter_iff, mem_preimage, hax]
      using And.intro ha hx'
  have hT : ContDiffWithinAt ℝ ∞ T (range (𝓡∂ (k + 1))) a :=
    (𝓡∂ (k + 1)).contDiffWithinAt_extendCoordChange
      (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he') hS
  have hSmem : T.source ∈ 𝓝[range (𝓡∂ (k + 1))] a :=
    (𝓡∂ (k + 1)).extendCoordChange_source_mem_nhdsWithin hS
  obtain ⟨β, U, hU, hbU, hβ, hag⟩ := hα e' he' x hx'
  have hβb : DifferentiableAt ℝ β b :=
    (hβ.contDiffAt (hU.mem_nhds hbU)).differentiableAt (by simp)
  have htarget : ∀ᶠ z in 𝓝[range (𝓡∂ (k + 1))] a,
      T z ∈ (e'.extend (𝓡∂ (k + 1))).target := by
    filter_upwards [hSmem] with z hz
    have hz' : (e.extend (𝓡∂ (k + 1))).symm z ∈
        (e'.extend (𝓡∂ (k + 1))).source := by
      simpa only [PartialEquiv.symm_symm, mem_preimage] using hz.2
    simpa only [T, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply] using
      (e'.extend (𝓡∂ (k + 1))).map_source hz'
  have ht : Tendsto T (𝓝[range (𝓡∂ (k + 1))] a)
      (𝓝[(e'.extend (𝓡∂ (k + 1))).target] b) := by
    rw [← hTa]
    exact tendsto_nhdsWithin_iff.mpr ⟨hT.continuousWithinAt, htarget⟩
  have hlocal : formInChart e α =ᶠ[𝓝[range (𝓡∂ (k + 1))] a]
      (fun z => (β (T z)).compContinuousLinearMap
        (fderivWithin ℝ T (range (𝓡∂ (k + 1))) z)) := by
    filter_upwards [hSmem, ht.eventually hag] with z hz hzg
    rw [formInChart_change he he' α hz.1
      (by simpa only [PartialEquiv.symm_symm, e'.extend_source, mem_preimage] using hz.2), ← hzg]
  rw [extDerivWithin_eq_extension hb hβb hag]
  have hdoma : extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target a =
      extDerivWithin (formInChart e α) (range (𝓡∂ (k + 1))) a := by
    unfold extDerivWithin
    rw [fderivWithin_congr_set (e.extend_target_eventuallyEqSet hx)]
  rw [hdoma, hlocal.extDerivWithin_eq_of_mem (e.extend_target_subset_range ha)]
  have hpull := extDerivWithin_pullback (s := range (𝓡∂ (k + 1))) (t := univ)
    (x := a) («ω» := β) (f := T)
    (by rw [hTa]; exact hβb.differentiableWithinAt) hT (by simp)
    (𝓡∂ (k + 1)).uniqueDiffOn
    ((𝓡∂ (k + 1)).range_subset_closure_interior (e.extend_target_subset_range ha))
    (e.extend_target_subset_range ha) (mapsTo_univ _ _)
  simpa only [extDerivWithin_univ, hTa] using hpull

/-- The native derivative can be computed in every atlas chart containing
the point; it is independent of the preferred chart in its definition. -/
theorem exteriorDerivative_eq_in_chart {r : ℕ}
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (α : Form k M r) (hα : IsLocallyExtendibleForm α)
    {x : M} (hx : x ∈ e.source) :
    exteriorDerivative α x =
      (extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target
        (e.extend (𝓡∂ (k + 1)) x)).compContinuousLinearMap (chartTangentMap e x) := by
  let c := chartAt (EuclideanHalfSpace (k + 1)) x
  have hc : c ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ x
  have hcx : x ∈ c.source := mem_chart_source _ x
  have hcy : c.extend (𝓡∂ (k + 1)) x ∈ (c.extend (𝓡∂ (k + 1))).target :=
    (c.extend (𝓡∂ (k + 1))).map_source (by simpa only [c.extend_source] using hcx)
  have hcx' : (c.extend (𝓡∂ (k + 1))).symm (c.extend (𝓡∂ (k + 1)) x) ∈ e.source :=
    by simpa only [c.extend_left_inv hcx] using hx
  change (extDerivWithin (formInChart c α) (c.extend (𝓡∂ (k + 1))).target
    (c.extend (𝓡∂ (k + 1)) x)).compContinuousLinearMap (chartTangentMap c x) = _
  rw [extDerivWithin_formInChart_change hc he α hα hcx hx,
    fderivWithin_chartChange hc he hcy hcx', c.extend_left_inv hcx]
  apply ContinuousAlternatingMap.ext
  intro vs
  apply congrArg (extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target
    (e.extend (𝓡∂ (k + 1)) x))
  funext i
  exact congrArg (chartTangentMap e x) (inverseChartTangentMap_chartTangentMap hc hcx (vs i))

/-- Local smooth extension constructs the actual native exterior derivative;
the full coordinate equation is proved for every atlas chart. -/
theorem hasExteriorDerivative_exteriorDerivative {r : ℕ}
    (α : Form k M r) (hα : IsLocallyExtendibleForm α) :
    HasExteriorDerivative α (exteriorDerivative α) := by
  intro e he y hy
  unfold formInChart
  rw [exteriorDerivative_eq_in_chart he α hα
    (by simpa only [e.extend_source] using (e.extend (𝓡∂ (k + 1))).map_target hy),
    (e.extend (𝓡∂ (k + 1))).right_inv hy]
  apply ContinuousAlternatingMap.ext
  intro vs
  apply congrArg (extDerivWithin (formInChart e α) (e.extend (𝓡∂ (k + 1))).target y)
  funext i
  exact chartTangentMap_inverseChartTangentMap he hy (vs i)

/-- The chart equation determines the native derivative uniquely, without
needing any unrelated two-form supplied as a permanent witness. -/
theorem eq_exteriorDerivative_of_hasExteriorDerivative {r : ℕ}
    {α : Form k M r} {omega : Form k M (r + 1)}
    (hd : HasExteriorDerivative α omega) : omega = exteriorDerivative α := by
  funext x
  let c := chartAt (EuclideanHalfSpace (k + 1)) x
  have hc : c ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ x
  have hx : x ∈ c.source := mem_chart_source _ x
  have hy : c.extend (𝓡∂ (k + 1)) x ∈ (c.extend (𝓡∂ (k + 1))).target :=
    (c.extend (𝓡∂ (k + 1))).map_source (by simpa only [c.extend_source] using hx)
  rw [← formInChart_comp_chartTangentMap hc omega hx, hd c hc _ hy]
  rfl

/-- Every locally extendible native form has exactly one actual derivative. -/
theorem existsUnique_exteriorDerivative {r : ℕ}
    (α : Form k M r) (hα : IsLocallyExtendibleForm α) :
    ∃! omega : Form k M (r + 1), HasExteriorDerivative α omega :=
  ⟨exteriorDerivative α, hasExteriorDerivative_exteriorDerivative α hα,
    fun _ hd => eq_exteriorDerivative_of_hasExteriorDerivative hd⟩

end FsFltz.Geometry.IntrinsicLiouville
