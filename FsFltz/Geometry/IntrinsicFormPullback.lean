import FsFltz.Geometry.IntrinsicLiouvilleForms

/-!
# Pullback of locally extendible native forms to a boundaryless source

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Pullback uses the actual manifold differential. For a
one-form, local open extensions of the native chart coefficients prove
smoothness of its pullback to any smooth boundaryless source. This supplies
the compact-interior primitive used by boundaryless completion gluing.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Actual native form pullback to a boundaryless smooth source. -/
def pullbackForm {d r : ℕ} (N : SmoothManifold d) (f : N.Point → M)
    (α : Form k M r) : N.Form r :=
  fun x => (α (f x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model d) (𝓡∂ (k + 1)) f x)

/-- Native chart coefficients of the actual pullback satisfy the Euclidean
coordinate chain rule, with the native inverse derivative computed within
the half-space chart target. -/
theorem formInChart_pullbackForm {d r : ℕ} (N : SmoothManifold d)
    {f : N.Point → M} (α : Form k M r) (a : N.Point)
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hx : f ((chartAt (Model d) a).symm y) ∈ e.source)
    (hf : MDifferentiableAt 𝓘(ℝ, Model d) (𝓡∂ (k + 1)) f
      ((chartAt (Model d) a).symm y)) :
    N.formInChart a (pullbackForm N f α) y =
      (formInChart e α (e.extend (𝓡∂ (k + 1))
        (f ((chartAt (Model d) a).symm y)))).compContinuousLinearMap
        (fderiv ℝ (e.extend (𝓡∂ (k + 1)) ∘ f ∘ (chartAt (Model d) a).symm) y) := by
  have hci := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy
  have hce := (e.contMDiffAt_extend
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := ∞) he) hx).mdifferentiableAt (by simp)
  rw [← mfderiv_eq_fderiv, mfderiv_comp y hce (hf.comp y hci),
    mfderiv_comp y hf hci]
  have hrec := formInChart_comp_chartTangentMap he α hx
  unfold SmoothManifold.formInChart pullbackForm
  rw [← hrec]
  ext vs
  rfl

private theorem contDiffAt_oneForm_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (z : G)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) z := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp z ha).clm_comp hB
  have hs := eE.contDiff.contDiffAt.comp z h
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- Smoothness of native one-form pullback follows from local native open
extensions and smoothness of the map. No smooth pullback witness is assumed. -/
theorem isSmoothForm_pullbackForm_one {d : ℕ} (N : SmoothManifold d)
    (f : N.Point → M) (hf : ContMDiff 𝓘(ℝ, Model d) (𝓡∂ (k + 1)) ∞ f)
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α) :
    N.IsSmoothForm (pullbackForm N f α) := by
  intro a y hy
  let c := chartAt (Model d) a
  let x := f (c.symm y)
  let e := chartAt (EuclideanHalfSpace (k + 1)) x
  let g := e.extend (𝓡∂ (k + 1)) ∘ f ∘ c.symm
  have hx : x ∈ e.source := mem_chart_source _ x
  have he := chart_mem_atlas (EuclideanHalfSpace (k + 1)) x
  have hci : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hce := e.contMDiffAt_extend
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := ∞) he) hx
  have hg : ContDiffAt ℝ ∞ g y :=
    (hce.comp y (hf.contMDiffAt.comp y hci)).contDiffAt
  obtain ⟨β, U, hU, hUy, hβ, hEq⟩ := hα e he x hx
  have hβy : ContDiffAt ℝ ∞ β (g y) := hβ.contDiffAt (hU.mem_nhds hUy)
  have hs := contDiffAt_oneForm_comp (β ∘ g) (fderiv ℝ g) y
    (hβy.comp y hg) (hg.fderiv_right (by simp))
  have hnb : ∀ᶠ z in 𝓝 y, f (c.symm z) ∈ e.source :=
    (hf.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (e.open_source.mem_nhds hx)
  have ht : Tendsto g (𝓝 y) (𝓝[(e.extend (𝓡∂ (k + 1))).target] (g y)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hg.continuousAt, ?_⟩
    filter_upwards [hnb] with z hz
    exact (e.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [e.extend_source, Function.comp_apply] using hz)
  apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hEq.comp_tendsto ht, c.open_target.mem_nhds hy, hnb] with z hz hzt hzx
  rw [formInChart_pullbackForm N α a he hzt hzx (hf.mdifferentiableAt (by simp))]
  exact congrArg (fun A => A.compContinuousLinearMap (fderiv ℝ g z)) hz.symm

end FsFltz.Geometry.IntrinsicLiouville
