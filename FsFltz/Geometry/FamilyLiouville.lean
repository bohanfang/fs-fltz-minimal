import FsFltz.Geometry.Family
import FsFltz.Geometry.SmoothLiouville

/-!
# Smooth Liouville fields in interval families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and `sec:lean`,
lines 783–814. A smooth primitive family has a jointly smooth spatial exterior
derivative: take the total derivative of its chart coefficients, restrict to
the spatial direction, and alternate. In a fixed chart the actual intrinsic
derivative equals this spatial derivative whenever those coefficients are
locally smooth. This local formulation accommodates nonuniform extension
neighborhoods of the closed parameter interval on a noncompact manifold.

The contraction matrices are therefore jointly smooth. Their invertibility
locus is open and contains every required parameter and spatial point by the
given nondegeneracy. Inverting on this locus gives the actual Liouville field
and its jointly smooth extension. Nondegeneracy outside the interval and
smoothness of the fields are not hypotheses.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry

/-- Taking the spatial exterior derivative preserves joint smoothness on an
open parameter and spatial neighborhood. -/
theorem contDiffOn_spatialExtDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (f : ℝ × E → E [⋀^Fin k]→L[ℝ] ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun ty => extDeriv (fun z => f (ty.1, z)) ty.2) U := by
  let inc := ContinuousLinearMap.inr ℝ ℝ E
  let B := fun ty => (fderiv ℝ f ty).comp inc
  have hB : ContDiffOn ℝ ∞ B U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
  have halt : ContDiff ℝ ∞
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ :
        (E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) → E [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)
      (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ)
  have hs : ContDiffOn ℝ ∞
      (fun ty => ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ (B ty)) U :=
    halt.comp_contDiffOn hB
  apply hs.congr
  intro ty hty
  have hinc : HasFDerivAt (fun z : E => (ty.1, z)) inc ty.2 :=
    hasFDerivAt_const ty.1 ty.2 |>.prodMk (hasFDerivAt_id ty.2)
  have hslice := ((hf.contDiffAt (hU.mem_nhds hty)).differentiableAt
    (by simp)).hasFDerivAt.comp ty.2 hinc
  change HasFDerivAt (fun z => f (ty.1, z)) (B ty) ty.2 at hslice
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ
      (fderiv ℝ (fun z => f (ty.1, z)) ty.2) =
    ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ (B ty)
  rw [hslice.fderiv]

namespace SmoothManifold

/-- The actual intrinsic derivative can be computed in a fixed chart from
local smoothness of its coefficients; no global smoothness of a time slice
outside its extension neighborhood is required. -/
theorem exteriorDerivative_eq_in_chart_of_contDiffAt {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (a x : M.Point) (hx : x ∈ (chartAt (Model d) a).source)
    (heta : ContDiffAt ℝ ∞ (M.formInChart a eta) (chartAt (Model d) a x)) :
    M.exteriorDerivative eta x =
      (extDeriv (M.formInChart a eta) (chartAt (Model d) a x)).compContinuousLinearMap
        (M.chartTangentMap a x) := by
  let c := chartAt (Model d) x
  let b := chartAt (Model d) a
  have hcx : x ∈ c.source := mem_chart_source _ _
  have hcy : c x ∈ c.target := c.map_source hcx
  have hc : c.symm (c x) = x := c.left_inv hcx
  have hA : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm (c x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_target.mem_nhds hcy)
  have hB : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ b (c.symm (c x)) := by
    rw [hc]
    exact (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hCoeff : DifferentiableAt ℝ (M.formInChart a eta) ((b ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply, hc] using heta.differentiableAt (by simp)
  have hnb : ∀ᶠ z in 𝓝 (c x), c.symm z ∈ b.source :=
    (c.continuousAt_symm hcy).preimage_mem_nhds (b.open_source.mem_nhds (by rwa [hc]))
  have hlocal : M.formInChart x eta =ᶠ[𝓝 (c x)]
      fun z => (M.formInChart a eta ((b ∘ c.symm) z)).compContinuousLinearMap
        (fderiv ℝ (b ∘ c.symm) z) := by
    filter_upwards [c.open_target.mem_nhds hcy, hnb] with z hz hzb
    simpa only [pullback_id, Function.comp_id, Function.id_comp, Function.comp_apply,
      id_eq, c, b] using
      M.formInChart_pullback M (f := id) eta x a z hz hzb
        (mdifferentiableAt_id (I := 𝓘(ℝ, Model d)))
  change (extDeriv (M.formInChart x eta) (c x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c x) = _
  rw [hlocal.extDeriv_eq, extDeriv_pullback hCoeff (hB.comp (c x) hA).contDiffAt (by simp)]
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (c x) (hB.mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))]
  simp only [Function.comp_apply]
  erw [hc]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hcx
  apply ContinuousAlternatingMap.ext
  intro vs
  change (extDeriv (M.formInChart a eta) (b x))
      (fun i => (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) b x)
        ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x))
          ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c x) (vs i)))) =
    (extDeriv (M.formInChart a eta) (b x))
      (fun i => (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) b x) (vs i))
  apply congrArg (extDeriv (M.formInChart a eta) (b x))
  funext i
  exact congrArg (fun v => (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) b x) v)
    (congrArg (fun L => L (vs i)) hinv)

/-- Local smooth coefficients also give the usual derivative formula after
transport back to the fixed chart. -/
theorem formInChart_exteriorDerivative_of_contDiffAt {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (a : M.Point) (y : Model d) (hy : y ∈ (chartAt (Model d) a).target)
    (heta : ContDiffAt ℝ ∞ (M.formInChart a eta) y) :
    M.formInChart a (M.exteriorDerivative eta) y = extDeriv (M.formInChart a eta) y := by
  let c := chartAt (Model d) a
  have hcy := c.right_inv hy
  have hcy' : chartAt (Model d) a (c.symm y) = y := hcy
  unfold formInChart
  rw [M.exteriorDerivative_eq_in_chart_of_contDiffAt eta a (c.symm y) (c.map_target hy)
    (by simpa only [hcy'] using heta)]
  rw [hcy]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).comp_symm_deriv hy
  apply ContinuousAlternatingMap.ext
  intro vs
  change (extDeriv (M.formInChart a eta) y)
      (fun i => (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c (c.symm y))
        ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm y) (vs i))) = _
  congr 1
  funext i
  exact congrArg (fun L => L (vs i)) hinv

/-- Invertibility of the canonical chart contraction detects nondegeneracy. -/
theorem nondegenerate_of_chartContraction_invertible {d : ℕ}
    (eta : Model d [⋀^Fin 2]→L[ℝ] ℝ) (h : (chartContraction eta).IsInvertible) :
    ∀ v, (∀ w, eta ![v, w] = 0) → v = 0 := by
  intro v hv
  have hc : eta.curryLeft v = 0 := by
    ext vs
    have he := hv (vs 0)
    convert he using 1
    apply congrArg eta
    ext i
    fin_cases i <;> simp
  apply h.injective
  simp only [chartContraction, ContinuousLinearMap.comp_apply, hc, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Nondegeneracy of fixed-chart coefficients implies intrinsic
nondegeneracy on the actual tangent fiber. -/
theorem nondegenerate_of_formInChart {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (a : M.Point) {y : Model d} (hy : y ∈ (chartAt (Model d) a).target)
    (hnd : ∀ v, (∀ w, M.formInChart a eta y ![v, w] = 0) → v = 0) :
    M.Nondegenerate eta ((chartAt (Model d) a).symm y) := by
  intro v hv
  let c := chartAt (Model d) a
  let x := c.symm y
  have hx := c.map_target hy
  have hxy := c.right_inv hy
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  have hback : M.inverseChartTangentMap a y (M.chartTangentMap a x v) = v := by
    have he := congrArg (fun L => L v) hinv
    change M.inverseChartTangentMap a (c x) (M.chartTangentMap a x v) = v at he
    erw [hxy] at he
    exact he
  have hzero : M.chartTangentMap a x v = 0 := by
    apply hnd
    intro w
    change (eta x) (fun i => M.inverseChartTangentMap a y
      (![M.chartTangentMap a x v, w] i)) = 0
    have hp : (fun i => M.inverseChartTangentMap a y
        (![M.chartTangentMap a x v, w] i)) =
        ![M.inverseChartTangentMap a y (M.chartTangentMap a x v),
          M.inverseChartTangentMap a y w] := by
      ext i
      fin_cases i <;> rfl
    rw [hp, hback]
    exact hv (M.inverseChartTangentMap a y w)
  rw [hzero, map_zero] at hback
  exact hback.symm

/-- Joint primitive smoothness produces joint smoothness of its actual
Liouville fields. Nondegeneracy is required only on the closed interval. -/
theorem isSmoothVectorFieldFamily_liouvilleVector {d : ℕ} (M : SmoothManifold d)
    (alpha : ℝ → M.Form 1) (halpha : M.IsSmoothFormFamily alpha)
    (hnd : ∀ t ∈ parameterInterval, ∀ x,
      M.Nondegenerate (M.exteriorDerivative (alpha t)) x) :
    M.IsSmoothVectorFieldFamily (fun t => M.liouvilleVector (alpha t)) := by
  intro a
  obtain ⟨U, hU, hsub, hf⟩ := halpha a
  let c := chartAt (Model d) a
  let f := fun ty : ℝ × Model d => M.formInChart a (alpha ty.1) ty.2
  let B := fun ty : ℝ × Model d => extDeriv (fun z => f (ty.1, z)) ty.2
  let A := fun ty : ℝ × Model d => chartContraction (B ty)
  let b := fun ty : ℝ × Model d => (chartOneFormEquiv d).symm (f ty)
  have hB : ContDiffOn ℝ ∞ B U := contDiffOn_spatialExtDeriv f U hU hf
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U := contDiffOn_const.clm_comp (hcur.comp_contDiffOn hB)
  have hb : ContDiffOn ℝ ∞ b U := (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn hf
  have hres (ty : ℝ × Model d) (hty : ty ∈ U) (hy : ty.2 ∈ c.target) :
      M.formInChart a (M.exteriorDerivative (alpha ty.1)) ty.2 = B ty := by
    have hs : ContDiffAt ℝ ∞ (fun z => f (ty.1, z)) ty.2 :=
      (hf.contDiffAt (hU.mem_nhds hty)).comp ty.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact M.formInChart_exteriorDerivative_of_contDiffAt (alpha ty.1) a ty.2 hy hs
  let V := U ∩ (univ ×ˢ c.target)
  have hV : IsOpen V := hU.inter (isOpen_univ.prod c.open_target)
  let W := V ∩ A ⁻¹' {T | T.IsInvertible}
  have hW : IsOpen W := (hA.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    hV ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hWsub : parameterInterval ×ˢ c.target ⊆ W := by
    intro ty hty
    have hmem : ty ∈ U := hsub hty
    refine ⟨⟨hmem, ⟨mem_univ _, hty.2⟩⟩, ?_⟩
    change (A ty).IsInvertible
    dsimp [A]
    rw [← hres ty hmem hty.2]
    exact chartContraction_invertible _ (M.nondegenerate_formInChart _ a hty.2
      (hnd ty.1 hty.1 _))
  refine ⟨W, hW, hWsub, ?_⟩
  have hAi : ContDiffOn ℝ ∞ (fun ty => (A ty).inverse) W := by
    intro ty hty
    exact hty.2.contDiffAt_map_inverse.comp_contDiffWithinAt ty
      (hA ty hty.1.1 |>.mono (fun _ hw => hw.1.1))
  apply (hAi.clm_apply (hb.mono (fun _ hw => hw.1.1))).congr
  intro ty hty
  have hactual : M.Nondegenerate (M.exteriorDerivative (alpha ty.1)) (c.symm ty.2) := by
    apply M.nondegenerate_of_formInChart _ a hty.1.2.2
    rw [hres ty hty.1.1 hty.1.2.2]
    exact nondegenerate_of_chartContraction_invertible (B ty) hty.2
  have he := M.liouvilleVector_chart_eq (alpha ty.1) a hty.1.2.2 hactual
  rw [hres ty hty.1.1 hty.1.2.2] at he
  exact he

/-- A smooth interval primitive family determines a smooth interval family
of actual intrinsic Liouville fields, including endpoint extensions. -/
theorem isSmoothIntervalVectorFieldFamily_liouvilleVector {d : ℕ} (M : SmoothManifold d)
    (alpha : Parameter → M.Form 1) (halpha : M.IsSmoothIntervalFormFamily alpha)
    (hnd : ∀ t x, M.Nondegenerate (M.exteriorDerivative (alpha t)) x) :
    M.IsSmoothIntervalVectorFieldFamily (fun t => M.liouvilleVector (alpha t)) := by
  obtain ⟨extension, hs, he⟩ := halpha
  refine ⟨fun t => M.liouvilleVector (extension t),
    M.isSmoothVectorFieldFamily_liouvilleVector extension hs ?_, ?_⟩
  · intro t ht x
    rw [he ⟨t, ht⟩]
    exact hnd ⟨t, ht⟩ x
  · intro t
    change M.liouvilleVector (extension t.val) = M.liouvilleVector (alpha t)
    rw [he t]

/-- Any specified contraction solutions agree with the form-determined
fields by nondegeneracy, so primitive-family smoothness also produces the
joint smoothness of these specified geometric fields. -/
theorem isSmoothIntervalVectorFieldFamily_of_liouvilleEquation {d : ℕ} (M : SmoothManifold d)
    (alpha : Parameter → M.Form 1) (halpha : M.IsSmoothIntervalFormFamily alpha)
    (hnd : ∀ t x, M.Nondegenerate (M.exteriorDerivative (alpha t)) x)
    (Z : (t : Parameter) → (x : M.Point) → M.Tangent x)
    (hZ : ∀ t x, M.LiouvilleEquation (alpha t) x (Z t x)) :
    M.IsSmoothIntervalVectorFieldFamily Z := by
  have he : (fun t => M.liouvilleVector (alpha t)) = Z := by
    funext t x
    exact M.liouvilleVector_eq (alpha t) x (hnd t x) (hZ t x)
  rw [← he]
  exact M.isSmoothIntervalVectorFieldFamily_liouvilleVector alpha halpha hnd

end SmoothManifold
end FsFltz.Geometry
