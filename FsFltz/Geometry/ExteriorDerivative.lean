import FsFltz.Geometry.FormCalculus

/-!
# Intrinsic exterior-derivative calculus

The chart-defined derivative in `Smooth.lean` has its expected expression in
every chart, preserves smoothness, squares to zero, and commutes with pullback
by smooth maps. These prove differential-form foundation bridges required by
the conventions and `sec:lean` of `geoemtric-part-fsf.tex`, lines 119–130 and
805–814; geometric existence remains pending.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.SmoothManifold

/-- The exterior derivative transforms by the differential of a chart change.
The coordinate identity holds on an open overlap before it is differentiated. -/
theorem extDeriv_formInChart_change {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) (a b : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target)
    (hb : (chartAt (Model d) a).symm y ∈ (chartAt (Model d) b).source) :
    extDeriv (M.formInChart a eta) y =
      (extDeriv (M.formInChart b eta)
        (chartAt (Model d) b ((chartAt (Model d) a).symm y))).compContinuousLinearMap
        (fderiv ℝ (chartAt (Model d) b ∘ (chartAt (Model d) a).symm) y) := by
  let ca := chartAt (Model d) a
  let cb := chartAt (Model d) b
  have hA : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ ca.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (ca.open_target.mem_nhds hy)
  have hB : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ cb (ca.symm y) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := b)).contMDiffAt
      (cb.open_source.mem_nhds hb)
  have hCoeff : DifferentiableAt ℝ (M.formInChart b eta) ((cb ∘ ca.symm) y) :=
    ((heta b).contDiffAt (cb.open_target.mem_nhds (cb.map_source hb))).differentiableAt
      (by simp)
  have hnb : ∀ᶠ z in nhds y, ca.symm z ∈ cb.source :=
    (ca.continuousAt_symm hy).preimage_mem_nhds (cb.open_source.mem_nhds hb)
  have hlocal : M.formInChart a eta =ᶠ[nhds y]
      fun z => (M.formInChart b eta ((cb ∘ ca.symm) z)).compContinuousLinearMap
        (fderiv ℝ (cb ∘ ca.symm) z) := by
    filter_upwards [ca.open_target.mem_nhds hy, hnb] with z hz hzb
    simpa only [pullback_id, Function.comp_id, Function.id_comp, Function.comp_apply,
      id_eq, ca, cb] using
      M.formInChart_pullback M (f := id) eta a b z hz hzb
        (mdifferentiableAt_id (I := 𝓘(ℝ, Model d)))
  rw [hlocal.extDeriv_eq]
  exact extDeriv_pullback hCoeff (hB.comp y hA).contDiffAt (by simp)

/-- A smooth form's intrinsic exterior derivative may be computed in any
chart whose source contains the point. -/
theorem exteriorDerivative_eq_in_chart {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) (a x : M.Point)
    (hx : x ∈ (chartAt (Model d) a).source) :
    M.exteriorDerivative eta x =
      (extDeriv (M.formInChart a eta) (chartAt (Model d) a x)).compContinuousLinearMap
        (M.chartTangentMap a x) := by
  let c := chartAt (Model d) x
  let b := chartAt (Model d) a
  have hcx : x ∈ c.source := mem_chart_source _ _
  have hcy : c x ∈ c.target := c.map_source hcx
  have hc : c.symm (c x) = x := c.left_inv hcx
  change (extDeriv (M.formInChart x eta) (c x)).compContinuousLinearMap
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c x) = _
  have hba : c.symm (c x) ∈ b.source := by simpa only [hc] using hx
  rw [M.extDeriv_formInChart_change eta heta x a (c x) hcy hba]
  rw [← mfderiv_eq_fderiv]
  have hC := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).mdifferentiableAt_symm hcy
  have hB : MDifferentiableAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) b (c.symm (c x)) := by
    rw [hc]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt hx
  rw [mfderiv_comp (c x) hB hC]
  erw [hc]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hcx
  apply ContinuousAlternatingMap.ext
  intro vs
  change (extDeriv (M.formInChart a eta) (b x))
      (fun i => (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) b x)
        ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c.symm (c x))
          ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c x) (vs i)))) = _
  apply congrArg (extDeriv (M.formInChart a eta) (b x))
  funext i
  exact congrArg (fun v => (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) b x) v)
    (congrArg (fun L => L (vs i)) hinv)

/-- On the open target of a fixed chart, taking the intrinsic exterior
derivative agrees with taking the Euclidean derivative of its coefficients. -/
theorem formInChart_exteriorDerivative {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) (a : M.Point) (y : Model d)
    (hy : y ∈ (chartAt (Model d) a).target) :
    M.formInChart a (M.exteriorDerivative eta) y = extDeriv (M.formInChart a eta) y := by
  let c := chartAt (Model d) a
  unfold formInChart
  rw [M.exteriorDerivative_eq_in_chart eta heta a (c.symm y) (c.map_target hy)]
  rw [c.right_inv hy]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).comp_symm_deriv hy
  apply ContinuousAlternatingMap.ext
  intro vs
  change (extDeriv (M.formInChart a eta) y)
      (fun i => (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c (c.symm y))
        ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c.symm y) (vs i))) = _
  apply congrArg (extDeriv (M.formInChart a eta) y)
  funext i
  exact congrArg (fun L => L (vs i)) hinv

/-- The exterior derivative of a smooth intrinsic form is smooth. -/
theorem isSmoothForm_exteriorDerivative {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) :
    M.IsSmoothForm (M.exteriorDerivative eta) := by
  intro a
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (M.formInChart a eta))
      (chartAt (Model d) a).target :=
    (heta a).fderiv_of_isOpen (chartAt (Model d) a).open_target (by simp)
  have he : ContDiffOn ℝ ∞ (extDeriv (M.formInChart a eta))
      (chartAt (Model d) a).target := by
    change ContDiffOn ℝ ∞
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (Model d) ℝ) ∘
        fderiv ℝ (M.formInChart a eta)) (chartAt (Model d) a).target
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM
      (n := k) ℝ (Model d) ℝ).contDiff.comp_contDiffOn hd
  exact he.congr (fun y hy => M.formInChart_exteriorDerivative eta heta a y hy)

/-- The second intrinsic exterior derivative of a smooth form vanishes.
This is an identity of actual derivatives, with no closedness certificate
included in the definition of a smooth form. -/
theorem exteriorDerivative_exteriorDerivative {d k : ℕ} (M : SmoothManifold d)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) :
    M.exteriorDerivative (M.exteriorDerivative eta) = 0 := by
  funext x
  let c := chartAt (Model d) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy : c x ∈ c.target := c.map_source hx
  have hlocal : M.formInChart x (M.exteriorDerivative eta) =ᶠ[nhds (c x)]
      extDeriv (M.formInChart x eta) := by
    filter_upwards [c.open_target.mem_nhds hy] with y hyt
    exact M.formInChart_exteriorDerivative eta heta x y hyt
  change (extDeriv (M.formInChart x (M.exteriorDerivative eta)) (c x)).compContinuousLinearMap
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) c x) = 0
  rw [hlocal.extDeriv_eq,
    extDeriv_extDeriv_apply ((heta x).contDiffAt (c.open_target.mem_nhds hy)) (by simp)]
  apply ContinuousAlternatingMap.ext
  intro vs
  rfl

/-- For a smooth primitive, the smoothness and closedness conditions on its
actual differential are theorems; exact symplecticity only requires checking
pointwise nondegeneracy. -/
theorem isSymplecticOn_exteriorDerivative_iff {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha) (s : Set M.Point) :
    M.IsSymplecticOn (M.exteriorDerivative alpha) s ↔
      ∀ x ∈ s, M.Nondegenerate (M.exteriorDerivative alpha) x := by
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨M.isSmoothForm_exteriorDerivative alpha halpha,
      fun x _ => congrFun (M.exteriorDerivative_exteriorDerivative alpha halpha) x, h⟩

/-- The intrinsic exterior derivative commutes with pullback from a normed
space. This applies directly to quotient covering maps and local coordinate
parametrizations, without introducing an auxiliary bundled manifold. -/
theorem exteriorDerivative_pullback_from_normedSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ} (M : SmoothManifold d)
    (f : E → M.Point) (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, Model d)) ∞ f)
    (eta : M.Form k) (heta : M.IsSmoothForm eta) (x : E) :
    extDeriv (fun z => (eta (f z)).compContinuousLinearMap
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, Model d)) f z)) x =
      (M.exteriorDerivative eta (f x)).compContinuousLinearMap
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, Model d)) f x) := by
  let b := chartAt (Model d) (f x)
  have hx : f x ∈ b.source := mem_chart_source _ _
  have hB : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hCoeff : DifferentiableAt ℝ (M.formInChart (f x) eta) ((b ∘ f) x) :=
    ((heta (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))).differentiableAt
      (by simp)
  have hnb : ∀ᶠ z in nhds x, f z ∈ b.source :=
    hf.continuous.continuousAt.preimage_mem_nhds (b.open_source.mem_nhds hx)
  have hlocal : (fun z => (eta (f z)).compContinuousLinearMap
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, Model d)) f z)) =ᶠ[nhds x]
      fun z => (M.formInChart (f x) eta ((b ∘ f) z)).compContinuousLinearMap
        (fderiv ℝ (b ∘ f) z) := by
    filter_upwards [hnb] with z hz
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp z ((mdifferentiable_chart (I := 𝓘(ℝ, Model d))
        (f x)).mdifferentiableAt hz) (hf.mdifferentiableAt (by simp))]
    rw [← M.formInChart_comp_chartTangentMap eta (f x) (f z) hz]
    apply ContinuousAlternatingMap.ext
    intro vs
    rfl
  erw [hlocal.extDeriv_eq,
    extDeriv_pullback hCoeff (hB.comp x hf.contMDiffAt).contDiffAt (by simp)]
  erw [← mfderiv_eq_fderiv,
    mfderiv_comp x (hB.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  apply ContinuousAlternatingMap.ext
  intro vs
  rfl

/-- The Euclidean exterior derivative of the chart coefficients of a pullback.
The proof obtains equality on a neighborhood, rather than differentiating a
merely pointwise coordinate identity. -/
theorem extDeriv_formInChart_pullback {d e k : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (f : M.SmoothMap N) (eta : N.Form k)
    (heta : N.IsSmoothForm eta) (x : M.Point) :
    extDeriv (M.formInChart x (M.pullback N f eta)) (chartAt (Model d) x x) =
      (extDeriv (N.formInChart (f x) eta)
        (chartAt (Model e) (f x) (f x))).compContinuousLinearMap
        (fderiv ℝ (chartAt (Model e) (f x) ∘ f ∘ (chartAt (Model d) x).symm)
          (chartAt (Model d) x x)) := by
  let a := chartAt (Model d) x
  let b := chartAt (Model e) (f x)
  let y := a x
  have hx : x ∈ a.source := mem_chart_source _ _
  have hy : y ∈ a.target := a.map_source hx
  have hay : a.symm y = x := a.left_inv hx
  have hbx : f x ∈ b.source := mem_chart_source _ _
  have hby : b (f x) ∈ b.target := b.map_source hbx
  have hA : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) ∞ a.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (a.open_target.mem_nhds hy)
  have hB : ContMDiffAt (𝓘(ℝ, Model e)) (𝓘(ℝ, Model e)) ∞ b (f (a.symm y)) := by
    rw [hay]
    exact (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hbx)
  have hF : ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) ∞ f (a.symm y) := by
    rw [hay]
    exact f.contMDiff.contMDiffAt
  have hFB := hB.comp y (hF.comp y hA)
  have hCoeff : DifferentiableAt ℝ (N.formInChart (f x) eta) ((b ∘ f ∘ a.symm) y) := by
    simpa only [Function.comp_apply, hay] using
      ((heta (f x)).contDiffAt (b.open_target.mem_nhds hby)).differentiableAt (by simp)
  have hnb : ∀ᶠ z in nhds y, f (a.symm z) ∈ b.source := by
    have hc : ContinuousAt (f ∘ a.symm) y :=
      f.contMDiff.continuous.continuousAt.comp (a.continuousAt_symm hy)
    apply hc.preimage_mem_nhds
    simpa only [Function.comp_apply, hay] using b.open_source.mem_nhds hbx
  have hlocal : M.formInChart x (M.pullback N f eta) =ᶠ[nhds y]
      fun z => (N.formInChart (f x) eta ((b ∘ f ∘ a.symm) z)).compContinuousLinearMap
        (fderiv ℝ (b ∘ f ∘ a.symm) z) := by
    filter_upwards [a.open_target.mem_nhds hy, hnb] with z hz hzb
    exact M.formInChart_pullback N eta x (f x) z hz hzb
      (f.contMDiff.mdifferentiableAt (by simp))
  rw [hlocal.extDeriv_eq]
  simpa only [Function.comp_apply, hay] using
    extDeriv_pullback hCoeff hFB.contDiffAt (by simp)

/-- Exterior derivative commutes with the actual tangent pullback of a smooth
map. No derivative-naturality certificate is added to the map or the form. -/
theorem exteriorDerivative_pullback {d e k : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.SmoothMap N) (eta : N.Form k) (heta : N.IsSmoothForm eta) :
    M.exteriorDerivative (M.pullback N f eta) =
      M.pullback N f (N.exteriorDerivative eta) := by
  funext x
  change (extDeriv (M.formInChart x (M.pullback N f eta))
      (chartAt (Model d) x x)).compContinuousLinearMap
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) (chartAt (Model d) x) x) =
    ((extDeriv (N.formInChart (f x) eta) (chartAt (Model e) (f x) (f x))).compContinuousLinearMap
      (mfderiv (𝓘(ℝ, Model e)) (𝓘(ℝ, Model e)) (chartAt (Model e) (f x)) (f x))).compContinuousLinearMap
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x)
  rw [M.extDeriv_formInChart_pullback N f eta heta x]
  rw [← mfderiv_eq_fderiv]
  let a := chartAt (Model d) x
  let b := chartAt (Model e) (f x)
  have hx : x ∈ a.source := mem_chart_source _ _
  have hy : a x ∈ a.target := a.map_source hx
  have hay : a.symm (a x) = x := a.left_inv hx
  have hbx : f x ∈ b.source := mem_chart_source _ _
  have hA := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).mdifferentiableAt_symm hy
  have hF := f.contMDiff.mdifferentiableAt (x := a.symm (a x)) (by simp)
  have hB : MDifferentiableAt (𝓘(ℝ, Model e)) (𝓘(ℝ, Model e)) b (f (a.symm (a x))) := by
    rw [hay]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Model e)) (f x)).mdifferentiableAt hbx
  have hchain := mfderiv_comp (a x) hB (hF.comp (a x) hA)
  rw [hchain, mfderiv_comp (a x) hF hA]
  simp only [Function.comp_apply]
  erw [hay]
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm_comp_deriv hx
  apply ContinuousAlternatingMap.ext
  intro vs
  change (extDeriv (N.formInChart (f x) eta) (b (f x)))
    (fun i => (mfderiv (𝓘(ℝ, Model e)) (𝓘(ℝ, Model e)) b (f x))
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x)
        ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) a.symm (a x))
          ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)) a x) (vs i))))) = _
  apply congrArg (extDeriv (N.formInChart (f x) eta) (b (f x)))
  funext i
  exact congrArg
    (fun v => (mfderiv (𝓘(ℝ, Model e)) (𝓘(ℝ, Model e)) b (f x))
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x) v))
    (congrArg (fun L => L (vs i)) hinv)

end FsFltz.Geometry.SmoothManifold
