import FsFltz.Geometry.FormCalculus
import FsFltz.Geometry.ToricForms

/-!
# Smooth actual differential forms

Chartwise closure and the manifold chain rule prove smoothness of actual
differentials and the descended angular form. These are foundations for the
prescribed primitives in `sec:data` of `geoemtric-part-fsf.tex`, lines 68–97,
and the bridges in `sec:lean`, lines 778–814. They assert no geometric
comparison or symplecticity.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators ComplexConjugate
open Set

namespace FsFltz.Geometry
namespace SmoothManifold

@[simp] theorem formInChart_zero {d k : ℕ} (M : SmoothManifold d) (a : M.Point) :
    M.formInChart a (0 : M.Form k) = 0 := by
  funext y
  ext v
  rfl

@[simp] theorem formInChart_add {d k : ℕ} (M : SmoothManifold d) (a : M.Point)
    (eta zeta : M.Form k) :
    M.formInChart a (eta + zeta) = M.formInChart a eta + M.formInChart a zeta := by
  funext y
  ext v
  rfl

@[simp] theorem formInChart_sub {d k : ℕ} (M : SmoothManifold d) (a : M.Point)
    (eta zeta : M.Form k) :
    M.formInChart a (eta - zeta) = M.formInChart a eta - M.formInChart a zeta := by
  funext y
  ext v
  rfl

@[simp] theorem formInChart_smul {d k : ℕ} (M : SmoothManifold d) (a : M.Point)
    (c : ℝ) (eta : M.Form k) :
    M.formInChart a (c • eta) = c • M.formInChart a eta := by
  funext y
  ext v
  rfl

theorem isSmoothForm_zero {d k : ℕ} (M : SmoothManifold d) :
    M.IsSmoothForm (0 : M.Form k) := by
  intro a
  rw [formInChart_zero]
  change ContDiffOn ℝ ∞ (fun _ : Model d =>
    (0 : Model d [⋀^Fin k]→L[ℝ] ℝ)) (chartAt (Model d) a).target
  exact contDiffOn_const

theorem IsSmoothForm.add {d k : ℕ} {M : SmoothManifold d} {eta zeta : M.Form k}
    (heta : M.IsSmoothForm eta) (hzeta : M.IsSmoothForm zeta) :
    M.IsSmoothForm (eta + zeta) := by
  intro a
  rw [formInChart_add]
  exact (heta a).add (hzeta a)

theorem IsSmoothForm.sub {d k : ℕ} {M : SmoothManifold d} {eta zeta : M.Form k}
    (heta : M.IsSmoothForm eta) (hzeta : M.IsSmoothForm zeta) :
    M.IsSmoothForm (eta - zeta) := by
  intro a
  rw [formInChart_sub]
  exact (heta a).sub (hzeta a)

theorem IsSmoothForm.smul {d k : ℕ} {M : SmoothManifold d} {eta : M.Form k}
    (heta : M.IsSmoothForm eta) (c : ℝ) : M.IsSmoothForm (c • eta) := by
  intro a
  rw [formInChart_smul]
  exact (contDiffOn_const.smul (heta a) :
    ContDiffOn ℝ ∞ ((fun _ => c) • M.formInChart a eta) (chartAt (Model d) a).target)

theorem IsSmoothForm.sum {d k : ℕ} {M : SmoothManifold d} {ι : Type*}
    (s : Finset ι) (eta : ι → M.Form k) (heta : ∀ i ∈ s, M.IsSmoothForm (eta i)) :
    M.IsSmoothForm (∑ i ∈ s, eta i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isSmoothForm_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (heta i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => heta j (Finset.mem_insert_of_mem hj)))

/-- A smooth scalar- or vector-valued function is smooth in every source chart. -/
theorem contDiffOn_comp_inverseChart {d : ℕ} (M : SmoothManifold d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : M.Point → E}
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) ∞ f) (a : M.Point) :
    ContDiffOn ℝ ∞ (f ∘ (chartAt (Model d) a).symm) (chartAt (Model d) a).target := by
  exact contMDiffOn_iff_contDiffOn.mp
    (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)))

/-- In a chart, the actual manifold differential agrees with the actual
Euclidean differential of the coordinate function. -/
theorem mfderiv_comp_inverseChart {d : ℕ} (M : SmoothManifold d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : M.Point → E}
    (hf : MDifferentiable (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f) (a : M.Point)
    {y : Model d} (hy : y ∈ (chartAt (Model d) a).target) :
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f ((chartAt (Model d) a).symm y)).comp
      (M.inverseChartTangentMap a y) =
        fderiv ℝ (f ∘ (chartAt (Model d) a).symm) y := by
  rw [← mfderiv_eq_fderiv]
  exact (mfderiv_comp y (hf _)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy)).symm

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_mfderiv_comp_inverseChart {d : ℕ} (M : SmoothManifold d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : M.Point → E}
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) ∞ f) (a : M.Point) :
    ContDiffOn ℝ ∞ (F := Model d →L[ℝ] E) (fun y =>
      ((mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, E)) f ((chartAt (Model d) a).symm y)).comp
        (M.inverseChartTangentMap a y) : Model d →L[ℝ] E))
      (chartAt (Model d) a).target := by
  apply ((M.contDiffOn_comp_inverseChart hf a).fderiv_of_isOpen
    (chartAt (Model d) a).open_target (by simp)).congr
  intro y hy
  exact M.mfderiv_comp_inverseChart (hf.mdifferentiable (by simp)) a hy

theorem IsSmoothForm.function_smul {d k : ℕ} {M : SmoothManifold d}
    {eta : M.Form k} (heta : M.IsSmoothForm eta) {f : M.Point → ℝ}
    (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ f) :
    M.IsSmoothForm (fun x => f x • eta x) := by
  intro a
  apply ((M.contDiffOn_comp_inverseChart hf a).smul (heta a)).congr
  intro y _
  ext v
  rfl

end SmoothManifold

/-- Smoothness of a covector field is tested after actual inverse-chart
tangent transport. The conversion to alternating one-forms is a linear isometry. -/
theorem isSmoothForm_covectorForm {d : ℕ} (M : SmoothManifold d)
    (b : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ ∞
      (fun y => (b ((chartAt (Model d) a).symm y)).comp (M.inverseChartTangentMap a y))
      (chartAt (Model d) a).target) : M.IsSmoothForm (covectorForm M b) := by
  intro a
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  apply (e.contDiff.comp_contDiffOn (hb a)).congr
  intro y _
  ext v
  rfl

theorem isSmoothForm_differentialCovector {d : ℕ} (M : SmoothManifold d)
    {f : M.Point → ℝ} (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ∞ f) :
    M.IsSmoothForm (covectorForm M (differentialCovector M f)) := by
  apply isSmoothForm_covectorForm
  intro a
  exact M.contDiffOn_mfderiv_comp_inverseChart hf a

theorem isSmoothForm_complexDifferential_comp {d : ℕ} (M : SmoothManifold d)
    {f : M.Point → ℂ} (hf : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℂ)) ∞ f)
    (L : ℂ →L[ℝ] ℝ) :
    M.IsSmoothForm (covectorForm M (fun x => L.comp (complexDifferential M f x))) := by
  apply isSmoothForm_covectorForm
  intro a
  have hd := M.contDiffOn_mfderiv_comp_inverseChart hf a
  apply ((contDiffOn_const (c := L)).clm_comp hd).congr
  intro y _
  ext v
  rfl

/-- The descended angular form is smooth for every smooth complex map. Its
unit-modulus property is needed for the angular interpretation, not smoothness. -/
theorem isSmoothForm_phaseCovector {d : ℕ} (M : SmoothManifold d)
    {q : M.Point → ℂ} (hq : ContMDiff (𝓘(ℝ, Model d)) (𝓘(ℝ, ℂ)) ∞ q) :
    M.IsSmoothForm (covectorForm M (phaseCovector M q)) := by
  apply isSmoothForm_covectorForm
  intro a
  have hq' := M.contDiffOn_comp_inverseChart hq a
  have hconj := Complex.conjCLE.contDiff.comp_contDiffOn hq'
  have hmul : ContDiffOn ℝ ∞ (fun y => conj (q ((chartAt (Model d) a).symm y)) •
      ContinuousLinearMap.id ℝ ℂ) (chartAt (Model d) a).target :=
    hconj.smul contDiffOn_const
  have hd := M.contDiffOn_mfderiv_comp_inverseChart hq a
  have hcomp := (contDiffOn_const (c := Complex.imCLM)).clm_comp (hmul.clm_comp hd)
  apply hcomp.congr
  intro y _
  ext v
  rfl

end FsFltz.Geometry
