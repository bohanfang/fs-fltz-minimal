import FsFltz.Geometry.SymplecticBridge
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Smoothness of the form-determined Liouville vector field

The contraction convention in `sec:data`, `geoemtric-part-fsf.tex`, lines
74–86, defines the actual intrinsic vector. Smoothness follows by inverting
its nondegenerate chartwise contraction map. This proves a foundation in
`sec:lean`, lines 783–814, and asserts no complete flow or end-bound existence.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
namespace SmoothManifold

private theorem comp_pair {E F : Type*} (f : E → F) (v w : E) :
    f ∘ ![v, w] = ![f v, f w] := by
  funext i
  fin_cases i <;> rfl

/-- The Euclidean inner product identifies chart one-forms with chart vectors.
This auxiliary equivalence is used only to invert the contraction map. -/
def chartOneFormEquiv (d : ℕ) :
    Model d ≃L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (Model d)).toContinuousLinearEquiv.trans
    (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv

/-- Contraction in chart coordinates, with the covector codomain identified
with vectors by the fixed Euclidean inner product. -/
def chartContraction {d : ℕ} (omega : Model d [⋀^Fin 2]→L[ℝ] ℝ) :
    Model d →L[ℝ] Model d :=
  (chartOneFormEquiv d).symm.toContinuousLinearMap.comp omega.curryLeft

/-- Nondegeneracy makes the chart contraction operator invertible. -/
theorem chartContraction_invertible {d : ℕ}
    (omega : Model d [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, omega ![v, w] = 0) → v = 0) :
    (chartContraction omega).IsInvertible := by
  have hinj : Function.Injective (chartContraction omega) := by
    intro v w h
    apply sub_eq_zero.mp
    apply hnd
    intro u
    have hz : chartContraction omega (v - w) = 0 := by
      rw [map_sub, h, sub_self]
    have hc : omega.curryLeft (v - w) = 0 := by
      apply (chartOneFormEquiv d).symm.injective
      simpa [chartContraction] using hz
    have he := congrArg (fun alpha => alpha ![u]) hc
    exact he
  exact ⟨ContinuousLinearEquiv.ofBijective (chartContraction omega)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj)), rfl⟩

/-- Nondegeneracy is preserved by the actual inverse-chart tangent transport. -/
theorem nondegenerate_formInChart {d : ℕ} (M : SmoothManifold d)
    (omega : M.Form 2) (a : M.Point) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hnd : M.Nondegenerate omega ((chartAt (Model d) a).symm y)) :
    ∀ v, (∀ w, M.formInChart a omega y ![v, w] = 0) → v = 0 := by
  intro v hv
  let x := (chartAt (Model d) a).symm y
  have hx : x ∈ (chartAt (Model d) a).source :=
    (chartAt (Model d) a).map_target hy
  have hxy : chartAt (Model d) a x = y := (chartAt (Model d) a).right_inv hy
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).comp_symm_deriv hy
  have hz : M.inverseChartTangentMap a y v = 0 := by
    apply hnd
    intro w
    have he := hv (M.chartTangentMap a x w)
    change omega x ((M.inverseChartTangentMap a y) ∘
      ![v, M.chartTangentMap a x w]) = 0 at he
    erw [comp_pair] at he
    have hi : M.inverseChartTangentMap a y (M.chartTangentMap a x w) = w := by
      have hi0 := congrArg (fun L => L w) hinv
      change M.inverseChartTangentMap a (chartAt (Model d) a x)
        (M.chartTangentMap a x w) = w at hi0
      erw [hxy] at hi0
      exact hi0
    rw [hi] at he
    exact he
  have he := congrArg (fun L => L v) hc
  change M.chartTangentMap a x (M.inverseChartTangentMap a y v) = v at he
  rw [hz, map_zero] at he
  exact he.symm

/-- Every covector has a unique contraction solution for a nondegenerate
two-form; this includes the zero-dimensional tangent space. -/
theorem liouvilleEquation_exists {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (x : M.Point)
    (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x) :
    ∃ Z, M.LiouvilleEquation alpha x Z := by
  let omega : Model d [⋀^Fin 2]→L[ℝ] ℝ := M.exteriorDerivative alpha x
  let b := (chartOneFormEquiv d).symm (alpha x)
  have hinv := chartContraction_invertible omega hnd
  refine ⟨(chartContraction omega).inverse b, ?_⟩
  have he : omega.curryLeft ((chartContraction omega).inverse b) = alpha x := by
    apply (chartOneFormEquiv d).symm.injective
    change chartContraction omega ((chartContraction omega).inverse b) = b
    exact hinv.self_apply_inverse b
  intro v
  have hv := congrArg (fun beta => beta (fun _ : Fin 1 => v)) he
  convert hv using 1
  · apply congrArg omega
    funext i
    fin_cases i <;> rfl
  · rfl

/-- The actual intrinsic Liouville field satisfies its contraction equation
after transport to any fixed chart. -/
theorem liouvilleVector_chart_contraction {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (a : M.Point) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hnd : M.Nondegenerate (M.exteriorDerivative alpha)
      ((chartAt (Model d) a).symm y)) :
    (M.formInChart a (M.exteriorDerivative alpha) y).curryLeft
      (M.vectorInChart a (M.liouvilleVector alpha) y) = M.formInChart a alpha y := by
  let x := (chartAt (Model d) a).symm y
  have hx : x ∈ (chartAt (Model d) a).source := (chartAt (Model d) a).map_target hy
  have hxy : chartAt (Model d) a x = y := (chartAt (Model d) a).right_inv hy
  have hsol := M.liouvilleVector_contraction alpha x
    (M.liouvilleEquation_exists alpha x hnd)
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  have hZ : M.inverseChartTangentMap a y
      (M.vectorInChart a (M.liouvilleVector alpha) y) = M.liouvilleVector alpha x := by
    have hi := congrArg (fun L => L (M.liouvilleVector alpha x)) hinv
    change M.inverseChartTangentMap a (chartAt (Model d) a x)
      (M.vectorInChart a (M.liouvilleVector alpha) y) = M.liouvilleVector alpha x at hi
    erw [hxy] at hi
    exact hi
  apply ContinuousAlternatingMap.ext
  intro vs
  have hv : vs = ![vs 0] := by
    funext i
    fin_cases i
    rfl
  rw [hv]
  change (M.exteriorDerivative alpha x)
    ((M.inverseChartTangentMap a y) ∘
      ![M.vectorInChart a (M.liouvilleVector alpha) y, vs 0]) =
    alpha x ((M.inverseChartTangentMap a y) ∘ ![vs 0])
  erw [comp_pair, hZ]
  convert hsol (M.inverseChartTangentMap a y (vs 0)) using 1
  · rfl
  · apply congrArg (alpha x)
    funext i
    fin_cases i
    rfl

/-- In a fixed chart, the actual intrinsic Liouville vector is obtained by
inverting the nondegenerate contraction operator. -/
theorem liouvilleVector_chart_eq {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (a : M.Point) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target)
    (hnd : M.Nondegenerate (M.exteriorDerivative alpha)
      ((chartAt (Model d) a).symm y)) :
    M.vectorInChart a (M.liouvilleVector alpha) y =
      (chartContraction (M.formInChart a (M.exteriorDerivative alpha) y)).inverse
        ((chartOneFormEquiv d).symm (M.formInChart a alpha y)) := by
  have hinv := chartContraction_invertible
    (M.formInChart a (M.exteriorDerivative alpha) y)
    (M.nondegenerate_formInChart (M.exteriorDerivative alpha) a hy hnd)
  symm
  apply (hinv.inverse_apply_eq).mpr
  symm
  change (chartOneFormEquiv d).symm
    ((M.formInChart a (M.exteriorDerivative alpha) y).curryLeft
      (M.vectorInChart a (M.liouvilleVector alpha) y)) = _
  rw [M.liouvilleVector_chart_contraction alpha a hy hnd]

/-- The intrinsic field selected by the actual contraction equation is smooth
for every smooth primitive with pointwise nondegenerate differential. -/
theorem isSmoothVectorField_liouvilleVector {d : ℕ} (M : SmoothManifold d)
    (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha)
    (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x) :
    M.IsSmoothVectorField (M.liouvilleVector alpha) := by
  intro a
  let A : Model d → Model d →L[ℝ] Model d :=
    fun y => chartContraction (M.formInChart a (M.exteriorDerivative alpha) y)
  let b : Model d → Model d :=
    fun y => (chartOneFormEquiv d).symm (M.formInChart a alpha y)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A (chartAt (Model d) a).target :=
    contDiffOn_const.clm_comp
      (hcur.comp_contDiffOn (M.isSmoothForm_exteriorDerivative alpha halpha a))
  have hb : ContDiffOn ℝ ∞ b (chartAt (Model d) a).target :=
    (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn (halpha a)
  have hAi : ContDiffOn ℝ ∞ (fun y => (A y).inverse)
      (chartAt (Model d) a).target := by
    intro y hy
    have hinv := chartContraction_invertible
      (M.formInChart a (M.exteriorDerivative alpha) y)
      (M.nondegenerate_formInChart (M.exteriorDerivative alpha) a hy (hnd _))
    exact hinv.contDiffAt_map_inverse.comp_contDiffWithinAt y (hA y hy)
  apply (hAi.clm_apply hb).congr
  intro y hy
  exact M.liouvilleVector_chart_eq alpha a hy (hnd _)

end SmoothManifold

/-- Smoothness of the actual quotient Liouville field for every `K ≥ 0`.
The nondegeneracy and primitive smoothness hypotheses are already proved. -/
theorem isSmoothVectorField_liouvilleVector_lambdaKForm {n : ℕ} (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    (lgManifold n).IsSmoothVectorField ((lgManifold n).liouvilleVector (lambdaKForm I K)) :=
  (lgManifold n).isSmoothVectorField_liouvilleVector (lambdaKForm I K)
    (isSmoothForm_lambdaKForm I K) (nondegenerate_exteriorDerivative_lambdaKForm I hK)

/-- The prescribed canonical cotangent primitive has a smooth intrinsic
Liouville field in every rank, including rank zero. -/
theorem isSmoothVectorField_liouvilleVector_lambdaCanForm (n : ℕ) :
    (cotangentManifold n).IsSmoothVectorField
      ((cotangentManifold n).liouvilleVector (lambdaCanForm n)) :=
  (cotangentManifold n).isSmoothVectorField_liouvilleVector (lambdaCanForm n)
    (isSmoothForm_lambdaCanForm n) nondegenerate_exteriorDerivative_lambdaCanForm

end FsFltz.Geometry
