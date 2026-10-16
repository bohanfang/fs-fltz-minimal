import FsFltz.Geometry.LiouvilleFlowPrimitive

/-!
# Exterior differentiation of a variable scalar times a one-form

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. The actual chart-defined exterior derivative satisfies the
product rule `d(f alpha) = f d(alpha) + df ∧ alpha`. This is proved from
Fréchet differentiation of the chart coefficients and the native manifold
chain rule; no differential formula is supplied as a hypothesis.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry

namespace FormScalarDerivative

/-- The ordinary product rule, evaluated on two vectors, for the actual
exterior derivative of a variable multiple of a one-form on a normed space. -/
theorem extDeriv_variable_smul_one_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (alpha : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x u v : E)
    (hf : DifferentiableAt ℝ f x) (halpha : DifferentiableAt ℝ alpha x) :
    extDeriv (fun y => f y • alpha y) x ![u, v] =
      f x * extDeriv alpha x ![u, v] +
        fderiv ℝ f x u * alpha x (fun _ => v) -
        fderiv ℝ f x v * alpha x (fun _ => u) := by
  change extDeriv (f • alpha) x ![u, v] = _
  rw [LiouvilleFlowPrimitive.extDeriv_one_apply, fderiv_smul hf halpha,
    LiouvilleFlowPrimitive.extDeriv_one_apply]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

end FormScalarDerivative

namespace SmoothManifold

/-- A scalar derivative computed in a native chart is its actual manifold
derivative after applying that chart's tangent map. -/
theorem fderiv_scalar_in_chart {d : ℕ} (M : SmoothManifold d)
    (f : M.Point → ℝ) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f)
    (a x : M.Point) (hx : x ∈ (chartAt (Model d) a).source) (v : M.Tangent x) :
    fderiv ℝ (f ∘ (chartAt (Model d) a).symm) (chartAt (Model d) a x)
      (M.chartTangentMap a x v) = M.scalarDerivative f x v := by
  let c := chartAt (Model d) a
  have hy : c x ∈ c.target := c.map_source hx
  have hi := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy
  have hcomp := mfderiv_comp (c x) (hf.mdifferentiableAt (by simp)) hi
  rw [← mfderiv_eq_fderiv, hcomp, c.left_inv hx]
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) f x)
    ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x))
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c x) v)) = _
  have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx
  exact congrArg (fun z => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) f x z)
    (congrArg (fun L => L v) hinv)

set_option backward.isDefEq.respectTransparency false in
/-- The actual manifold exterior derivative satisfies the variable-scalar
product rule, with both scalar derivatives and one-form evaluations intrinsic. -/
theorem evalTwo_exteriorDerivative_smul {d : ℕ} (M : SmoothManifold d)
    (f : M.Point → ℝ) (alpha : M.Form 1)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ f) (halpha : M.IsSmoothForm alpha)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (fun y => f y • alpha y)) x v w =
      f x * evalTwo (M.exteriorDerivative alpha) x v w +
        M.scalarDerivative f x v * evalOne alpha x w -
        M.scalarDerivative f x w * evalOne alpha x v := by
  let c := chartAt (Model d) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy : c x ∈ c.target := c.map_source hx
  have hci : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm (c x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hfc : DifferentiableAt ℝ (f ∘ c.symm) (c x) :=
    (hf.contMDiffAt.comp (c x) hci).contDiffAt.differentiableAt (by simp)
  have hac : DifferentiableAt ℝ (M.formInChart x alpha) (c x) :=
    ((halpha x).contDiffAt (c.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hcoeff : M.formInChart x (fun y => f y • alpha y) =
      fun y => f (c.symm y) • M.formInChart x alpha y := by
    funext y
    ext vs
    rfl
  have hpair : M.chartTangentMap x x ∘ ![v, w] =
      ![M.chartTangentMap x x v, M.chartTangentMap x x w] := by
    funext i
    fin_cases i <;> rfl
  have htwo : extDeriv (M.formInChart x alpha) (c x)
      ![M.chartTangentMap x x v, M.chartTangentMap x x w] =
      evalTwo (M.exteriorDerivative alpha) x v w := by
    change _ = extDeriv (M.formInChart x alpha) (c x)
      (M.chartTangentMap x x ∘ ![v, w])
    rw [hpair]
  have hone (u : M.Tangent x) : (M.formInChart x alpha (c x))
      (fun _ => M.chartTangentMap x x u) = evalOne alpha x u := by
    exact congrArg (fun beta => beta (fun _ : Fin 1 => u))
      (M.formInChart_comp_chartTangentMap alpha x x hx)
  change extDeriv (M.formInChart x (fun y => f y • alpha y)) (c x)
    (M.chartTangentMap x x ∘ ![v, w]) = _
  rw [hcoeff, hpair]
  erw [FormScalarDerivative.extDeriv_variable_smul_one_apply (f ∘ c.symm)
    (M.formInChart x alpha) (c x) (M.chartTangentMap x x v)
      (M.chartTangentMap x x w) hfc hac]
  simp only [Function.comp_apply]
  erw [c.left_inv hx, htwo, hone, hone,
    M.fderiv_scalar_in_chart f hf x x hx v, M.fderiv_scalar_in_chart f hf x x hx w]

end SmoothManifold

end FsFltz.Geometry
