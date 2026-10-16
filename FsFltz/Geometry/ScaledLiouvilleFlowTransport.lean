import FsFltz.Geometry.FlowBridge
import FsFltz.Geometry.FormScalarDerivative

/-!
# Complete Liouville flows under constant primitive scaling

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 148–160, and
`def:chain`, lines 175–189. A constant scaling of the primitive scales its
exterior derivative by the same constant. The target contraction equation
therefore forces the transported field to be the actual target Liouville
field. Uniqueness of native integral curves then intertwines the supplied
complete flows at every real time.

The construction of a scaled completion equivalence is a separate producer;
neither field nor flow equivariance is an input here. Positivity belongs to
that construction and is not needed for these consequences of its equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- A diffeomorphism with a constant-scaled primitive equation transports
the actual Liouville fields. -/
theorem CompleteLiouvilleManifold.map_field_of_scaled_primitive {d e : ℕ}
    (X : CompleteLiouvilleManifold d) (Y : CompleteLiouvilleManifold e)
    (f : X.manifold.SmoothEquiv Y.manifold) (c : ℝ)
    (hprimitive : X.manifold.pullback Y.manifold f Y.primitive = c • X.primitive)
    (x : X.manifold.Point) :
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x) = Y.field (f x) := by
  apply Y.manifold.liouvilleEquation_unique Y.primitive (f x)
    (Y.symplectic.2.2 (f x) (Set.mem_univ _)) _ (Y.contraction (f x))
  intro w
  obtain ⟨v, rfl⟩ := (f.mfderivToContinuousLinearEquiv (by simp) x).surjective w
  have hd : X.manifold.exteriorDerivative (c • X.primitive) =
      X.manifold.pullback Y.manifold f (Y.manifold.exteriorDerivative Y.primitive) := by
    rw [← hprimitive]
    exact X.manifold.exteriorDerivative_pullback Y.manifold f.toContMDiffMap
      Y.primitive Y.smooth_primitive
  have hs : evalTwo (X.manifold.exteriorDerivative (c • X.primitive))
      x (X.field x) v =
      c * evalTwo (X.manifold.exteriorDerivative X.primitive) x (X.field x) v := by
    change evalTwo (X.manifold.exteriorDerivative (fun y => c • X.primitive y))
      x (X.field x) v = _
    have h := X.manifold.evalTwo_exteriorDerivative_smul (fun _ => c) X.primitive
      contMDiff_const X.smooth_primitive x (X.field x) v
    simpa only [scalarDerivative, mfderiv_const, zero_apply, zero_mul,
      add_zero, sub_zero] using h
  have hd_eval := congrArg (fun eta => evalTwo eta x (X.field x) v) hd
  have hp_eval := congrArg (fun eta => evalOne eta x v) hprimitive
  have hvec : (fun i : Fin 2 =>
      mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (![X.field x, v] i)) =
      ![mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x),
        mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x v] := by
    funext i
    fin_cases i <;> rfl
  rw [hs] at hd_eval
  simp only [evalTwo, pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hvec] at hd_eval
  change evalOne Y.primitive (f x)
      (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x v) =
      c * evalOne X.primitive x v at hp_eval
  change evalTwo (Y.manifold.exteriorDerivative Y.primitive) (f x)
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x))
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x v) = _
  exact hd_eval.symm.trans
    ((congrArg (fun a : ℝ => c * a) (X.contraction x v)).trans hp_eval.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Constant primitive scaling intertwines the actual complete flows at
all real times; no equivariance hypothesis is supplied. -/
theorem CompleteLiouvilleManifold.map_flow_of_scaled_primitive {d e : ℕ}
    (X : CompleteLiouvilleManifold d) (Y : CompleteLiouvilleManifold e)
    (f : X.manifold.SmoothEquiv Y.manifold) (c : ℝ)
    (hprimitive : X.manifold.pullback Y.manifold f Y.primitive = c • X.primitive)
    (x : X.manifold.Point) (t : ℝ) :
    f (X.completeFlow.flow t x) = Y.completeFlow.flow t (f x) := by
  have hleft : IsMIntegralCurve (fun s => f (X.completeFlow.flow s x)) Y.field := by
    intro s
    have h := ((f.contMDiff.mdifferentiable (by simp))
      (X.completeFlow.flow s x)).hasMFDerivAt.comp s (X.completeFlow.isMIntegralCurve x s)
    apply h.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f (X.completeFlow.flow s x)
      (r • X.field (X.completeFlow.flow s x)) = r • Y.field (f (X.completeFlow.flow s x))
    rw [map_smul, X.map_field_of_scaled_primitive Y f c hprimitive]
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (Y.smooth_field.contMDiff_section.of_le (by simp)) hleft
    (Y.completeFlow.isMIntegralCurve (f x)) (by simp only [Flow.map_zero_apply])
  exact congrFun heq t

end FsFltz.Geometry
