import FsFltz.Geometry.Identification
import FsFltz.Geometry.ExteriorDerivative
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Liouville fields under primitive-preserving maps

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and `sec:lean`,
lines 805–814. The contraction equation and exterior-derivative naturality
force a strict ambient diffeomorphism to carry the Liouville field to the
Liouville field. Flow equivariance and construction of the induced boundary
map remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

/-- A primitive-preserving diffeomorphism between completed Liouville
manifolds intertwines their actual fields. No field equation for the map is
an extra hypothesis. -/
theorem CompleteLiouvilleManifold.map_field {d e : ℕ}
    (X : CompleteLiouvilleManifold d) (Y : CompleteLiouvilleManifold e)
    (f : X.manifold.SmoothEquiv Y.manifold)
    (hprimitive : X.manifold.pullback Y.manifold f Y.primitive = X.primitive)
    (x : X.manifold.Point) :
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x) = Y.field (f x) := by
  apply Y.manifold.liouvilleEquation_unique Y.primitive (f x)
    (Y.symplectic.2.2 (f x) (Set.mem_univ _)) _ (Y.contraction (f x))
  intro w
  obtain ⟨v, rfl⟩ := (f.mfderivToContinuousLinearEquiv (by simp) x).surjective w
  have hd : X.manifold.exteriorDerivative X.primitive =
      X.manifold.pullback Y.manifold f (Y.manifold.exteriorDerivative Y.primitive) := by
    rw [← hprimitive]
    exact X.manifold.exteriorDerivative_pullback Y.manifold f.toContMDiffMap
      Y.primitive Y.smooth_primitive
  have hd_eval := congrArg (fun eta => evalTwo eta x (X.field x) v) hd
  have hp_eval := congrArg (fun eta => evalOne eta x v) hprimitive
  have hvec : (fun i : Fin 2 =>
      mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (![X.field x, v] i)) =
      ![mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x),
        mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x v] := by
    funext i
    fin_cases i <;> rfl
  simp only [evalTwo, pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hvec] at hd_eval
  change evalTwo (Y.manifold.exteriorDerivative Y.primitive) (f x)
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x (X.field x))
    (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) f x v) = _
  exact hd_eval.symm.trans ((X.contraction x v).trans hp_eval.symm)

/-- In particular the ambient map in each permitted completion step carries
the form-determined Liouville field, as required by `def:chain`, 183–184. -/
theorem CompletionIdentification.map_field {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (x : P.ambientCompletion.ambient.manifold.Point) :
    mfderiv (𝓘(ℝ, Model (2 * n))) (𝓘(ℝ, Model (2 * n))) h.ambientEquiv x
      (P.ambientCompletion.ambient.field x) =
        Q.ambientCompletion.ambient.field (h.ambientEquiv x) :=
  P.ambientCompletion.ambient.map_field Q.ambientCompletion.ambient
    h.ambientEquiv h.primitive x

end FsFltz.Geometry
