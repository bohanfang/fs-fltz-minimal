import FsFltz.Geometry.MaslovPullback

/-!
# Grading endpoint transport through an original native slice

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–240;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
The original completion and the represented completion may use unequal
tangent models. The derivative of the original endpoint comparison cancels
the derivative of the actual native slice inverse. Thus original endpoint
identification laws imply the represented presentation pullbacks.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- The original endpoint comparison, followed by the actual inverse slice,
has exactly the differential of the completion presentation. -/
theorem nativeSlice_presentation_mfderiv_comp {d n : ℕ}
    (X : SmoothManifold d) (M N : SmoothManifold (2 * n))
    (S : X.SmoothEquiv M) (P : M.SmoothEquiv N) (y : M.Point) :
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) (S.symm y)).comp
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y) =
        mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) P y := by
  have he : (S.trans P) ∘ S.symm = P := by
    funext z
    exact congrArg P (S.apply_symm_apply z)
  rw [← mfderiv_comp y ((S.trans P).mdifferentiable (by simp) (S.symm y))
    (S.symm.mdifferentiable (by simp) y), he]

/-- Native endpoint intertwinement transports to the prescribed represented
complex field. No represented endpoint equation is a premise. -/
theorem inverseNativeComplex_eq_presentationPullback {d n : ℕ}
    (X : SmoothManifold d) (M N : SmoothManifold (2 * n))
    (S : X.SmoothEquiv M) (P : M.SmoothEquiv N)
    (Jnative : AlmostComplexField X) (J : AlmostComplexField N)
    (hJ : ∀ x v,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x (Jnative x v) =
        J ((S.trans P) x)
          (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x v)) :
    (fun y => (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y).inverse.comp
      ((Jnative (S.symm y)).comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y))) =
      pullbackAlmostComplex M N P J := by
  funext y
  apply ContinuousLinearMap.ext
  intro v
  apply (P.isInvertible_mfderiv (by simp)).injective
  let D : Model (2 * n) →L[ℝ] Model d :=
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y
  let E : Model d →L[ℝ] Model (2 * n) :=
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) (S.symm y)
  let A : Model (2 * n) →L[ℝ] Model (2 * n) :=
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) P y
  have hD : D.IsInvertible := S.symm.isInvertible_mfderiv (by simp)
  have hcomp : E.comp D = A := nativeSlice_presentation_mfderiv_comp X M N S P y
  change A (D.inverse (Jnative (S.symm y) (D v))) =
    A (pullbackAlmostComplex M N P J y v)
  calc
    _ = E (Jnative (S.symm y) (D v)) := by
      rw [← hcomp]
      simp only [ContinuousLinearMap.comp_apply, hD.self_apply_inverse]
    _ = J (P y) (E (D v)) := by
      have h := hJ (S.symm y) (D v)
      change E (Jnative (S.symm y) (D v)) = J (P (S (S.symm y))) (E (D v)) at h
      rw [S.apply_symm_apply] at h
      exact h
    _ = J (P y) (A v) := congrArg (J (P y)) (congrArg (fun f => f v) hcomp)
    _ = _ := (pullbackAlmostComplex_intertwines M N P J y v).symm

/-- Full canonical-square tensors transport in every tangent slot along the
same actual native endpoint comparison. -/
theorem inverseNativeTensor_eq_presentationPullback {d n : ℕ}
    (X : SmoothManifold d) (M N : SmoothManifold (2 * n))
    (S : X.SmoothEquiv M) (P : M.SmoothEquiv N)
    (Tnative : X.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ)
    (T : N.Point → SquaredCanonicalTensor n)
    (hT : ∀ x, Tnative x = (T ((S.trans P) x)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x)) :
    (fun y => (Tnative (S.symm y)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y)) =
      pullbackSquaredTensor M N P T := by
  funext y
  rw [hT]
  ext v
  have hcomp := nativeSlice_presentation_mfderiv_comp X M N S P y
  change T (P (S (S.symm y)))
    (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) (S.symm y)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y (v i))) = _
  rw [S.apply_symm_apply]
  apply congrArg (T (P y))
  funext i
  exact congrArg (fun f => f (v i)) hcomp

end FsFltz.Geometry
