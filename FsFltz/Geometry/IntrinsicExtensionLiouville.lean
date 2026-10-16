import FsFltz.Geometry.IntrinsicPrimitiveExtension

/-!
# The actual Liouville field under an intrinsic extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Full primitive and exterior-derivative pullback laws determine
the ambient Liouville vector on the entire native carrier, including its
boundary. Surjectivity of the actual inclusion differential supplies every
ambient test vector in the contraction equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The canonical ambient contraction field is the actual differential image
of the native field, as forced by the two full pullback identities. -/
theorem liouvilleVector_extension_eq
    (N : SmoothManifold (k + 1)) (i : M → N.Point)
    (α : Form k M 1) (lam : N.Form 1)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hprim : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x)
    (hderiv : ∀ x, (N.exteriorDerivative lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = exteriorDerivative α x)
    (x : M)
    (hsurj : Function.Surjective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hambient : N.Nondegenerate (N.exteriorDerivative lam) (i x)) :
    N.liouvilleVector lam (i x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
        (liouvilleVector α (exteriorDerivative α) x) := by
  apply N.liouvilleVector_eq lam (i x) hambient
  intro v
  obtain ⟨w, rfl⟩ := hsurj v
  have hZ := contraction_liouvilleVector α (exteriorDerivative α) hnd x w
  have hd := congrArg (fun eta => eta ![liouvilleVector α (exteriorDerivative α) x, w])
    (hderiv x)
  have hp := congrArg (fun eta => eta ![w]) (hprim x)
  change N.exteriorDerivative lam (i x)
      ![mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector α (exteriorDerivative α) x),
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x w] =
      lam (i x) (fun _ => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x w)
  convert hd.trans (hZ.trans hp.symm) using 1
  · apply congrArg (N.exteriorDerivative lam (i x))
    funext j
    fin_cases j <;> rfl
  · apply congrArg (lam (i x))
    funext j
    fin_cases j; rfl

end FsFltz.Geometry.IntrinsicLiouville
