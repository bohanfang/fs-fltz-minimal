import FsFltz.Geometry.TailoringCompletedGradingTransport

/-!
# Native tensor formula for actual same-dimensional embedding pullback

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2089.
The constructed open-image diffeomorphism retains the actual embedding
and its actual native tangent derivative in every tensor slot.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The actual open-image diffeomorphism has the native embedding's
derivative in the common tangent model. -/
theorem SmoothManifold.SmoothEmbedding.mfderiv_rangeDiffeomorph {d : ℕ}
    {M N : SmoothManifold d} (j : M.SmoothEmbedding N) (x : M.Point) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.rangeDiffeomorph x =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map x := by
  have h := mfderiv_comp (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
    (I'' := 𝓘(ℝ, Model d)) (f := j.rangeDiffeomorph)
    (g := (Subtype.val : j.openRange → N.Point)) x
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
    (j.rangeDiffeomorph.contMDiff.mdifferentiableAt (by simp))
  erw [N.mfderiv_restrict_val j.openRange, ContinuousLinearMap.id_comp] at h
  exact h.symm

theorem MaslovFamily.pullbackPrimitiveEmbedding_tensor_apply {n : ℕ}
    {M N : SmoothManifold (2 * n)} {α : ℝ → N.Form 1}
    (s : MaslovFamily N (fun t => N.exteriorDerivative (α t)))
    (hα : ∀ t ∈ parameterInterval, N.IsSmoothForm (α t))
    (j : M.SmoothEmbedding N) (t : ℝ) (x : M.Point) :
    (s.pullbackPrimitiveEmbedding hα j).tensor t x =
      (s.tensor t (j.map x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) j.map x) := by
  change (s.tensor t (j.map x)).compContinuousLinearMap
    (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) j.rangeDiffeomorph x) = _
  rw [j.mfderiv_rangeDiffeomorph]

end FsFltz.Geometry
