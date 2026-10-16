import FsFltz.Geometry.CommonEmbeddingCompactMap
import FsFltz.Geometry.SmoothEmbeddingFactorization

/-!
# The actual open image of a same-dimensional smooth embedding

Source: `geoemtric-part-fsf.tex`, `g:initial`, lines 373–384, and
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
The given native ambient embedding identifies its source with its actual
open image. This supplies the diffeomorphism needed to restrict and pull
back the ambient grading, without assuming a smooth inverse or surjectivity.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Function

namespace FsFltz.Geometry.SmoothManifold.SmoothEmbedding

variable {d : ℕ} {M N : SmoothManifold d} (j : M.SmoothEmbedding N)

/-- The open image of the actual same-dimensional smooth embedding. -/
def openRange : TopologicalSpace.Opens N.Point :=
  ⟨range j.map, j.isLocalDiffeomorph.image.isOpen⟩

/-- The actual embedding is a diffeomorphism onto its open image.
The inverse is continuous in the induced topology and smooth by the
proved factorization theorem for smooth embeddings. -/
def rangeDiffeomorph : M.SmoothEquiv (N.restrict j.openRange) := by
  let e : M.Point ≃ (N.restrict j.openRange).Point :=
    Equiv.ofInjective j.map j.embedding.injective
  have hcomp : j.map ∘ e.symm = (Subtype.val : j.openRange → N.Point) := by
    funext y
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have hcont : Continuous e.symm := j.embedding.isInducing.continuous_iff.mpr (by
    rw [hcomp]
    exact continuous_subtype_val)
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff j.openRange e).mp
    exact j.map.contMDiff
  · exact contMDiff_of_comp_smoothEmbedding M (N.restrict j.openRange) N j hcont (by
      rw [hcomp]
      exact contMDiff_subtype_val)

@[simp]
theorem rangeDiffeomorph_val (x : M.Point) :
    (j.rangeDiffeomorph x).val = j.map x := rfl

@[simp]
theorem map_rangeDiffeomorph_symm (y : (N.restrict j.openRange).Point) :
    j.map (j.rangeDiffeomorph.symm y) = y.val := by
  exact congrArg Subtype.val (j.rangeDiffeomorph.apply_symm_apply y)

end FsFltz.Geometry.SmoothManifold.SmoothEmbedding
