import FsFltz.Analysis.OriginalRegularFiber
import FsFltz.Geometry.RegularFiberManifold

/-!
# The smooth full original far fiber

Source: `geoemtric-part-fsf.tex`, `g:initial`, lines 373–379, and
`geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 923–930.
Far-fiber regularity constructs an actual smooth embedded manifold of real
dimension `2 * n - 2`, with image exactly `FullFiber I R`. This supplies the
manifold and embedding needed by `FullFiberModel`; symplectic restriction,
intrinsic completeness and the inclusion-induced marking remain separate
geometric obligations.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false

/-- The literal full far fiber is a smooth embedded manifold of the expected
real dimension. Its manifold and embedding are conclusions of the original
toric regularity estimate, including in rank one. -/
theorem exists_original_farFiber_smoothEmbedding {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R) :
    ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = FullFiber I R := by
  have h := exists_regularLevel_embedding (lgManifold n) (W I) (R : ℂ)
    (contMDiff_W_lgManifold I) (original_W_far_regularValue I hamb hR)
  rw [Complex.finrank_real_complex] at h
  exact h

/-- For the actual far-fiber inclusion, tangent vectors are exactly the
kernel of the actual native differential of `W`. This statement applies to
any of the smooth embeddings with the required literal image. -/
theorem original_farFiber_embedding_tangent_range {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) (x : N.Point) :
    (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker := by
  have h := @regularLevel_embedding_tangent_range (2 * n) (lgManifold n) ℂ
    inferInstance inferInstance inferInstance (W I) (R : ℂ)
    (contMDiff_W_lgManifold I) (original_W_far_regularValue I hamb hR)
  rw [Complex.finrank_real_complex] at h
  exact h j himage x

end FsFltz.Geometry
