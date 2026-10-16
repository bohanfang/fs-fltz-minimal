import FsFltz.Analysis.OriginalFiberProjection
import FsFltz.Geometry.ProperExhaustionCompleteFlow
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Target

/-!
# Complete intrinsic flow of the original full far fiber

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 803–812,
and `prop:allinitial`, lines 923–930; `geoemtric-part-fsf.tex`, `g:initial`,
lines 373–379. The literal fiber is closed, so the ambient quadratic
potential restricts to a proper exhaustion. Its actual intrinsic Liouville
derivative has the proved linear bound, yielding a constructed all-real
smooth flow. The resulting `FullFiberModel` realizes the whole actual fiber
with the literal restricted primitive; a compact ribbon and its marking
are separate subsequent constructions.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Function

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- The actual full-fiber embedding is closed. Consequently the ambient
compact quadratic sublevels pull back to compact intrinsic sublevels. -/
theorem isCompact_originalFiber_phi0_sublevel {n d : ℕ} (I : ToricInput n)
    {R : ℝ} {N : SmoothManifold d} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) (A : ℝ) (hA : 0 ≤ A) :
    IsCompact {x : N.Point | phi0 (j.map x) ≤ A} := by
  have hclosed : IsClosed (Set.range j.map) := by
    rw [himage]
    exact isClosed_eq (continuous_W I) continuous_const
  have hj : Topology.IsClosedEmbedding j.map := ⟨j.embedding, hclosed⟩
  exact hj.isCompact_preimage (isCompact_phi0_sublevel A hA)

/-- The intrinsic Liouville field on every actual smooth full far-fiber
realization has an actual complete jointly smooth flow. Properness comes
from the closed literal fiber; the intrinsic derivative bound is proved
from its radial projection, with no flow supplied as input. -/
theorem exists_originalFiberCompleteLiouvilleFlow {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) :
    Nonempty (CompleteLiouvilleFlow N
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)))) := by
  have hμ := N.isSmoothForm_pullback_one (lgManifold n) j.map (lambda0Form n)
    (isSmoothForm_lambda0Form n)
  have hsymp := isSymplecticOn_original_farFiber I hamb hR j himage
  have hfield := N.isSmoothVectorField_liouvilleVector _ hμ (fun x => hsymp.2.2 x (mem_univ _))
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ (phi0 ∘ j.map) :=
    contMDiff_original_phi0.comp j.map.contMDiff
  exact N.exists_completeFlow_of_proper_exhaustion _ hfield (phi0 ∘ j.map) hρ
    (fun x => div_nonneg (realSquaredNorm_nonneg (j.map x).1) (by norm_num))
    (isCompact_originalFiber_phi0_sublevel I j himage) (by norm_num : (0 : ℝ) < 2)
    (scalarDerivative_phi0_original_farFiber_growth I hamb hR j himage)

/-- The literal original fiber primitive with its constructed complete
intrinsic flow, on the very smooth manifold supplied by its embedding. -/
def originalFiberCompletePrimitive {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) :
    CompletePrimitive N (N.pullback (lgManifold n) j.map (lambda0Form n)) where
  smooth_primitive := N.isSmoothForm_pullback_one (lgManifold n) j.map (lambda0Form n)
    (isSmoothForm_lambda0Form n)
  symplectic := isSymplecticOn_original_farFiber I hamb hR j himage
  smooth_field := N.isSmoothVectorField_liouvilleVector _
    (N.isSmoothForm_pullback_one (lgManifold n) j.map (lambda0Form n)
      (isSmoothForm_lambda0Form n))
    (fun x => (isSymplecticOn_original_farFiber I hamb hR j himage).2.2 x (mem_univ _))
  contraction := fun x => N.liouvilleVector_contraction _ x
    (N.liouvilleEquation_exists _ x
      ((isSymplecticOn_original_farFiber I hamb hR j himage).2.2 x (mem_univ _)))
  completeFlow := Classical.choice (exists_originalFiberCompleteLiouvilleFlow I hamb hR j himage)

/-- The whole original far fiber with all of the fixed `FullFiberModel`
data: actual manifold, embedding, literal image and primitive, regular value,
and complete intrinsic Liouville flow. No component is supplied as a target
shaped assumption. This does not yet construct its compact ribbon marking. -/
def originalFullFiberModel {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R) : FullFiberModel I R := by
  apply Classical.choice
  obtain ⟨N, j, himage⟩ := exists_original_farFiber_smoothEmbedding I hamb hR
  exact ⟨{
    ambient := (originalFiberCompletePrimitive I hamb hR j himage).toCompleteLiouvilleManifold
    embedding := j
    image := himage
    primitive := rfl
    regularValue := original_W_far_regularValue I hamb hR }⟩

/-- A full-fiber witness exists throughout the prescribed far-value range. -/
theorem exists_originalFullFiberModel {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R) : Nonempty (FullFiberModel I R) :=
  ⟨originalFullFiberModel I hamb hR⟩

end FsFltz.Geometry
