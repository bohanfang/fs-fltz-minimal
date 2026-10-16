import FsFltz.Analysis.OriginalPotentialDomain
import FsFltz.Analysis.OriginalFlowAbsorption
import FsFltz.Analysis.OriginalAmbientMargin
import FsFltz.Geometry.FlowAbsorptionMarking
import FsFltz.Target

/-!
# Finite type of the actual original primitive for every nonnegative parameter

Source: `geoemtric-part-fsf.tex`, `thm:target`, `g:complete`, lines 358–361,
and `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818.
The original complete field enters a literal compact quadratic sublevel in
finite negative time. Its native smooth boundary and outwardness construct
an actual completion with identity ambient inclusion and actual boundary
flow. The finite-type witness therefore concerns the fixed original quotient
manifold and primitive. The ambient bound and compact level are conclusions
constructed from the finite toric input, for every real `K ≥ 0`.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- Every quadratic level above a valid ambient end bound supplies an
actual compact Liouville domain whose completion marks the original ambient.
The manifold, primitive and flow are the prescribed original ones. -/
def originalFiniteTypePrimitive {n : ℕ} (I : ToricInput n)
    {K Aamb A : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (hA : Aamb < A) : FiniteTypePrimitive (lgManifold n) (lambdaKForm I K) := by
  let D := originalPotentialLiouvilleDomain I hK hamb hA
  apply FlowAbsorptionMarking.finiteTypeOfSublevelAbsorption D
    (originalCompletePrimitive I hK) phi0 contMDiff_phi0
    (originalPotentialCompactDomain_frontier I hK hamb hA) ?_ rfl ?_
  · intro x hx
    exact scalarDerivative_phi0_originalLiouville_pos I hK hamb x (hA.le.trans hx)
  · exact originalCompletePrimitive_absorbs_phi0_sublevel I hK hamb hA.le

end FsFltz.Geometry

namespace FsFltz

/-- G1's completeness and finite-type assertion for every nonnegative real
parameter is proved from the finite toric input alone. An original ambient
end bound exists, and the concrete domain at the larger level `Aamb + 1`
gives the finite-type witness with its actual inclusion marking. -/
theorem ToricInput.allNonnegativeComplete {n : ℕ} (I : ToricInput n) :
    AllNonnegativeComplete I := by
  obtain ⟨Aamb, hamb⟩ := I.exists_original_ambientEndBound
  intro K hK
  exact ⟨Geometry.originalFiniteTypePrimitive I hK hamb
    (show Aamb < Aamb + 1 by linarith)⟩

end FsFltz
