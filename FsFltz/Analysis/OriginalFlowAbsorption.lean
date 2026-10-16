import FsFltz.Analysis.OriginalCompleteFlow
import FsFltz.Analysis.OriginalLiouvilleIdentities
import FsFltz.Geometry.FlowAbsorption
import FsFltz.Compactness

/-!
# Finite negative-time absorption for the actual original ambient

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and `lem:absorption`, lines 444–468. The actual quadratic exhaustion on
the period-`2π` quotient has compact sublevels. Its differential along the
actual original field is positive past every valid ambient end bound.
The constructed original complete flow therefore enters every larger
potential sublevel in finite negative time. This is the absorption input
to the ambient inclusion marking; the marking itself remains a separate
construction required by `geoemtric-part-fsf.tex`, `g:initial`, lines 374–384.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators
open Set

namespace FsFltz

/-- Proper exhaustion sublevels of the original quadratic potential,
including the empty sublevels at negative heights. The nonnegative-height
case is the existing quotient compactness theorem. -/
theorem isCompact_phi0_sublevel_all {n : ℕ} (A : ℝ) :
    IsCompact {y : LGSpace n | phi0 y ≤ A} := by
  by_cases hA : 0 ≤ A
  · exact isCompact_phi0_sublevel A hA
  · have hempty : {y : LGSpace n | phi0 y ≤ A} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hnonneg : 0 ≤ phi0 y := div_nonneg (realSquaredNorm_nonneg y.1) (by norm_num)
      exact hA (hnonneg.trans hy)
    rw [hempty]
    exact isCompact_empty

namespace Geometry

/-- The actual original quadratic exhaustion is smooth on the quotient.
Its coordinates are logarithmic coordinates, so no angular lift is chosen. -/
theorem contMDiff_phi0 {n : ℕ} :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => phi0 y) := by
  unfold phi0 realSquaredNorm
  exact (ContMDiff.sum (fun j _ => (contMDiff_lgLogCoordinate j).pow 2)).div_const 2

/-- The valid ambient end bound supplies positivity of the actual intrinsic
exhaustion derivative. This is the previously proved original-field
identity, expressed in the scalar-derivative API of the flow theorem. -/
theorem scalarDerivative_phi0_originalLiouville_pos {n : ℕ} (I : ToricInput n)
    {K Aamb : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (y : (lgManifold n).Point) (hy : Aamb ≤ phi0 y) :
    0 < (lgManifold n).scalarDerivative phi0 y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) :=
  differentialCovector_phi0_originalLiouville_pos I hK hamb y hy

/-- Every complete flow of the actual original field enters each potential
sublevel on or above a valid ambient end bound in finite negative time. No
derivative or properness certificate is added as an input assumption. -/
theorem original_flow_absorbs_phi0_sublevel {n : ℕ} (I : ToricInput n)
    {K Aamb A : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (hA : Aamb ≤ A)
    (F : CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K)))
    (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧ phi0 (F.flow (-T) y) ≤ A := by
  apply F.exists_nonneg_time_scalar_le phi0 contMDiff_phi0
    (isSmoothVectorField_liouvilleVector_lambdaKForm I hK)
    isCompact_phi0_sublevel_all A
  intro x hx
  exact scalarDerivative_phi0_originalLiouville_pos I hK hamb x (hA.trans hx)

/-- The constructed original flow enters every larger potential sublevel
in finite negative time, for every finite nonnegative `K` and every valid
ambient bound. The flow itself is a proved construction from finite input. -/
theorem originalCompletePrimitive_absorbs_phi0_sublevel {n : ℕ} (I : ToricInput n)
    {K Aamb A : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (hA : Aamb ≤ A) (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧
      phi0 ((originalCompletePrimitive I hK).completeFlow.flow (-T) y) ≤ A :=
  original_flow_absorbs_phi0_sublevel I hK hamb hA
    (originalCompletePrimitive I hK).completeFlow y

/-- For a strictly larger level, the same actual negative orbit reaches
the interior of its sublevel: first absorb at the ambient end bound. -/
theorem originalCompletePrimitive_absorbs_phi0_strict_sublevel {n : ℕ}
    (I : ToricInput n) {K Aamb A : ℝ} (hK : 0 ≤ K)
    (hamb : AmbientEndBound I Aamb) (hA : Aamb < A) (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧
      phi0 ((originalCompletePrimitive I hK).completeFlow.flow (-T) y) < A := by
  obtain ⟨T, hT, hentry⟩ :=
    originalCompletePrimitive_absorbs_phi0_sublevel I hK hamb le_rfl y
  exact ⟨T, hT, hentry.trans_lt hA⟩

end Geometry

end FsFltz
