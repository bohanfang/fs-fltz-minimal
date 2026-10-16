import FsFltz.Geometry.Admissibility
import FsFltz.Geometry.QuotientFormBridge
import FsFltz.Geometry.SymplecticBridge

/-!
# Intrinsic and coordinate admissibility

The covectors and intrinsic Liouville vector in `def:rounding`,
`geoemtric-part-fsf.tex`, lines 309–326, agree with their representative
formulas. The actual quotient derivative, exterior calculus and nondegeneracy
prove the full admissibility equivalence required by `sec:lean`, lines 805–814.
-/

noncomputable section

namespace FsFltz.Geometry
open SmoothManifold

/-- The actual intrinsic Liouville vector is the pushforward of the explicit
coordinate solution. Nondegeneracy and the contraction identity are proved,
not supplied as additional hypotheses. Source: `sec:data`, lines 74–86. -/
theorem liouvilleVector_lambdaKForm_lgCover {n : ℕ} (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) (x : TangentCoordinates n) :
    (lgManifold n).liouvilleVector (lambdaKForm I K) (lgCover x) =
      lgCoverTangent x (liouvilleCoordinates I K (lgCover x)) := by
  apply (lgManifold n).liouvilleVector_eq (lambdaKForm I K) (lgCover x)
    (nondegenerate_exteriorDerivative_lambdaKForm I hK (lgCover x))
  intro v
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  rw [exteriorDerivative_lambdaKForm_lgCover, lambdaKForm_lgCover]
  exact omegaKCoordinates_liouville I (lgCover x) hK q

/-- The derivative used in the geometric outwardness test is exactly its
coordinate formula evaluated on the prescribed Liouville solution. -/
theorem differentialCovector_absWSq_liouvilleVector {n : ℕ} (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) (y : (lgManifold n).Point) :
    differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) =
        dAbsWSq I y (liouvilleCoordinates I K y) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [liouvilleVector_lambdaKForm_lgCover I hK, differentialCovector_absWSq_lgCover]

/-- The actual corner covectors test all tangent directions, since the
derivative of the quotient projection is surjective. -/
theorem geometricCornerCovectorsIndependent_lgCover_iff {n : ℕ}
    (I : ToricInput n) (x : TangentCoordinates n) :
    GeometricCornerCovectorsIndependent I (lgCover x) ↔
      CornerCovectorsIndependent I (lgCover x) := by
  constructor
  · intro h s t hst
    apply h s t
    intro v
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    simpa only [differentialCovector_phi0_lgCover,
      differentialCovector_absWSq_lgCover] using hst q
  · intro h s t hst
    apply h s t
    intro q
    simpa only [differentialCovector_phi0_lgCover,
      differentialCovector_absWSq_lgCover] using hst (lgCoverTangent x q)

/-- Corner independence is intrinsic; no angle representative is fixed as
part of admissibility. This equivalence has no symplecticity hypothesis. -/
theorem geometricCornerCovectorsIndependent_iff {n : ℕ}
    (I : ToricInput n) (y : (lgManifold n).Point) :
    GeometricCornerCovectorsIndependent I y ↔ CornerCovectorsIndependent I y := by
  obtain ⟨theta, htheta⟩ := angleQuotient_surjective y.2
  have hy : lgCover (y.1, theta) = y := Prod.ext rfl htheta
  rw [← hy]
  exact geometricCornerCovectorsIndependent_lgCover_iff I (y.1, theta)

/-- The actual geometric and explicit coordinate rounding predicates agree
throughout the nonnegative parameter range. This proves the representation
bridge of `def:rounding`, lines 309–326, without assuming any rounding exists. -/
theorem geometricAdmissibleRounding_iff {n : ℕ} (I : ToricInput n)
    (R : ℝ) {K : ℝ} (hK : 0 ≤ K) (Aminus A : ℝ) (m : RoundingChoice) :
    GeometricAdmissibleRounding I R K Aminus A m ↔
      CoordinateAdmissibleRounding I R K Aminus A m := by
  unfold GeometricAdmissibleRounding CoordinateAdmissibleRounding
  simp only [differentialCovector_absWSq_liouvilleVector I hK,
    geometricCornerCovectorsIndependent_iff]
  rfl

/-- In rank one a valid fiber end bound makes the corner band empty.
The actual geometric admissibility condition therefore imposes exactly the
stated width inequalities, even before the Liouville-field bridge is proved.
Source: `sec:initial`, lines 283–289 and 343; `sec:lean`, lines 825–830. -/
theorem geometricAdmissibleRounding_rank_one_iff (I : ToricInput 1)
    (Aamb R Afib K Aminus A : ℝ) (m : RoundingChoice)
    (hfib : FiberEndBound I Aamb R Afib) (hR : 0 ≤ R) (hlevels : Afib < Aminus) :
    GeometricAdmissibleRounding I R K Aminus A m ↔
      0 < m.eps ∧ m.eps < A - Aminus := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hpos, hwidth⟩
    refine ⟨hpos, hwidth, ?_⟩
    intro y hy
    rw [cornerBand_empty_rank_one I Aamb R Afib Aminus A m.eps
      hfib hR hlevels hwidth] at hy
    exact False.elim hy

end FsFltz.Geometry
