import FsFltz.Analysis.OriginalRoundedDomain
import FsFltz.Analysis.OriginalFlowAbsorption
import FsFltz.Geometry.BoundaryOutwardAbsorptionMarking

/-!
# Actual negative-flow absorption into every original rounded domain

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468,
and `prop:allinitial`, lines 915–948; `geoemtric-part-fsf.tex`,
`g:initial`, lines 363–382. The ambient-bound quadratic sublevel lies
strictly inside every admissible rounding: the potential coordinate is
below `-eps`, and the base coordinate is strictly negative. The proved
original flow enters that quadratic sublevel in finite negative time,
so it enters the literal rounded domain.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The actual ambient-bound quadratic sublevel lies strictly inside every
admissible original rounded scalar sublevel. -/
theorem roundedDefiningFunction_neg_on_ambient_sublevel {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (y : LGSpace n) (hy : phi0 y ≤ Aamb) : roundedDefiningFunction I R A m y < 0 := by
  let u := phi0 y - A
  let v := Complex.normSq (W I y) - R ^ 2
  have hu : u < -m.eps := by
    dsimp [u]
    linarith [hfib.1, hadmiss.2.1]
  have hu0 : u ≤ 0 := by linarith [hadmiss.1]
  have hnorm : ‖W I y‖ < R :=
    ((sublevelMaximumAttained I Aamb hamb.1.le).1 y hy).trans_lt
      ((le_max_right _ _).trans_lt hR)
  have hv : v < 0 := by
    dsimp [v]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (W I y)]
  have hface : m.profile.toFun (u, 0) = 0 := by
    rw [m.profile.exact_away (u, 0) (by
      simp only [sub_zero, abs_of_nonpos hu0]
      linarith)]
    exact max_eq_right hu0
  have hle : m.profile.toFun (u, v) ≤ 0 := by
    rw [← hface]
    exact m.profile.monotone_second u hv.le
  have hne : m.profile.toFun (u, v) ≠ 0 := by
    intro hz
    have hvzero := m.profile.second_eq_zero_of_zero_of_first_le_neg_eps
      hadmiss.1 (u, v) hz hu.le hv.le
    exact hv.ne hvzero
  exact lt_of_le_of_ne hle hne

/-- Every complete flow of the original field reaches every admissible
literal rounded domain in finite negative time. The entry is actually
strict in the defining scalar. -/
theorem original_flow_absorbs_roundedDefiningFunction {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (F : CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K)))
    (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧ roundedDefiningFunction I R A m (F.flow (-T) y) < 0 := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  obtain ⟨T, hT, hentry⟩ := original_flow_absorbs_phi0_sublevel I hKnonneg hamb le_rfl F y
  exact ⟨T, hT, roundedDefiningFunction_neg_on_ambient_sublevel I hamb hR
    hfib hlevels m hadmiss (F.flow (-T) y) hentry⟩

/-- Finite negative-time entry into the literal rounded domain, along any
complete flow of the actual original Liouville field. -/
theorem original_flow_absorbs_roundedDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (F : CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K)))
    (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧ F.flow (-T) y ∈ RoundedDomain I R A m := by
  obtain ⟨T, hT, hentry⟩ := original_flow_absorbs_roundedDefiningFunction I
    hamb hR hset hK hfib hlevels m hadmiss F y
  exact ⟨T, hT, hentry.le⟩

/-- The proved original complete flow reaches every admissible rounded
domain. Its existence is the previously constructed finite-input flow. -/
theorem originalCompletePrimitive_absorbs_roundedDomain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hKnonneg : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧
      (originalCompletePrimitive I hKnonneg).completeFlow.flow (-T) y ∈ RoundedDomain I R A m :=
  original_flow_absorbs_roundedDomain I hamb hR hset hK hfib hlevels m hadmiss
    (originalCompletePrimitive I hKnonneg).completeFlow y

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed original ambient is an actual completion of every
admissible rounded domain. Inclusion is the identity on the compact carrier
and the end map is the original Liouville boundary flow.
Source: `lem:absorption`, lines 444–468; `prop:allinitial`, lines 932–940. -/
def originalRoundedCompletion {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m) :
    Completion (originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss) := by
  let P := originalCompletePrimitive I
    ((zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK)
  exact BoundaryOutwardAbsorptionMarking.completionOfBoundaryOutwardAbsorption
    (originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss) P
    (roundedDefiningFunction I R A m) (contMDiff_roundedDefiningFunction I R A m)
    (originalRoundedCompactDomain_frontier I hamb hR hset hK hfib hlevels m hadmiss)
    (differentialCovector_roundedDefiningFunction_originalLiouville_pos I
      hamb hR hset hK hfib hlevels m hadmiss) rfl
    (original_flow_absorbs_roundedDomain I hamb hR hset hK hfib hlevels m hadmiss P.completeFlow)

set_option backward.isDefEq.respectTransparency false in
/-- Any chosen native completion of the actual original rounded domain has
the specified primitive-preserving ambient inclusion marking, induced by
the original Liouville flow. No negative-entry premise is supplied. -/
def originalRoundedInclusionMarking {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (C : Completion (originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss)) :
    InclusionMarking C
      (originalCompletePrimitive I
        ((zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK)).toCompleteLiouvilleManifold
      (fun x => x.val) := by
  let P := originalCompletePrimitive I
    ((zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK)
  exact BoundaryOutwardAbsorptionMarking.inclusionMarkingOfBoundaryOutwardAbsorption
    (originalRoundedLiouvilleDomain I hamb hR hset hK hfib hlevels m hadmiss) P
    (roundedDefiningFunction I R A m) (contMDiff_roundedDefiningFunction I R A m)
    (originalRoundedCompactDomain_frontier I hamb hR hset hK hfib hlevels m hadmiss)
    (differentialCovector_roundedDefiningFunction_originalLiouville_pos I
      hamb hR hset hK hfib hlevels m hadmiss) rfl
    (original_flow_absorbs_roundedDomain I hamb hR hset hK hfib hlevels m hadmiss P.completeFlow) C

end FsFltz.Geometry
