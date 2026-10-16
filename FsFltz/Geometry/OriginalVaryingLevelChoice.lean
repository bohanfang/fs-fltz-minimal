import FsFltz.Geometry.OriginalVaryingLevelGrading
import FsFltz.Analysis.OriginalRounding

/-!
# Comparison of arbitrary supplied original initial choices

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 437–474, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973.
The actual full-ribbon motion in a common rounded ambient is attached to
both supplied endpoints. Its same three-arrow path carries the ambient
markings and prescribed grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- Compose two actual strict marked identifications with one actual
marked and graded deformation, retaining the specified terminal datum. -/
theorem exists_threeStep_markedComparison_to_datum {n : ℕ} {I : ToricInput n}
    {R K A0 E0 A1 E1 : ℝ} {m0 m1 : RoundingChoice}
    (S : InitialPairData I R K A0 E0 m0) (T : InitialPairData I R K A1 E1 m1)
    (Q : PairDeformation n)
    (a : FixedAmbientPairMarking I K Q.source) (b : FixedAmbientPairMarking I K Q.target)
    (q0 : CompletionIdentification S.pair Q.source)
    (q1 : CompletionIdentification Q.target T.pair)
    (hmark0 : q0.ambientEquiv.trans a.equiv = S.ambientMarking.equiv)
    (hmark1 : q1.ambientEquiv.trans T.ambientMarking.equiv = b.equiv)
    (dm : FixedAmbientPairDeformation Q a b)
    (v : Q.source.Maslov) (w : Q.target.Maslov)
    (hv : IsLogarithmicGrading a.equiv v)
    (gm : GradedPairDeformation Q v w)
    (u : T.pair.Maslov) (hu : IsLogarithmicGrading T.ambientMarking.equiv u)
    (g1 : GradedCompletionIdentification q1 w u) :
    ∃ C : InitialChoiceComparison S T, C.chain.length = 3 ∧ C.targetDatum = u := by
  let s := v.pullbackTo q0.ambientEquiv q0.pullback_symplecticForm
  have hs : IsLogarithmicGrading S.ambientMarking.equiv s := by
    rw [← hmark0]
    exact hv.pullbackTo q0.ambientEquiv a.equiv q0.pullback_symplecticForm
  obtain ⟨g0⟩ := (q0.gradedLift_iff_class_eq s v).mpr rfl
  let C : InitialChoiceComparison S T :=
    { sourceMarking := S.fixedAmbientMarking
      targetMarking := T.fixedAmbientMarking
      source_embedding := rfl
      target_embedding := rfl
      source_marking := rfl
      target_marking := rfl
      chain := ((Quiver.Path.nil.cons (ComparisonStep.identification q0)).cons
        (ComparisonStep.deformation Q)).cons (ComparisonStep.identification q1)
      fixedAmbient := .cons (.cons (.cons (.nil S.fixedAmbientMarking)
        (.identification (source := S.fixedAmbientMarking) (target := a)
          (fun x => DFunLike.congr_fun hmark0 x))) (.deformation dm))
        (.identification (source := b) (target := T.fixedAmbientMarking)
          (fun x => DFunLike.congr_fun hmark1 x))
      sourceDatum := s
      targetDatum := u
      source_prescribed := hs
      target_prescribed := hu
      graded := .cons (.cons (.cons (.nil s) (.identification g0))
        (.deformation gm)) (.identification g1) }
  exact ⟨C, rfl, rfl⟩

end FsFltz.Geometry

namespace FsFltz.Geometry.OriginalVaryingLevelBoundaryData
open SmoothManifold

variable {n : ℕ} {I : ToricInput n} {Aamb R Afib K A B Lbound Elevel : ℝ}
  {hamb : AmbientEndBound I Aamb}
  {hR : max 1 (sublevelMagnitudeSup I Aamb) < R}
  {hset : RatioSetWellDefined I R} {hK : K0 I R ≤ K}
  {hfib : FiberEndBound I Aamb R Afib} {hA : Afib < A} (hB : Afib < B)
  {hL : max A B < Lbound} {m : RoundingChoice}
  {hm : GeometricAdmissibleRounding I R K Lbound Elevel m}
  (V : OriginalVaryingLevelBoundaryData I hamb hR hset hK hfib hA hL m hm)

local notation "CE" => originalRoundedCompletion I hamb hR hset hK hfib
  (lt_trans hA (lt_of_le_of_lt (le_max_left A B) hL)) m hm

include hB V in
/-- Attach any two supplied endpoints, retaining any prescribed terminal
representative, on the same three-step marked and graded path. -/
theorem exists_supplied_comparison_to_datum {E0 E1 : ℝ} {m0 m1 : RoundingChoice}
    (S : InitialPairData I R K A E0 m0) (T : InitialPairData I R K B E1 m1)
    (u : T.pair.Maslov) (hu : IsLogarithmicGrading T.ambientMarking.equiv u) :
    ∃ C : InitialChoiceComparison S T, C.chain.length = 3 ∧ C.targetDatum = u := by
  let S0 : InitialPairData I R K A Elevel m :=
    (V.initial hB parameterZero).castRibbonLevel (by simp [parameterZero])
  let S1 : InitialPairData I R K B Elevel m :=
    (V.initial hB parameterOne).castRibbonLevel (by simp [parameterOne])
  obtain ⟨q0, _, hmark0, _, _⟩ := S.exists_fixedRibbon_identification S0
  obtain ⟨q1, _, hmark1, _, _⟩ := S1.exists_fixedRibbon_identification T
  let v : MaslovRepresentative (CE).ambient.manifold
      ((CE).ambient.manifold.exteriorDerivative (CE).ambient.primitive) :=
    u.pullbackTo q1.ambientEquiv q1.pullback_symplecticForm
  have hv : IsLogarithmicGrading S1.ambientMarking.equiv v := by
    rw [← hmark1]
    exact hu.pullbackTo q1.ambientEquiv T.ambientMarking.equiv q1.pullback_symplecticForm
  obtain ⟨g1⟩ := (q1.gradedLift_iff_class_eq v u).mpr rfl
  exact exists_threeStep_markedComparison_to_datum S T V.deformation
    S0.fixedAmbientMarking S1.fixedAmbientMarking q0 q1 hmark0 hmark1
    (V.fixedAmbientDeformation hB) v v hv (V.graded v) u hu g1

end FsFltz.Geometry.OriginalVaryingLevelBoundaryData

namespace FsFltz.Geometry
open SmoothManifold

/-- Arbitrary supplied original initial pairs with levels above any common
valid fiber bound admit the actual three-arrow comparison, retaining any
prescribed terminal representative. The common admissible ambient rounding
and actual varying full-ribbon family are constructed here. -/
theorem exists_originalInitialChoiceComparison_to_datum {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K A B E0 E1 : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hA : Afib < A) (hB : Afib < B)
    {m0 m1 : RoundingChoice}
    (S : InitialPairData I R K A E0 m0) (T : InitialPairData I R K B E1 m1)
    (u : T.pair.Maslov) (hu : IsLogarithmicGrading T.ambientMarking.equiv u) :
    ∃ C : InitialChoiceComparison S T, C.chain.length = 3 ∧ C.targetDatum = u := by
  let Lbound := max A B + 1
  let Elevel := Lbound + 1
  have hL : max A B < Lbound := by dsimp [Lbound]; linarith
  have hLb : Afib < Lbound := hA.trans ((le_max_left A B).trans_lt hL)
  have hLE : Lbound < Elevel := by dsimp [Elevel]; linarith
  obtain ⟨m, hm⟩ := exists_original_admissible_rounding I hamb hR hset hK hfib hLb hLE
  obtain ⟨V⟩ := nonempty_originalVaryingLevelBoundaryData I hamb hR hset hK hfib hA hB hL m hm
  exact OriginalVaryingLevelBoundaryData.exists_supplied_comparison_to_datum hB V S T u hu

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- The exact conditional comparison-of-choices proposition of the
original `lem:choices`. Both valid fiber bounds, both admissible profiles
and both independently supplied initial-pair presentations are arbitrary. -/
theorem initialChoicesStatement : InitialChoicesStatement := by
  intro n I Aamb R0 _hcomplete hRanges R hR K hK Afib0 Afib1 hfib0 hfib1
    A E0 B E1 hA _hAE hB _hBE m0 m1 _hm0 _hm1 S T
  have hset : RatioSetWellDefined I R :=
    ⟨(hRanges.2.2 R hR).1.1, (hRanges.2.2 R hR).1.2.1⟩
  let Afib := min Afib0 Afib1
  have hfib : FiberEndBound I Aamb R Afib := by
    dsimp [Afib]
    rcases le_total Afib0 Afib1 with h | h
    · simpa only [min_eq_left h] using hfib0
    · simpa only [min_eq_right h] using hfib1
  have hAfibA : Afib < A := (min_le_left Afib0 Afib1).trans_lt hA
  have hAfibB : Afib < B := (min_le_right Afib0 Afib1).trans_lt hB
  have hnonneg : 0 ≤ K :=
    (zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK
  obtain ⟨C, _hlength, _hdatum⟩ := exists_originalInitialChoiceComparison_to_datum I
    hRanges.1 (hRanges.2.1.trans_le hR) hset hK hfib hAfibA hAfibB S T
    (T.sourceMaslov hnonneg) (T.sourceMaslov_prescribed hnonneg)
  exact ⟨C⟩

end FsFltz
