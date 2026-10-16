import FsFltz.Geometry.OriginalParameterPairFamily
import FsFltz.Geometry.OriginalCoefficientMaslovFamily
import FsFltz.Geometry.LocalGermMaslovFamilyPullback
import FsFltz.Geometry.TargetGrading
import FsFltz.Geometry.MaslovClassPullback
import FsFltz.Geometry.PairDeformationMaslovFamily

/-!
# Prescribed grading on the same original coefficient deformation

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–240,
and `def:chain`, lines 163–199; `geometric-part-fsf-proof.tex`,
`lem:markedfamily`, lines 975–1009, and `sec:assembly`, lines 2148–2153.
The fixed logarithmic complex field and squared volume tensor are pulled
back along the actual completed maps of the constructed pair deformation.
Their joint local germs are proved from the original Liouville flows.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set

namespace FsFltz.Geometry
open SmoothManifold

private theorem gradedChain_castCoefficient {n : ℕ} {I : ToricInput n}
    {R K L K' L' Aminus A : ℝ} {m : RoundingChoice}
    (P : InitialPairData I R K Aminus A m) (T : InitialPairData I R L Aminus A m)
    (hK : K = K') (hL : L = L')
    (s : P.pair.Maslov) (u : T.pair.Maslov)
    (hs : IsLogarithmicGrading P.ambientMarking.equiv s)
    (hu : IsLogarithmicGrading T.ambientMarking.equiv u)
    (C : ComparisonChain P.pair T.pair) (hC : C.length = 1)
    (hg : Nonempty (GradedComparisonChain P.pair C s u)) :
    ∃ s' : (P.castCoefficient hK).pair.Maslov,
    ∃ u' : (T.castCoefficient hL).pair.Maslov,
    ∃ C' : ComparisonChain (P.castCoefficient hK).pair (T.castCoefficient hL).pair,
      C'.length = 1 ∧ IsLogarithmicGrading (P.castCoefficient hK).ambientMarking.equiv s' ∧
      IsLogarithmicGrading (T.castCoefficient hL).ambientMarking.equiv u' ∧
      Nonempty (GradedComparisonChain (P.castCoefficient hK).pair C' s' u') := by
  cases hK
  cases hL
  exact ⟨s, u, C, hC, hs, hu, hg⟩

/-- Every admissible original profile admits an increasing-coefficient
comparison chain of one step, graded by the prescribed logarithmic datum
on these same actual initial-pair endpoints and completion maps. -/
theorem exists_originalParameter_gradedComparisonChain {n : ℕ} (I : ToricInput n)
    {Aamb R Afib K L Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K) (hKL : K ≤ L)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hm : GeometricAdmissibleRounding I R K Aminus A m) :
    ∃ P : InitialPairData I R K Aminus A m,
    ∃ T : InitialPairData I R L Aminus A m,
    ∃ s : P.pair.Maslov, ∃ u : T.pair.Maslov,
    ∃ C : ComparisonChain P.pair T.pair, C.length = 1 ∧
      IsLogarithmicGrading P.ambientMarking.equiv s ∧
      IsLogarithmicGrading T.ambientMarking.equiv u ∧
      Nonempty (GradedComparisonChain P.pair C s u) := by
  obtain ⟨j, hj, hp, h, hB, hs, p, hcompleted, hfield, he⟩ :=
    exists_originalParameter_presentations_with_mapGerms I hamb hR hset hK hKL hfib hlevels m hm
  let S := originalParameterInitialPairData I hamb hR hset hK hKL hfib hlevels m hm j hj hp
  let Q := originalParameterPairDeformation I hamb hR hset hK hKL hfib hlevels m hm
    j hj hp h hB hs p hcompleted hfield
  have hnonneg : 0 ≤ K :=
    (zero_le_one.trans (one_le_K0 I R hset.1 hset.2)).trans hK
  have hcoefficient (t : Parameter) : 0 ≤ (1 - t.val) * K + t.val * L :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) hnonneg)
      (mul_nonneg t.property.1 (hnonneg.trans hKL))
  let s := (S parameterZero).sourceMaslov (hcoefficient parameterZero)
  let u := (S parameterOne).sourceMaslov (hcoefficient parameterOne)
  let f := logarithmicAffineMaslovFamily I K L hnonneg (hnonneg.trans hKL)
  let e : Parameter → Q.source.ambientManifold.SmoothEquiv (lgManifold n) :=
    fun t => (p t).equiv.trans (S t).ambientMarking.equiv
  have hprimitive (t : Parameter) :
      Q.source.ambientManifold.pullback (lgManifold n) (e t)
        (lambdaKForm I ((1 - t.val) * K + t.val * L)) = Q.completedPrimitive t := by
    change Q.source.ambientManifold.pullback (lgManifold n)
      ((S t).ambientMarking.equiv ∘ (p t).equiv) _ =
      Q.source.ambientManifold.pullback (S t).pair.ambientManifold (p t).equiv
        (S t).pair.ambientCompletion.ambient.primitive
    rw [Q.source.ambientManifold.pullback_comp (S t).pair.ambientManifold (lgManifold n)
      ((p t).equiv.mdifferentiable (by simp))
      ((S t).ambientMarking.equiv.mdifferentiable (by simp))]
    exact congrArg (Q.source.ambientManifold.pullback (S t).pair.ambientManifold (p t).equiv)
      (S t).ambientMarking.primitive
  have hform (t : Parameter) :
      Q.source.ambientManifold.pullback (lgManifold n) (e t)
        ((lgManifold n).exteriorDerivative
          (lambdaKForm I ((1 - t.val) * K + t.val * L))) =
      Q.completedSymplecticExtension t.val := by
    exact (Q.source.ambientManifold.exteriorDerivative_pullback (lgManifold n)
      (e t).toContMDiffMap _ (isSmoothForm_lambdaKForm I _)).symm.trans
        ((congrArg Q.source.ambientManifold.exteriorDerivative (hprimitive t)).trans
          (Q.completedSymplecticExtension_apply t).symm)
  have hJ₀ : pullbackAlmostComplex Q.source.ambientManifold (lgManifold n)
      (e parameterZero) (f.J 0) =
      pullbackAlmostComplex Q.source.ambientManifold Q.source.ambientManifold
        (Q.ambientCompletionPresentation parameterZero).equiv s.J :=
    pullbackAlmostComplex_trans Q.source.ambientManifold (S parameterZero).pair.ambientManifold
      (lgManifold n) (p parameterZero).equiv (S parameterZero).ambientMarking.equiv _
  have hJ₁ : pullbackAlmostComplex Q.source.ambientManifold (lgManifold n)
      (e parameterOne) (f.J 1) =
      pullbackAlmostComplex Q.source.ambientManifold Q.target.ambientManifold
        (Q.ambientCompletionPresentation parameterOne).equiv u.J :=
    pullbackAlmostComplex_trans Q.source.ambientManifold (S parameterOne).pair.ambientManifold
      (lgManifold n) (p parameterOne).equiv (S parameterOne).ambientMarking.equiv _
  have ht₀ : pullbackSquaredTensor Q.source.ambientManifold (lgManifold n)
      (e parameterZero) (f.tensor 0) =
      pullbackSquaredTensor Q.source.ambientManifold Q.source.ambientManifold
        (Q.ambientCompletionPresentation parameterZero).equiv s.tensor :=
    pullbackSquaredTensor_trans Q.source.ambientManifold (S parameterZero).pair.ambientManifold
      (lgManifold n) (p parameterZero).equiv (S parameterZero).ambientMarking.equiv _
  have ht₁ : pullbackSquaredTensor Q.source.ambientManifold (lgManifold n)
      (e parameterOne) (f.tensor 1) =
      pullbackSquaredTensor Q.source.ambientManifold Q.target.ambientManifold
        (Q.ambientCompletionPresentation parameterOne).equiv u.tensor :=
    pullbackSquaredTensor_trans Q.source.ambientManifold (S parameterOne).pair.ambientManifold
      (lgManifold n) (p parameterOne).equiv (S parameterOne).ambientMarking.equiv _
  obtain ⟨g, _, _⟩ := GradedPairDeformation.exists_of_localGermPullback
    (D := Q) (source := s) (target := u) (lgManifold n) f e he
    Q.completedSymplecticExtension Q.completedSymplecticExtension_apply
    hform hJ₀ hJ₁ ht₀ ht₁
  let C : ComparisonChain (S parameterZero).pair (S parameterOne).pair :=
    Quiver.Path.nil.cons (.deformation Q)
  have hg : Nonempty (GradedComparisonChain (S parameterZero).pair C s u) :=
    ⟨.cons (.nil s) (.deformation g)⟩
  have hzero : (1 - parameterZero.val) * K + parameterZero.val * L = K := by
    simp [parameterZero]
  have hone : (1 - parameterOne.val) * K + parameterOne.val * L = L := by
    simp [parameterOne]
  exact ⟨(S parameterZero).castCoefficient hzero, (S parameterOne).castCoefficient hone,
    gradedChain_castCoefficient (S parameterZero) (S parameterOne) hzero hone s u
      ((S parameterZero).sourceMaslov_prescribed (hcoefficient parameterZero))
      ((S parameterOne).sourceMaslov_prescribed (hcoefficient parameterOne)) C rfl hg⟩

end FsFltz.Geometry
