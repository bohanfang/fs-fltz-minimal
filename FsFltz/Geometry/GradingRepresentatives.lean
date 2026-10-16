import FsFltz.Geometry.StandardComplexCompatibility

/-!
# Actual representatives for the prescribed endpoint gradings

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 220–243, and
`sec:lean`, lines 794–814. A smooth actual coframe and smooth inversion of
invertible continuous linear maps give smoothness of the transported fields.
The pointwise symplectic calculations then assemble compatible structures
and actual prescribed smooth nowhere-zero squared-canonical representatives.
No completion markings, comparison chains, or grading transport are assumed.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false in
/-- Conjugating a fixed linear complex structure through an actual smooth
coframe produces a smooth intrinsic field. The inverse coframe is controlled
in every chart by smooth inversion on the open set of invertible maps. -/
theorem isSmoothAlmostComplexField_of_coframe {n : ℕ} (M : SmoothManifold (2 * n))
    (C : (x : M.Point) → M.Tangent x ≃L[ℝ] TangentCoordinates n)
    (hC : ∀ a, ContDiffOn ℝ ∞ (fun y : Model (2 * n) =>
      ((C ((chartAt (Model (2 * n)) a).symm y)).toContinuousLinearMap.comp
        (M.inverseChartTangentMap a y) : Model (2 * n) →L[ℝ] TangentCoordinates n))
      (chartAt (Model (2 * n)) a).target) :
    IsSmoothAlmostComplexField M (fun x => (C x).symm.toContinuousLinearMap.comp
      ((coordinateComplexStructure n).comp (C x).toContinuousLinearMap)) := by
  intro a
  let c := chartAt (Model (2 * n)) a
  let A (y : Model (2 * n)) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
    (C (c.symm y)).toContinuousLinearMap.comp (M.inverseChartTangentMap a y)
  let B (y : Model (2 * n)) : TangentCoordinates n →L[ℝ] Model (2 * n) :=
    (M.chartTangentMap a (c.symm y)).comp (C (c.symm y)).symm.toContinuousLinearMap
  have hAB (y : Model (2 * n)) (hy : y ∈ c.target) :
      (A y).comp (B y) = ContinuousLinearMap.id ℝ (TangentCoordinates n) := by
    apply ContinuousLinearMap.ext
    intro v
    have hinv := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv
      (c.map_target hy)
    rw [c.right_inv hy] at hinv
    have h : (M.inverseChartTangentMap a y)
        ((M.chartTangentMap a (c.symm y)) ((C (c.symm y)).symm v)) =
          (C (c.symm y)).symm v :=
      congrArg (fun L => L ((C (c.symm y)).symm v)) hinv
    change C (c.symm y) ((M.inverseChartTangentMap a y)
      ((M.chartTangentMap a (c.symm y)) ((C (c.symm y)).symm v))) = v
    rw [h]
    exact (C (c.symm y)).apply_symm_apply v
  have hBA (y : Model (2 * n)) (hy : y ∈ c.target) :
      (B y).comp (A y) = ContinuousLinearMap.id ℝ (Model (2 * n)) := by
    apply ContinuousLinearMap.ext
    intro v
    change (M.chartTangentMap a (c.symm y)) ((C (c.symm y)).symm
      (C (c.symm y) ((M.inverseChartTangentMap a y) v))) = v
    rw [(C (c.symm y)).symm_apply_apply]
    exact congrArg (fun L => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).comp_symm_deriv hy)
  have hAi (y : Model (2 * n)) (hy : y ∈ c.target) : (A y).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (hAB y hy) (hBA y hy)
  have hInv : ContDiffOn ℝ ∞ (fun y => (A y).inverse) c.target := by
    intro y hy
    exact (hAi y hy).contDiffAt_map_inverse.comp_contDiffWithinAt y (hC a y hy)
  have hSmooth := hInv.clm_comp
    ((contDiffOn_const (c := coordinateComplexStructure n)).clm_comp (hC a))
  apply hSmooth.congr
  intro y hy
  rw [ContinuousLinearMap.inverse_eq (hAB y hy) (hBA y hy)]
  ext v
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed logarithmic complex structure is smooth on the actual quotient atlas. -/
theorem isSmoothAlmostComplexField_logarithmicAlmostComplexField (n : ℕ) :
    IsSmoothAlmostComplexField (lgManifold n) (logarithmicAlmostComplexField n) :=
  isSmoothAlmostComplexField_of_coframe (lgManifold n) lgTangentCoframeEquiv
    (contDiffOn_lgTangentCoframe_inChart (n := n))

set_option backward.isDefEq.respectTransparency false in
/-- The standard vertical-first cotangent complex structure is smooth globally. -/
theorem isSmoothAlmostComplexField_cotangentAlmostComplexField (n : ℕ) :
    IsSmoothAlmostComplexField (cotangentManifold n) (cotangentAlmostComplexField n) :=
  isSmoothAlmostComplexField_of_coframe (cotangentManifold n) cotangentTangentCoframeEquiv
    (contDiffOn_cotangentTangentCoframe_inChart (n := n))

/-- The based logarithmic structure is compatible with the actual prescribed
exterior derivative for every `K ≥ 0`, as specified in source lines 236–238. -/
theorem isCompatibleAlmostComplex_logarithmicAlmostComplexField {n : ℕ}
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) :
    IsCompatibleAlmostComplex (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaKForm I K))
      (logarithmicAlmostComplexField n) :=
  ⟨isSmoothAlmostComplexField_logarithmicAlmostComplexField n,
    logarithmicAlmostComplexField_sq,
    logarithmicAlmostComplexField_symplectic I K,
    logarithmicAlmostComplexField_positive I hK⟩

/-- The vertical-first structure is compatible with the actual cotangent
exterior derivative, with the sign convention of source lines 239–243. -/
theorem isCompatibleAlmostComplex_cotangentAlmostComplexField (n : ℕ) :
    IsCompatibleAlmostComplex (cotangentManifold n)
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n))
      (cotangentAlmostComplexField n) :=
  ⟨isSmoothAlmostComplexField_cotangentAlmostComplexField n,
    cotangentAlmostComplexField_sq,
    cotangentAlmostComplexField_symplectic,
    cotangentAlmostComplexField_positive⟩

/-- The initial squared logarithmic volume form is an actual ambient Maslov
representative on the entire quotient `Y`, for every nonnegative `K`. -/
def logarithmicMaslovRepresentative {n : ℕ} (I : ToricInput n)
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaKForm I K)) where
  J := logarithmicAlmostComplexField n
  compatible := isCompatibleAlmostComplex_logarithmicAlmostComplexField I hK
  tensor := logarithmicSquaredVolumeTensor n
  canonical := logarithmicSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n
  nowhereZero := logarithmicSquaredVolumeTensor_ne_zero

/-- The standard cotangent vertical-phase-zero form is an actual ambient
Maslov representative, without a global real-valued angle choice. -/
def cotangentMaslovRepresentative (n : ℕ) :
    MaslovRepresentative (cotangentManifold n)
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) where
  J := cotangentAlmostComplexField n
  compatible := isCompatibleAlmostComplex_cotangentAlmostComplexField n
  tensor := cotangentSquaredVolumeTensor n
  canonical := cotangentSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_cotangentSquaredVolumeTensor n
  nowhereZero := cotangentSquaredVolumeTensor_ne_zero

/-- The constructed representative has precisely the source's prescribed
logarithmic tensor values on every pair of tangent frames. -/
theorem isLogarithmicGrading_logarithmicMaslovRepresentative {n : ℕ} (I : ToricInput n)
    (K : ℝ) (hK : 0 ≤ K) :
    IsLogarithmicGrading id (logarithmicMaslovRepresentative I K hK) :=
  (isLogarithmicGrading_id_iff_tensor_eq _).mpr rfl

theorem isVerticalGrading_cotangentMaslovRepresentative (n : ℕ) :
    IsVerticalGrading id (cotangentMaslovRepresentative n) :=
  (isVerticalGrading_id_iff_tensor_eq _).mpr rfl

/-- Existence of the specified datum is a proved foundation, without
assuming any comparison chain, completion marking, or geometric end estimate. -/
theorem exists_logarithmicMaslovRepresentative {n : ℕ} (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ s : MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative (lambdaKForm I K)), IsLogarithmicGrading id s :=
  ⟨logarithmicMaslovRepresentative I K hK,
    isLogarithmicGrading_logarithmicMaslovRepresentative I K hK⟩

theorem exists_cotangentMaslovRepresentative (n : ℕ) :
    ∃ s : MaslovRepresentative (cotangentManifold n)
      ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)), IsVerticalGrading id s :=
  ⟨cotangentMaslovRepresentative n, isVerticalGrading_cotangentMaslovRepresentative n⟩

end FsFltz.Geometry
