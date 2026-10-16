import FsFltz.Geometry.CanonicalCoframe
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth local coordinates for canonical tensors

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. Every almost complex structure has a complex
coframe at each point, proved in `CanonicalCoframe`. Projection extends it
to an actual smooth complex coframe near that point. The local
determinant generator, section reconstruction, and smooth transition
coefficients use the concrete canonical fibers from `CanonicalLine`.

The global intrinsic bundle atlas and invariance under changing compatible
complex structures remain separate foundations.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- Complex-linear projection of a fixed real coframe against a varying `J`.
Only the coframe at the distinguished point is supplied. -/
def projectedComplexCoframe {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (2 : ℝ)⁻¹ • (C.toContinuousLinearMap -
    (coordinateComplexStructure n).comp (C.toContinuousLinearMap.comp J))

theorem projectedComplexCoframe_intertwines {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, J (J v) = -v) (v : Model (2 * n)) :
    projectedComplexCoframe C J (J v) =
      coordinateComplexStructure n (projectedComplexCoframe C J v) := by
  simp only [projectedComplexCoframe, smul_apply,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, hJ, map_neg, map_smul, map_sub,
    coordinateComplexStructure_sq]
  module

theorem projectedComplexCoframe_eq {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hC : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    projectedComplexCoframe C J = C.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [projectedComplexCoframe, smul_apply,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, hC, coordinateComplexStructure_sq]
  module

theorem contDiffOn_projectedComplexCoframe {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U) :
    ContDiffOn ℝ ∞ (fun x => projectedComplexCoframe C (J x)) U := by
  apply ContDiffOn.const_smul
  exact (contDiffOn_const (c := C.toContinuousLinearMap)).sub
    ((contDiffOn_const (c := coordinateComplexStructure n)).clm_comp
      ((contDiffOn_const (c := C.toContinuousLinearMap)).clm_comp hJ))

/-- Smooth projection produces invertible coframes on a neighborhood, rather
than requiring an already smooth local coframe as a hypothesis. -/
theorem projectedComplexCoframe_eventually_invertible {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {x₀ : E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U)
    (hC : ∀ v, C (J x₀ v) = coordinateComplexStructure n (C v)) :
    ∀ᶠ x in 𝓝 x₀, (projectedComplexCoframe C (J x)).IsInvertible := by
  have hcont := (contDiffOn_projectedComplexCoframe C hJ).continuousOn x₀ hx₀
  have hcont' := (hcont.continuousAt (hU.mem_nhds hx₀)).tendsto
  rw [projectedComplexCoframe_eq C (J x₀) hC] at hcont'
  exact hcont' C.nhds

/-- A smooth almost complex field admits smooth local complex coframes
around every point. The seed coframe is a conclusion of finite-dimensional
algebra, and invertibility on the neighborhood is a conclusion of openness. -/
theorem exists_smooth_local_complexCoframe {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {x₀ : E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U) (hJsq : ∀ x ∈ U, ∀ v, J x (J x v) = -v) :
    ∃ C₀ : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧
        ContDiffOn ℝ ∞ (fun x => projectedComplexCoframe C₀ (J x)) V ∧
        (∀ x ∈ V, (projectedComplexCoframe C₀ (J x)).IsInvertible) ∧
        (∀ x ∈ V, ∀ v, projectedComplexCoframe C₀ (J x) (J x v) =
          coordinateComplexStructure n (projectedComplexCoframe C₀ (J x) v)) := by
  obtain ⟨C₀, hC₀⟩ := exists_complexCoframe (J x₀) (hJsq x₀ hx₀)
  have hi := projectedComplexCoframe_eventually_invertible hU hx₀ C₀ hJ hC₀
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hi
  refine ⟨C₀, V ∩ U, inter_subset_right, hVo.inter hU, ⟨hxV, hx₀⟩, ?_, ?_, ?_⟩
  · exact (contDiffOn_projectedComplexCoframe C₀ hJ).mono inter_subset_right
  · intro x hx
    exact hV hx.1
  · intro x hx
    exact projectedComplexCoframe_intertwines C₀ (J x) (hJsq x hx.2)

/-- The inverse coframe is smooth wherever the constructed map is invertible. -/
theorem contDiffOn_coframe_inverse {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C U) (hinv : ∀ x ∈ U, (C x).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => (C x).inverse) U := by
  intro x hx
  exact (hinv x hx).contDiffAt_map_inverse.comp_contDiffWithinAt x (hC x hx)

/-- The determinant square of a real coframe, with no invertibility assumption. -/
def coframeSquaredGenerator {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) : SquaredCanonicalTensor n :=
  (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C)

theorem contDiffOn_coframeSquaredGenerator {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun x => coframeSquaredGenerator (C x)) U :=
  ((coordinateSquaredVolumeTensor n).compContinuousLinearMapLRight
    (E := fun _ => Model (2 * n))).contDiff.comp_contDiffOn
      (contDiffOn_pi.mpr (fun _ => hC))

theorem coframeSquaredGenerator_canonical {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hC : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    IsSquaredCanonicalTensor J (coframeSquaredGenerator C) :=
  isSquaredCanonicalTensor_coordinateSquaredVolumeTensor C J hC

theorem coframeSquaredGenerator_frame {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible) :
    coframeSquaredGenerator C (fun i => C.inverse (verticalFrame n (i.elim id id))) = 1 := by
  simp only [coframeSquaredGenerator, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    hC.self_apply_inverse]
  exact coordinateSquaredVolumeValue_verticalFrame n

theorem coframeSquaredGenerator_ne_zero {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible) :
    coframeSquaredGenerator C ≠ 0 := by
  intro hz
  have hf := coframeSquaredGenerator_frame C hC
  rw [hz, zero_apply] at hf
  exact zero_ne_one hf

/-- Scalar coordinate of a squared tensor in the inverse coframe. -/
def squaredCoframeCoefficient {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (s : SquaredCanonicalTensor n) : ℂ :=
  s (fun i => C.inverse (verticalFrame n (i.elim id id)))

theorem squaredCoframe_reconstruction {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hC : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : SquaredCanonicalTensor n) (hs : IsSquaredCanonicalTensor J s) :
    s = squaredCoframeCoefficient C s • coframeSquaredGenerator C := by
  obtain ⟨e, he⟩ := hinv
  subst C
  ext v
  simpa [squaredCoframeCoefficient, coframeSquaredGenerator, smul_eq_mul] using
    squaredCanonicalTensor_reconstruction e J hC ⟨s, hs⟩ v

theorem contDiffOn_squaredCoframeCoefficient {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    {s : E → SquaredCanonicalTensor n}
    (hC : ContDiffOn ℝ ∞ C U) (hinv : ∀ x ∈ U, (C x).IsInvertible)
    (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (fun x => squaredCoframeCoefficient (C x) (s x)) U := by
  have hframe : ContDiffOn ℝ ∞
      (fun x (i : Fin n ⊕ Fin n) => (C x).inverse (verticalFrame n (i.elim id id))) U :=
    contDiffOn_pi.mpr (fun i =>
      (contDiffOn_coframe_inverse hC hinv).clm_apply contDiffOn_const)
  let ev := (ContinuousLinearMap.id ℝ (SquaredCanonicalTensor n)).flipMultilinear
  exact (ev.contDiff.comp_contDiffOn hframe).clm_apply hs

/-- The concrete smoothness condition is precisely smoothness of the scalar
section coordinate. This is the local section consumer of reconstruction. -/
theorem contDiffOn_squaredTensor_iff_coefficient {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    {s : E → SquaredCanonicalTensor n}
    (hC : ContDiffOn ℝ ∞ C U) (hinv : ∀ x ∈ U, (C x).IsInvertible)
    (hCJ : ∀ x ∈ U, ∀ v, C x (J x v) = coordinateComplexStructure n (C x v))
    (hs : ∀ x ∈ U, IsSquaredCanonicalTensor (J x) (s x)) :
    ContDiffOn ℝ ∞ s U ↔
      ContDiffOn ℝ ∞ (fun x => squaredCoframeCoefficient (C x) (s x)) U := by
  constructor
  · exact contDiffOn_squaredCoframeCoefficient hC hinv
  · intro hcoeff
    apply (hcoeff.smul (contDiffOn_coframeSquaredGenerator hC)).congr
    intro x hx
    exact squaredCoframe_reconstruction (C x) (hinv x hx) (J x) (hCJ x hx)
      (s x) (hs x hx)

/-- Transition coefficient from the determinant generator of `C` to that of `D`. -/
def canonicalCoframeTransition {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n) : ℂ :=
  coordinateVolumeValue (fun i => C (D.inverse (verticalFrame n i)))

/-- The squared transition is derived by evaluating the actual tensor generator. -/
def squaredCoframeTransition {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n) : ℂ :=
  squaredCoframeCoefficient D (coframeSquaredGenerator C)

theorem squaredCoframeTransition_eq_square {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n) :
    squaredCoframeTransition C D = canonicalCoframeTransition C D ^ 2 := by
  simp [squaredCoframeTransition, squaredCoframeCoefficient, coframeSquaredGenerator,
    coordinateSquaredVolumeTensor_apply, coordinateSquaredVolumeValue,
    canonicalCoframeTransition, pow_two]

theorem contDiffOn_canonicalCoframeTransition {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C D : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C U) (hD : ContDiffOn ℝ ∞ D U)
    (hDinv : ∀ x ∈ U, (D x).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => canonicalCoframeTransition (C x) (D x)) U := by
  have hframe : ContDiffOn ℝ ∞
      (fun x (i : Fin n) => C x ((D x).inverse (verticalFrame n i))) U :=
    contDiffOn_pi.mpr (fun i => hC.clm_apply
      ((contDiffOn_coframe_inverse hD hDinv).clm_apply contDiffOn_const))
  exact (coordinateVolumeTensor n).toContinuousMultilinearMap.contDiff.comp_contDiffOn hframe

theorem contDiffOn_squaredCoframeTransition {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {C D : E → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C U) (hD : ContDiffOn ℝ ∞ D U)
    (hDinv : ∀ x ∈ U, (D x).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => squaredCoframeTransition (C x) (D x)) U :=
  contDiffOn_squaredCoframeCoefficient hD hDinv (contDiffOn_coframeSquaredGenerator hC)

theorem squaredCoframeTransition_self {n : ℕ}
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible) :
    squaredCoframeTransition C C = 1 :=
  coframeSquaredGenerator_frame C hinv

/-- Actual generators agree on overlaps by the derived transition scalar. -/
theorem coframeSquaredGenerator_transition {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n) (hDinv : D.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (hDJ : ∀ v, D (J v) = coordinateComplexStructure n (D v)) :
    coframeSquaredGenerator C = squaredCoframeTransition C D • coframeSquaredGenerator D :=
  squaredCoframe_reconstruction D hDinv J hDJ _
    (coframeSquaredGenerator_canonical C J hCJ)

theorem squaredCoframeTransition_ne_zero {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (hCinv : C.IsInvertible) (hDinv : D.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (hDJ : ∀ v, D (J v) = coordinateComplexStructure n (D v)) :
    squaredCoframeTransition C D ≠ 0 := by
  intro hz
  have h := coframeSquaredGenerator_transition C D hDinv J hCJ hDJ
  apply coframeSquaredGenerator_ne_zero C hCinv
  ext v
  have he := congrArg (fun t : SquaredCanonicalTensor n => t v) h
  simpa [hz, smul_eq_mul] using he

/-- The actual scalar coordinates of any canonical section transform by
the same transition coefficient as the generators. -/
theorem squaredCoframeCoefficient_change {n : ℕ}
    (C D : Model (2 * n) →L[ℝ] TangentCoordinates n) (hCinv : C.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : SquaredCanonicalTensor n) (hs : IsSquaredCanonicalTensor J s) :
    squaredCoframeCoefficient D s =
      squaredCoframeCoefficient C s * squaredCoframeTransition C D := by
  have h := squaredCoframe_reconstruction C hCinv J hCJ s hs
  have he := congrArg (fun t => squaredCoframeCoefficient D t) h
  simpa only [squaredCoframeCoefficient, smul_apply, smul_eq_mul,
    squaredCoframeTransition] using he

/-- The overlap maps satisfy the cocycle identity because they are the
coordinates of the same actual tensor, rather than an assumed cocycle. -/
theorem squaredCoframeTransition_cocycle {n : ℕ}
    (C D A : Model (2 * n) →L[ℝ] TangentCoordinates n) (hDinv : D.IsInvertible)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (hDJ : ∀ v, D (J v) = coordinateComplexStructure n (D v)) :
    squaredCoframeTransition C A =
      squaredCoframeTransition C D * squaredCoframeTransition D A :=
  squaredCoframeCoefficient_change D A hDinv J hDJ _
    (coframeSquaredGenerator_canonical C J hCJ)

/-- Every smooth almost complex field has a smooth nonzero local squared
canonical section; neither a pointwise coframe nor a local section is assumed. -/
theorem exists_smooth_local_squaredCanonical_section {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {x₀ : E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    {J : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hJ : ContDiffOn ℝ ∞ J U) (hJsq : ∀ x ∈ U, ∀ v, J x (J x v) = -v) :
    ∃ C₀ : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∃ V ⊆ U, IsOpen V ∧ x₀ ∈ V ∧
      ContDiffOn ℝ ∞ (fun x => coframeSquaredGenerator (projectedComplexCoframe C₀ (J x))) V ∧
      (∀ x ∈ V, IsSquaredCanonicalTensor (J x)
        (coframeSquaredGenerator (projectedComplexCoframe C₀ (J x)))) ∧
      (∀ x ∈ V, coframeSquaredGenerator (projectedComplexCoframe C₀ (J x)) ≠ 0) := by
  obtain ⟨C₀, V, hVU, hVo, hxV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_complexCoframe hU hx₀ hJ hJsq
  refine ⟨C₀, V, hVU, hVo, hxV, contDiffOn_coframeSquaredGenerator hC, ?_, ?_⟩
  · intro x hx
    exact coframeSquaredGenerator_canonical _ _ (hCJ x hx)
  · intro x hx
    exact coframeSquaredGenerator_ne_zero _ (hinv x hx)

theorem isSquaredCanonicalTensor_comp_of_intertwines {n : ℕ}
    (A : Model (2 * n) →L[ℝ] Model (2 * n))
    (J J' : Model (2 * n) →L[ℝ] Model (2 * n))
    (hA : ∀ v, A (J' v) = J (A v))
    (s : SquaredCanonicalTensor n) (hs : IsSquaredCanonicalTensor J s) :
    IsSquaredCanonicalTensor J' (s.compContinuousLinearMap (fun _ => A)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v i j hij hv
    exact hs.1 _ i j hij (congrArg A hv)
  · intro v i j hij hv
    exact hs.2.1 _ i j hij (congrArg A hv)
  · intro v i
    have hu : (fun k => A (Function.update v i (J' (v i)) k)) =
        Function.update (fun k => A (v k)) i (J (A (v i))) := by
      funext k
      by_cases hk : k = i
      · subst k; simp only [Function.update_self]; exact hA _
      · simp only [Function.update_of_ne hk]
    change s (fun k => A (Function.update v i (J' (v i)) k)) = _
    rw [hu]
    exact hs.2.2 _ i

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse chart differential intertwines the chart expression
of `J` with the intrinsic field. -/
theorem inverseChartTangentMap_almostComplexInChart {n : ℕ}
    (M : SmoothManifold (2 * n)) (a : M.Point) (J : AlmostComplexField M)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (v : Model (2 * n)) :
    M.inverseChartTangentMap a y (almostComplexInChart M a J y v) =
      J ((chartAt (Model (2 * n)) a).symm y) (M.inverseChartTangentMap a y v) := by
  let c := chartAt (Model (2 * n)) a
  have hi := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv
    (c.map_target hy)
  rw [c.right_inv hy] at hi
  exact congrArg (fun A => A (J (c.symm y) (M.inverseChartTangentMap a y v))) hi

set_option backward.isDefEq.respectTransparency false in
/-- The defining canonical equations survive the actual atlas change. -/
theorem squaredTensorInChart_canonical {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (J : AlmostComplexField M)
    (s : M.Point → SquaredCanonicalTensor n)
    (hs : ∀ x, IsSquaredCanonicalTensor (J x) (s x))
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    IsSquaredCanonicalTensor (almostComplexInChart M a J y) (squaredTensorInChart M a s y) :=
  isSquaredCanonicalTensor_comp_of_intertwines (M.inverseChartTangentMap a y)
    (J ((chartAt (Model (2 * n)) a).symm y)) (almostComplexInChart M a J y)
    (inverseChartTangentMap_almostComplexInChart M a J y hy) _
    (hs ((chartAt (Model (2 * n)) a).symm y))

set_option backward.isDefEq.respectTransparency false in
theorem squaredTensorInChart_ne_zero {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (s : M.Point → SquaredCanonicalTensor n) (hs : ∀ x, s x ≠ 0)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    squaredTensorInChart M a s y ≠ 0 := by
  let c := chartAt (Model (2 * n)) a
  have hi := (mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).symm_comp_deriv
    (c.map_target hy)
  rw [c.right_inv hy] at hi
  intro hz
  apply hs (c.symm y)
  ext v
  have he := congrArg (fun t : SquaredCanonicalTensor n =>
    t (fun i => M.chartTangentMap a (c.symm y) (v i))) hz
  change s (c.symm y) (fun i => M.inverseChartTangentMap a y
    (M.chartTangentMap a (c.symm y) (v i))) = 0 at he
  have hv : (fun i => M.inverseChartTangentMap a y
      (M.chartTangentMap a (c.symm y) (v i))) = v :=
    funext (fun i => congrArg (fun A => A (v i)) hi)
  rwa [hv] at he

set_option backward.isDefEq.respectTransparency false in
theorem almostComplexInChart_sq {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (J : AlmostComplexField M) (hJ : ∀ x v, J x (J x v) = -v)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (v : Model (2 * n)) :
    almostComplexInChart M a J y (almostComplexInChart M a J y v) = -v := by
  let c := chartAt (Model (2 * n)) a
  change M.chartTangentMap a (c.symm y)
    (J (c.symm y) (M.inverseChartTangentMap a y (almostComplexInChart M a J y v))) = -v
  rw [inverseChartTangentMap_almostComplexInChart M a J y hy, hJ, map_neg]
  exact congrArg Neg.neg (congrArg (fun A => A v)
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2 * n))) a).comp_symm_deriv hy))

namespace MaslovRepresentative

/-- An existing actual Maslov section has smooth scalar coordinates in any
smooth complex coframe in an atlas chart. -/
theorem contDiffOn_coframeCoefficient {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (a : M.Point)
    {C : Model (2 * n) → Model (2 * n) →L[ℝ] TangentCoordinates n}
    (hC : ContDiffOn ℝ ∞ C (chartAt (Model (2 * n)) a).target)
    (hinv : ∀ y ∈ (chartAt (Model (2 * n)) a).target, (C y).IsInvertible) :
    ContDiffOn ℝ ∞
      (fun y => squaredCoframeCoefficient (C y) (squaredTensorInChart M a s.tensor y))
      (chartAt (Model (2 * n)) a).target :=
  contDiffOn_squaredCoframeCoefficient hC hinv (s.smooth a)

/-- Its scalar coordinate is nonzero because the intrinsic section is
nonzero and local determinant reconstruction is exact. -/
theorem coframeCoefficient_ne_zero {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (a : M.Point)
    (C : Model (2 * n) →L[ℝ] TangentCoordinates n) (hinv : C.IsInvertible)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (hCJ : ∀ v, C (almostComplexInChart M a s.J y v) = coordinateComplexStructure n (C v)) :
    squaredCoframeCoefficient C (squaredTensorInChart M a s.tensor y) ≠ 0 := by
  intro hz
  have h := squaredCoframe_reconstruction C hinv (almostComplexInChart M a s.J y) hCJ
    (squaredTensorInChart M a s.tensor y) (squaredTensorInChart_canonical M a s.J s.tensor s.canonical y hy)
  apply squaredTensorInChart_ne_zero M a s.tensor s.nowhereZero y hy
  ext v
  have he := congrArg (fun t : SquaredCanonicalTensor n => t v) h
  simpa [hz, smul_eq_mul] using he

/-- At every chart center an actual Maslov section has smooth nonzero
scalar coordinates in a locally constructed complex coframe. The coframe
is produced from its almost complex field, with no seed hypothesis. -/
theorem exists_local_projected_coframeCoordinates {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (a : M.Point) :
    ∃ C₀ : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∃ V ⊆ (chartAt (Model (2 * n)) a).target,
      IsOpen V ∧ chartAt (Model (2 * n)) a a ∈ V ∧
      ContDiffOn ℝ ∞ (fun y => squaredCoframeCoefficient
        (projectedComplexCoframe C₀ (almostComplexInChart M a s.J y))
        (squaredTensorInChart M a s.tensor y)) V ∧
      (∀ y ∈ V, squaredCoframeCoefficient
        (projectedComplexCoframe C₀ (almostComplexInChart M a s.J y))
        (squaredTensorInChart M a s.tensor y) ≠ 0) := by
  let c := chartAt (Model (2 * n)) a
  have ha : c a ∈ c.target := c.map_source (mem_chart_source _ a)
  obtain ⟨C₀, V, hVc, hVo, haV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_complexCoframe c.open_target ha (s.compatible.1 a)
      (fun y hy => almostComplexInChart_sq M a s.J s.compatible.2.1 y hy)
  refine ⟨C₀, V, hVc, hVo, haV, ?_, ?_⟩
  · exact contDiffOn_squaredCoframeCoefficient hC hinv ((s.smooth a).mono hVc)
  · intro y hy
    exact s.coframeCoefficient_ne_zero a _ (hinv y hy) y (hVc hy) (hCJ y hy)

end MaslovRepresentative

end FsFltz.Geometry
