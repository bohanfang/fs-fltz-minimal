import FsFltz.Geometry.PrescribedGrading
import FsFltz.Geometry.SymplecticBridge
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Topology.Instances.Matrix

/-!
# Tensor producers for the prescribed endpoint gradings

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, especially
236–243, and `sec:lean`, lines 794–814. The determinant square is constructed
as an actual continuous multilinear map and pulled back by the actual real
and circle-coordinate differentials. Smoothness, nonvanishing, and the
squared-canonical equations for the intrinsic transported `J` are proved.
Smoothness and symplectic compatibility of that `J`, and the rank-one bundle
interpretation of the squared canonical fibers, remain separate bridges.
No geometric comparison or grading transport along a chain is asserted.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- The determinant, as a continuous complex multilinear map in its rows. -/
def complexDeterminantTensor (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩

@[simp] theorem complexDeterminantTensor_apply {n : ℕ} (v : Fin n → Fin n → ℂ) :
    complexDeterminantTensor n v = Matrix.det v := rfl

/-- The tensor square keeps its two alternating blocks separately labelled. -/
def complexSquaredDeterminantTensor (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ⊕ Fin n => Fin n → ℂ) ℂ :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (complexDeterminantTensor n)
    |>.compContinuousMultilinearMap (complexDeterminantTensor n)).uncurrySum

@[simp] theorem complexSquaredDeterminantTensor_apply {n : ℕ}
    (v : Fin n ⊕ Fin n → Fin n → ℂ) :
    complexSquaredDeterminantTensor n v =
      Matrix.det (fun i => v (Sum.inl i)) * Matrix.det (fun i => v (Sum.inr i)) := by
  simp [complexSquaredDeterminantTensor, ContinuousMultilinearMap.uncurrySum_apply,
    smul_eq_mul]
  rfl

/-- Complexification of a pair of real coordinate vectors. -/
def complexifyTangentCoordinates (n : ℕ) :
    TangentCoordinates n →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun j =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))) +
    Complex.I • Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n))))

@[simp] theorem complexifyTangentCoordinates_apply {n : ℕ}
    (q : TangentCoordinates n) (j : Fin n) :
    complexifyTangentCoordinates n q j = (q.1 j : ℂ) + Complex.I * (q.2 j : ℂ) := by
  simp [complexifyTangentCoordinates]

/-- The literal determinant-square formula is a continuous real multilinear tensor. -/
def coordinateSquaredVolumeTensor (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => TangentCoordinates n) ℂ :=
  ((complexSquaredDeterminantTensor n).restrictScalars ℝ).compContinuousLinearMap
    (fun _ => complexifyTangentCoordinates n)

@[simp] theorem coordinateSquaredVolumeTensor_apply {n : ℕ}
    (v : Fin n ⊕ Fin n → TangentCoordinates n) :
    coordinateSquaredVolumeTensor n v = coordinateSquaredVolumeValue v := by
  simp [coordinateSquaredVolumeTensor, coordinateSquaredVolumeValue,
    coordinateVolumeValue, complexifyTangentCoordinates]

/-- The actual `du,dtheta` coframe, bundled as a continuous linear map. -/
def lgTangentCoframe {n : ℕ} (y : (lgManifold n).Point) :
    (lgManifold n).Tangent y →L[ℝ] TangentCoordinates n :=
  (ContinuousLinearMap.pi (fun j => lgLogCovector j y)).prod
    (ContinuousLinearMap.pi (fun j => lgAngleCovector j y))

/-- The actual `dp,dtheta` coframe uses the source's vertical-first order. -/
def cotangentTangentCoframe {n : ℕ} (y : (cotangentManifold n).Point) :
    (cotangentManifold n).Tangent y →L[ℝ] TangentCoordinates n :=
  (ContinuousLinearMap.pi (fun j => cotangentMomentumCovector j y)).prod
    (ContinuousLinearMap.pi (fun j => cotangentAngleCovector j y))

theorem lgTangentCoframe_lgCover {n : ℕ} (x q : TangentCoordinates n) :
    lgTangentCoframe (lgCover x) (lgCoverTangent x q) = q := by
  apply Prod.ext <;> funext j
  · exact lgLogCovector_lgCover j x q
  · exact lgAngleCovector_lgCover j x q

theorem cotangentTangentCoframe_cotangentCover {n : ℕ} (x q : TangentCoordinates n) :
    cotangentTangentCoframe (cotangentCover x) (cotangentCoverTangent x q) = q.swap := by
  apply Prod.ext <;> funext j
  · exact cotangentMomentumCovector_cotangentCover j x q
  · exact cotangentAngleCovector_cotangentCover j x q

/-- The logarithmic endpoint tensor on every point of the actual quotient. -/
def logarithmicSquaredVolumeTensor (n : ℕ) :
    (lgManifold n).Point → SquaredCanonicalTensor n :=
  fun y => (coordinateSquaredVolumeTensor n).compContinuousLinearMap
    (fun _ => lgTangentCoframe y)

/-- The cotangent endpoint tensor on the whole cotangent quotient. -/
def cotangentSquaredVolumeTensor (n : ℕ) :
    (cotangentManifold n).Point → SquaredCanonicalTensor n :=
  fun y => (coordinateSquaredVolumeTensor n).compContinuousLinearMap
    (fun _ => cotangentTangentCoframe y)

theorem logarithmicSquaredVolumeTensor_apply {n : ℕ} (y : (lgManifold n).Point)
    (v : Fin n ⊕ Fin n → (lgManifold n).Tangent y) :
    logarithmicSquaredVolumeTensor n y v = coordinateSquaredVolumeValue
      (fun i => logarithmicTangentCoordinates (lgManifold n) id y (v i)) := rfl

theorem cotangentSquaredVolumeTensor_apply {n : ℕ} (y : (cotangentManifold n).Point)
    (v : Fin n ⊕ Fin n → (cotangentManifold n).Tangent y) :
    cotangentSquaredVolumeTensor n y v = coordinateSquaredVolumeValue
      (fun i => cotangentTangentCoordinates (cotangentManifold n) id y (v i)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem logarithmicSquaredVolumeTensor_lgCover {n : ℕ} (x : TangentCoordinates n)
    (v : Fin n ⊕ Fin n → TangentCoordinates n) :
    logarithmicSquaredVolumeTensor n (lgCover x) (fun i => lgCoverTangent x (v i)) =
      coordinateSquaredVolumeValue v := by
  simp only [logarithmicSquaredVolumeTensor,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateSquaredVolumeTensor_apply]
  congr 1
  funext i
  exact lgTangentCoframe_lgCover x (v i)

set_option backward.isDefEq.respectTransparency false in
theorem cotangentSquaredVolumeTensor_cotangentCover {n : ℕ} (x : TangentCoordinates n)
    (v : Fin n ⊕ Fin n → TangentCoordinates n) :
    cotangentSquaredVolumeTensor n (cotangentCover x)
        (fun i => cotangentCoverTangent x (v i)) =
      coordinateSquaredVolumeValue (fun i => (v i).swap) := by
  simp only [cotangentSquaredVolumeTensor,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    coordinateSquaredVolumeTensor_apply]
  congr 1
  funext i
  exact cotangentTangentCoframe_cotangentCover x (v i)

set_option backward.isDefEq.respectTransparency false in
/-- Nonvanishing is witnessed by actual quotient tangent frames, also in rank zero. -/
theorem logarithmicSquaredVolumeTensor_ne_zero {n : ℕ} (y : (lgManifold n).Point) :
    logarithmicSquaredVolumeTensor n y ≠ 0 := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  intro h
  have hv := logarithmicSquaredVolumeTensor_lgCover x
    (fun i => verticalFrame n (i.elim id id))
  rw [h, zero_apply, coordinateSquaredVolumeValue_verticalFrame] at hv
  exact zero_ne_one hv

set_option backward.isDefEq.respectTransparency false in
theorem cotangentSquaredVolumeTensor_ne_zero {n : ℕ} (y : (cotangentManifold n).Point) :
    cotangentSquaredVolumeTensor n y ≠ 0 := by
  obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
  intro h
  have hv := cotangentSquaredVolumeTensor_cotangentCover x
    (fun i => (verticalFrame n (i.elim id id)).swap)
  simp only [Prod.swap_swap] at hv
  rw [h, zero_apply, coordinateSquaredVolumeValue_verticalFrame] at hv
  exact zero_ne_one hv

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of an actual one-form recovers smoothness of its covector
coefficients through the inverse of the native one-form linear isometry. -/
theorem contDiffOn_covector_comp_inverseChart {d : ℕ} (M : SmoothManifold d)
    (b : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hb : M.IsSmoothForm (covectorForm M b)) (a : M.Point) :
    ContDiffOn ℝ ∞ (fun y : Model d =>
      ((b ((chartAt (Model d) a).symm y)).comp (M.inverseChartTangentMap a y) :
        Model d →L[ℝ] ℝ)) (chartAt (Model d) a).target := by
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  apply (e.symm.contDiff.comp_contDiffOn (hb a)).congr
  intro y _
  apply e.injective
  ext v
  rfl

/-- Finite families of smoothly varying covectors assemble smoothly. -/
theorem contDiffOn_piCovector {d n : ℕ} {s : Set (Model d)}
    {b : Fin n → Model d → Model d →L[ℝ] ℝ}
    (hb : ∀ j, ContDiffOn ℝ ∞ (b j) s) :
    ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.pi (fun j => b j y)) s := by
  exact (ContinuousLinearMap.piEquivL ℝ (Model d) (fun _ : Fin n => ℝ)).contDiff
    |>.comp_contDiffOn (contDiffOn_pi.mpr hb)

set_option backward.isDefEq.respectTransparency false in
/-- The transported quotient coframe is smooth in every actual atlas chart. -/
theorem contDiffOn_lgTangentCoframe_inChart {n : ℕ} (a : (lgManifold n).Point) :
    ContDiffOn ℝ ∞ (fun y : Model (2 * n) =>
      ((lgTangentCoframe ((chartAt (Model (2 * n)) a).symm y)).comp
        ((lgManifold n).inverseChartTangentMap a y) :
          Model (2 * n) →L[ℝ] TangentCoordinates n))
      (chartAt (Model (2 * n)) a).target := by
  have hu := contDiffOn_piCovector (fun j =>
    contDiffOn_covector_comp_inverseChart (lgManifold n) (lgLogCovector j)
      (isSmoothForm_lgLogCovector j) a)
  have ht := contDiffOn_piCovector (fun j =>
    contDiffOn_covector_comp_inverseChart (lgManifold n) (lgAngleCovector j)
      (isSmoothForm_lgAngleCovector j) a)
  apply ((ContinuousLinearMap.prodL (𝕜 := ℝ) (E := Model (2 * n))
    (F := RealSpace n) (G := RealSpace n) ℝ).contDiff.comp_contDiffOn
      (hu.prodMk ht)).congr
  intro y _
  ext q j <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_cotangentTangentCoframe_inChart {n : ℕ}
    (a : (cotangentManifold n).Point) :
    ContDiffOn ℝ ∞ (fun y : Model (2 * n) =>
      ((cotangentTangentCoframe ((chartAt (Model (2 * n)) a).symm y)).comp
        ((cotangentManifold n).inverseChartTangentMap a y) :
          Model (2 * n) →L[ℝ] TangentCoordinates n))
      (chartAt (Model (2 * n)) a).target := by
  have hp := contDiffOn_piCovector (fun j =>
    contDiffOn_covector_comp_inverseChart (cotangentManifold n)
      (cotangentMomentumCovector j) (isSmoothForm_cotangentMomentumCovector j) a)
  have ht := contDiffOn_piCovector (fun j =>
    contDiffOn_covector_comp_inverseChart (cotangentManifold n)
      (cotangentAngleCovector j) (isSmoothForm_cotangentAngleCovector j) a)
  apply ((ContinuousLinearMap.prodL (𝕜 := ℝ) (E := Model (2 * n))
    (F := RealSpace n) (G := RealSpace n) ℝ).contDiff.comp_contDiffOn
      (hp.prodMk ht)).congr
  intro y _
  ext q j <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed logarithmic tensor is smooth on the entire quotient ambient. -/
theorem isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor (n : ℕ) :
    IsSmoothSquaredTensorSection (lgManifold n) (logarithmicSquaredVolumeTensor n) := by
  intro a
  have h := ((coordinateSquaredVolumeTensor n).compContinuousLinearMapLRight
    (E := fun _ => Model (2 * n))).contDiff
    |>.comp_contDiffOn (contDiffOn_pi.mpr
      (fun _ : Fin n ⊕ Fin n => contDiffOn_lgTangentCoframe_inChart a))
  apply h.congr
  intro y _
  ext v
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The vertical-phase-zero tensor is smooth on the entire cotangent ambient. -/
theorem isSmoothSquaredTensorSection_cotangentSquaredVolumeTensor (n : ℕ) :
    IsSmoothSquaredTensorSection (cotangentManifold n) (cotangentSquaredVolumeTensor n) := by
  intro a
  have h := ((coordinateSquaredVolumeTensor n).compContinuousLinearMapLRight
    (E := fun _ => Model (2 * n))).contDiff
    |>.comp_contDiffOn (contDiffOn_pi.mpr
      (fun _ : Fin n ⊕ Fin n => contDiffOn_cotangentTangentCoframe_inChart a))
  apply h.congr
  intro y _
  ext v
  rfl

/-- The based logarithmic complex structure `J(du,dtheta)=(-dtheta,du)`. -/
def coordinateComplexStructure (n : ℕ) : TangentCoordinates n →L[ℝ] TangentCoordinates n :=
  (-(ContinuousLinearMap.snd ℝ (RealSpace n) (RealSpace n))).prod
    (ContinuousLinearMap.fst ℝ (RealSpace n) (RealSpace n))

@[simp] theorem coordinateComplexStructure_apply {n : ℕ} (q : TangentCoordinates n) :
    coordinateComplexStructure n q = (-q.2, q.1) := rfl

theorem coordinateComplexStructure_sq {n : ℕ} (q : TangentCoordinates n) :
    coordinateComplexStructure n (coordinateComplexStructure n q) = -q := by
  apply Prod.ext <;> funext j <;> simp [coordinateComplexStructure_apply]

theorem complexify_coordinateComplexStructure {n : ℕ} (q : TangentCoordinates n) :
    complexifyTangentCoordinates n (coordinateComplexStructure n q) =
      Complex.I • complexifyTangentCoordinates n q := by
  ext j
  simp [coordinateComplexStructure_apply]
  ring_nf
  simp

/-- Separate alternation and slotwise complex linearity prove the project's
squared-canonical predicate after any intertwining tangent-coordinate map. -/
theorem isSquaredCanonicalTensor_coordinateSquaredVolumeTensor {n : ℕ}
    (L : Model (2 * n) →L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, L (J v) = coordinateComplexStructure n (L v)) :
    IsSquaredCanonicalTensor J
      ((coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => L)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v i j hij hv
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      coordinateSquaredVolumeTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.coe_restrictScalars, complexSquaredDeterminantTensor_apply]
    have hd : Matrix.det (fun k => complexifyTangentCoordinates n (L (v (Sum.inl k)))) = 0 :=
      Matrix.detRowAlternating.map_eq_zero_of_eq _ (congrArg
        (fun q => complexifyTangentCoordinates n (L q)) hv) hij
    rw [hd, zero_mul]
  · intro v i j hij hv
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      coordinateSquaredVolumeTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.coe_restrictScalars, complexSquaredDeterminantTensor_apply]
    have hd : Matrix.det (fun k => complexifyTangentCoordinates n (L (v (Sum.inr k)))) = 0 :=
      Matrix.detRowAlternating.map_eq_zero_of_eq _ (congrArg
        (fun q => complexifyTangentCoordinates n (L q)) hv) hij
    rw [hd, mul_zero]
  · intro v i
    classical
    let w : Fin n ⊕ Fin n → Fin n → ℂ := fun k => complexifyTangentCoordinates n (L (v k))
    have hu : (fun k => complexifyTangentCoordinates n (L
        (Function.update v i (J (v i)) k))) = Function.update w i (Complex.I • w i) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp only [Function.update_self, hJ, complexify_coordinateComplexStructure]
        rfl
      · simp only [Function.update_of_ne hk]
        rfl
    change complexSquaredDeterminantTensor n
      (fun k => complexifyTangentCoordinates n (L (Function.update v i (J (v i)) k))) =
        Complex.I * complexSquaredDeterminantTensor n w
    rw [hu, ContinuousMultilinearMap.map_update_smul, Function.update_eq_self]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem lgTangentCoframe_bijective {n : ℕ} (y : (lgManifold n).Point) :
    Function.Bijective (lgTangentCoframe y) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  constructor
  · intro v w hvw
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    obtain ⟨r, rfl⟩ := (lgCoverTangent_bijective x).2 w
    have hqr : q = r := by simpa only [lgTangentCoframe_lgCover] using hvw
    rw [hqr]
  · intro q
    exact ⟨lgCoverTangent x q, lgTangentCoframe_lgCover x q⟩

set_option backward.isDefEq.respectTransparency false in
theorem cotangentTangentCoframe_bijective {n : ℕ} (y : (cotangentManifold n).Point) :
    Function.Bijective (cotangentTangentCoframe y) := by
  obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
  constructor
  · intro v w hvw
    obtain ⟨q, rfl⟩ := (cotangentCoverTangent_bijective x).2 v
    obtain ⟨r, rfl⟩ := (cotangentCoverTangent_bijective x).2 w
    have hqr : q.swap = r.swap := by
      simpa only [cotangentTangentCoframe_cotangentCover] using hvw
    have hqr' : q = r := by simpa only [Prod.swap_swap] using congrArg Prod.swap hqr
    rw [hqr']
  · intro q
    refine ⟨cotangentCoverTangent x q.swap, ?_⟩
    rw [cotangentTangentCoframe_cotangentCover, Prod.swap_swap]

/-- The actual quotient coframe is a continuous linear equivalence. -/
def lgTangentCoframeEquiv {n : ℕ} (y : (lgManifold n).Point) :
    (lgManifold n).Tangent y ≃L[ℝ] TangentCoordinates n :=
  (LinearEquiv.ofBijective (lgTangentCoframe y).toLinearMap
    (lgTangentCoframe_bijective y)).toContinuousLinearEquiv

def cotangentTangentCoframeEquiv {n : ℕ} (y : (cotangentManifold n).Point) :
    (cotangentManifold n).Tangent y ≃L[ℝ] TangentCoordinates n :=
  (LinearEquiv.ofBijective (cotangentTangentCoframe y).toLinearMap
    (cotangentTangentCoframe_bijective y)).toContinuousLinearEquiv

/-- The intrinsic field obtained by transporting the source's based `J`.
Smoothness and compatibility with the actual symplectic form are separate obligations. -/
def logarithmicAlmostComplexField (n : ℕ) : AlmostComplexField (lgManifold n) :=
  fun y => (lgTangentCoframeEquiv y).symm.toContinuousLinearMap.comp
    ((coordinateComplexStructure n).comp (lgTangentCoframeEquiv y).toContinuousLinearMap)

def cotangentAlmostComplexField (n : ℕ) : AlmostComplexField (cotangentManifold n) :=
  fun y => (cotangentTangentCoframeEquiv y).symm.toContinuousLinearMap.comp
    ((coordinateComplexStructure n).comp (cotangentTangentCoframeEquiv y).toContinuousLinearMap)

set_option backward.isDefEq.respectTransparency false in
theorem lgTangentCoframe_almostComplex {n : ℕ} (y : (lgManifold n).Point)
    (v : (lgManifold n).Tangent y) :
    lgTangentCoframe y (logarithmicAlmostComplexField n y v) =
      coordinateComplexStructure n (lgTangentCoframe y v) := by
  change lgTangentCoframeEquiv y
    ((lgTangentCoframeEquiv y).symm (coordinateComplexStructure n (lgTangentCoframeEquiv y v))) = _
  exact (lgTangentCoframeEquiv y).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
theorem cotangentTangentCoframe_almostComplex {n : ℕ} (y : (cotangentManifold n).Point)
    (v : (cotangentManifold n).Tangent y) :
    cotangentTangentCoframe y (cotangentAlmostComplexField n y v) =
      coordinateComplexStructure n (cotangentTangentCoframe y v) := by
  change cotangentTangentCoframeEquiv y
    ((cotangentTangentCoframeEquiv y).symm
      (coordinateComplexStructure n (cotangentTangentCoframeEquiv y v))) = _
  exact (cotangentTangentCoframeEquiv y).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
theorem logarithmicAlmostComplexField_sq {n : ℕ} (y : (lgManifold n).Point)
    (v : (lgManifold n).Tangent y) :
    logarithmicAlmostComplexField n y (logarithmicAlmostComplexField n y v) = -v := by
  apply (lgTangentCoframe_bijective y).1
  rw [lgTangentCoframe_almostComplex, lgTangentCoframe_almostComplex,
    coordinateComplexStructure_sq, map_neg]

set_option backward.isDefEq.respectTransparency false in
theorem cotangentAlmostComplexField_sq {n : ℕ} (y : (cotangentManifold n).Point)
    (v : (cotangentManifold n).Tangent y) :
    cotangentAlmostComplexField n y (cotangentAlmostComplexField n y v) = -v := by
  apply (cotangentTangentCoframe_bijective y).1
  rw [cotangentTangentCoframe_almostComplex, cotangentTangentCoframe_almostComplex,
    coordinateComplexStructure_sq, map_neg]

set_option backward.isDefEq.respectTransparency false in
theorem logarithmicSquaredVolumeTensor_canonical {n : ℕ} (y : (lgManifold n).Point) :
    IsSquaredCanonicalTensor (logarithmicAlmostComplexField n y)
      (logarithmicSquaredVolumeTensor n y) :=
  isSquaredCanonicalTensor_coordinateSquaredVolumeTensor (lgTangentCoframe y)
    (logarithmicAlmostComplexField n y) (lgTangentCoframe_almostComplex y)

set_option backward.isDefEq.respectTransparency false in
theorem cotangentSquaredVolumeTensor_canonical {n : ℕ} (y : (cotangentManifold n).Point) :
    IsSquaredCanonicalTensor (cotangentAlmostComplexField n y)
      (cotangentSquaredVolumeTensor n y) :=
  isSquaredCanonicalTensor_coordinateSquaredVolumeTensor (cotangentTangentCoframe y)
    (cotangentAlmostComplexField n y) (cotangentTangentCoframe_almostComplex y)

set_option backward.isDefEq.respectTransparency false in
/-- The existing prescribed-grading predicate selects exactly the constructed
smooth nowhere-zero logarithmic tensor, independently of the representative's `J`. -/
theorem isLogarithmicGrading_id_iff_tensor_eq {n : ℕ}
    {eta : (lgManifold n).Form 2} (s : MaslovRepresentative (lgManifold n) eta) :
    IsLogarithmicGrading id s ↔ s.tensor = logarithmicSquaredVolumeTensor n := by
  constructor
  · intro h
    funext x
    ext v
    exact (h x v).trans (logarithmicSquaredVolumeTensor_apply x v).symm
  · intro h x v
    rw [h]
    exact logarithmicSquaredVolumeTensor_apply x v

set_option backward.isDefEq.respectTransparency false in
/-- The cotangent prescription likewise selects the actual vertical-phase-zero tensor. -/
theorem isVerticalGrading_id_iff_tensor_eq {n : ℕ}
    {eta : (cotangentManifold n).Form 2}
    (s : MaslovRepresentative (cotangentManifold n) eta) :
    IsVerticalGrading id s ↔ s.tensor = cotangentSquaredVolumeTensor n := by
  constructor
  · intro h
    funext x
    ext v
    exact (h x v).trans (cotangentSquaredVolumeTensor_apply x v).symm
  · intro h x v
    rw [h]
    exact cotangentSquaredVolumeTensor_apply x v

end FsFltz.Geometry
