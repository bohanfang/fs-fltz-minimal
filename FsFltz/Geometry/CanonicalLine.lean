import FsFltz.Geometry.PrescribedGradingBridge
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Determinant

/-!
# Canonical fibers and their genuine complex tensor product

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The multiplication map below is defined on the
actual complex tensor product of canonical fibers. Its values are exactly
the two separately alternating blocks used by the Maslov representation.
The endpoint determinant squares are consumers of this map.

`CanonicalCoframe` constructs complex coframes for arbitrary almost complex
structures and proves the fiber equivalence without a supplied coframe.
The global smooth bundle correspondence remains a separate foundation.
-/

noncomputable section
open scoped TensorProduct

namespace FsFltz.Geometry

/-- The existing canonical predicate cuts out a complex vector subspace. -/
def canonicalSubmodule {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) : Submodule ℂ (CanonicalTensor n) where
  carrier := {s | IsCanonicalTensor J s}
  zero_mem' := by intro v i; simp
  add_mem' := by
    intro s t hs ht v i
    simp only [ContinuousAlternatingMap.add_apply, hs v i, ht v i, mul_add]
  smul_mem' := by
    intro c s hs v i
    simp only [ContinuousAlternatingMap.smul_apply, hs v i, smul_eq_mul]
    ring

/-- The existing squared predicate is likewise a complex vector subspace. -/
def squaredCanonicalSubmodule {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    Submodule ℂ (SquaredCanonicalTensor n) where
  carrier := {s | IsSquaredCanonicalTensor J s}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp
  add_mem' := by
    rintro s t ⟨hs₁, hs₂, hs₃⟩ ⟨ht₁, ht₂, ht₃⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v i j hij hv
      simp [hs₁ v i j hij hv, ht₁ v i j hij hv]
    · intro v i j hij hv
      simp [hs₂ v i j hij hv, ht₂ v i j hij hv]
    · intro v i
      simp only [add_apply, hs₃ v i, ht₃ v i, mul_add]
  smul_mem' := by
    rintro c s ⟨hs₁, hs₂, hs₃⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v i j hij hv
      simp [hs₁ v i j hij hv]
    · intro v i j hij hv
      simp [hs₂ v i j hij hv]
    · intro v i
      simp only [smul_apply, hs₃ v i, smul_eq_mul]
      ring

/-- Pointwise multiplication of two alternating tensors, with independent blocks. -/
def canonicalTensorProduct {n : ℕ} (s t : CanonicalTensor n) :
    SquaredCanonicalTensor n :=
  ((ContinuousLinearMap.id ℝ ℂ).smulRight t.toContinuousMultilinearMap
    |>.compContinuousMultilinearMap s.toContinuousMultilinearMap).uncurrySum

@[simp] theorem canonicalTensorProduct_apply {n : ℕ} (s t : CanonicalTensor n)
    (v : Fin n ⊕ Fin n → Model (2 * n)) :
    canonicalTensorProduct s t v = s (fun i => v (Sum.inl i)) *
      t (fun i => v (Sum.inr i)) := by
  simp [canonicalTensorProduct, ContinuousMultilinearMap.uncurrySum_apply, smul_eq_mul]
  rfl

theorem canonicalTensorProduct_canonical {n : ℕ}
    {J : Model (2 * n) →L[ℝ] Model (2 * n)} {s t : CanonicalTensor n}
    (hs : IsCanonicalTensor J s) (ht : IsCanonicalTensor J t) :
    IsSquaredCanonicalTensor J (canonicalTensorProduct s t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v i j hij hv
    rw [canonicalTensorProduct_apply, s.map_eq_zero_of_eq (fun i => v (Sum.inl i)) hv hij]
    exact zero_mul _
  · intro v i j hij hv
    rw [canonicalTensorProduct_apply, t.map_eq_zero_of_eq (fun i => v (Sum.inr i)) hv hij]
    exact mul_zero _
  · intro v i
    cases i with
    | inl i =>
      have hleft : (fun j => Function.update v (Sum.inl i) (J (v (Sum.inl i)))
          (Sum.inl j)) = Function.update (fun j => v (Sum.inl j)) i (J (v (Sum.inl i))) := by
        funext j
        by_cases h : j = i <;> simp [h]
      have hright : (fun j => Function.update v (Sum.inl i) (J (v (Sum.inl i)))
          (Sum.inr j)) = (fun j => v (Sum.inr j)) := by funext j; simp
      rw [canonicalTensorProduct_apply, hleft, hright, hs]
      simp [canonicalTensorProduct_apply, mul_assoc]
    | inr i =>
      have hleft : (fun j => Function.update v (Sum.inr i) (J (v (Sum.inr i)))
          (Sum.inl j)) = (fun j => v (Sum.inl j)) := by funext j; simp
      have hright : (fun j => Function.update v (Sum.inr i) (J (v (Sum.inr i)))
          (Sum.inr j)) = Function.update (fun j => v (Sum.inr j)) i (J (v (Sum.inr i))) := by
        funext j
        by_cases h : j = i <;> simp [h]
      rw [canonicalTensorProduct_apply, hleft, hright, ht]
      simp only [canonicalTensorProduct_apply]
      ring

/-- The canonical product is complex bilinear; this is the producer for the
actual tensor-product linear map, rather than a predicate assuming its existence. -/
def canonicalProductBilinear {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    canonicalSubmodule J →ₗ[ℂ] canonicalSubmodule J →ₗ[ℂ] squaredCanonicalSubmodule J :=
  LinearMap.mk₂ ℂ
    (fun s t => ⟨canonicalTensorProduct s.val t.val,
      canonicalTensorProduct_canonical s.property t.property⟩)
    (by intro s₁ s₂ t; apply Subtype.ext; ext v; simp [add_mul])
    (by intro c s t; apply Subtype.ext; ext v; simp [smul_eq_mul, mul_assoc])
    (by intro s t₁ t₂; apply Subtype.ext; ext v; simp [mul_add])
    (by intro c s t; apply Subtype.ext; ext v; simp [smul_eq_mul]; ring)

/-- The genuine map `K_J ⊗ℂ K_J` to the concrete squared-canonical fiber. -/
def canonicalSquareMap {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) :
    TensorProduct ℂ (canonicalSubmodule J) (canonicalSubmodule J) →ₗ[ℂ]
      squaredCanonicalSubmodule J :=
  TensorProduct.lift (canonicalProductBilinear J)

@[simp] theorem canonicalSquareMap_tmul {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (s t : canonicalSubmodule J) :
    (canonicalSquareMap J (s ⊗ₜ[ℂ] t)).val = canonicalTensorProduct s.val t.val := by
  rw [canonicalSquareMap, TensorProduct.lift.tmul]
  rfl

/-- Real multilinearity and the `I` equation imply full complex multilinearity.
This reconstructs the complex tensor rather than assuming a complex lift. -/
def complexMultilinearOfI {ι : Type*} [decι : DecidableEq ι] {n : ℕ}
    (s : ContinuousMultilinearMap ℝ (fun _ : ι => Fin n → ℂ) ℂ)
    (hI : ∀ v i, s (Function.update v i (Complex.I • v i)) = Complex.I * s v) :
    ContinuousMultilinearMap ℂ (fun _ : ι => Fin n → ℂ) ℂ where
  toMultilinearMap :=
    { toFun := s
      map_update_add' := by intro _ v i x y; exact s.map_update_add v i x y
      map_update_smul' := by
        intro decι' v i c x
        have hd : decι' = decι := Subsingleton.elim _ _
        subst decι'
        have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
          ext j
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          rw [← mul_assoc, ← add_mul, Complex.re_add_im]
        have hx : s (Function.update v i (Complex.I • x)) =
            Complex.I * s (Function.update v i x) := by
          simpa only [Function.update_self, Function.update_idem] using
            hI (Function.update v i x) i
        rw [hc, s.map_update_add, s.map_update_smul, s.map_update_smul, hx]
        simp only [Complex.real_smul, smul_eq_mul]
        rw [← mul_assoc, ← add_mul, Complex.re_add_im] }
  cont := s.cont

/-- Every top-degree complex alternating form is determined by its standard-frame value. -/
theorem complexAlternating_determinant {n : ℕ}
    (s : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ) (v : Fin n → Fin n → ℂ) :
    s v = s (Pi.basisFun ℂ (Fin n)) * Matrix.det v := by
  have h := congrArg (fun a : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ => a v)
    (s.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin n)))
  simpa [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Matrix.det_transpose,
    Matrix.det]
    using h

/-- The real coordinate pairs and complex coordinates are genuinely equivalent. -/
def complexifyTangentCoordinatesEquiv (n : ℕ) :
    TangentCoordinates n ≃L[ℝ] (Fin n → ℂ) where
  toLinearEquiv :=
    { (complexifyTangentCoordinates n).toLinearMap with
      invFun := fun z => (fun j => (z j).re, fun j => (z j).im)
      left_inv := by
        intro q
        apply Prod.ext <;> funext j <;> simp
      right_inv := by
        intro z
        funext j
        change (complexifyTangentCoordinates n
          (fun j => (z j).re, fun j => (z j).im)) j = z j
        simp [mul_comm Complex.I] }
  continuous_toFun := (complexifyTangentCoordinates n).continuous
  continuous_invFun := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro j
    · exact Complex.continuous_re.comp (continuous_apply j)
    · exact Complex.continuous_im.comp (continuous_apply j)

@[simp] theorem complexifyTangentCoordinatesEquiv_apply {n : ℕ}
    (q : TangentCoordinates n) :
    complexifyTangentCoordinatesEquiv n q = complexifyTangentCoordinates n q := rfl

/-- A real coframe turns the concrete `(n,0)` equation into an actual complex
alternating form. The lift is proved from the equation, not supplied as input. -/
def canonicalComplexForm {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : canonicalSubmodule J) : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ := by
  let e := C.trans (complexifyTangentCoordinatesEquiv n)
  let f := s.val.compContinuousLinearMap e.symm.toContinuousLinearMap
  have hi (z : Fin n → ℂ) : e.symm (Complex.I • z) = J (e.symm z) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change Complex.I • z = complexifyTangentCoordinates n (C (J (e.symm z)))
    rw [hJ, complexify_coordinateComplexStructure]
    exact congrArg (fun a => Complex.I • a) (e.apply_symm_apply z).symm
  have hI : ∀ v i, f (Function.update v i (Complex.I • v i)) = Complex.I * f v := by
    intro v i
    have hu : (fun k => e.symm (Function.update v i (Complex.I • v i) k)) =
        Function.update (fun k => e.symm (v k)) i (J (e.symm (v i))) := by
      funext k
      by_cases hk : k = i
      · subst k; simp [hi]
      · simp [hk]
    change s.val (fun k => e.symm (Function.update v i (Complex.I • v i) k)) =
      Complex.I * s.val (fun k => e.symm (v k))
    rw [hu]
    exact s.property _ _
  exact ⟨complexMultilinearOfI f.toContinuousMultilinearMap hI,
    fun v i j hv hij => f.map_eq_zero_of_eq v hv hij⟩

@[simp] theorem canonicalComplexForm_apply {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : canonicalSubmodule J) (v : Fin n → Fin n → ℂ) :
    canonicalComplexForm C J hJ s v =
      s.val (fun i => C.symm ((complexifyTangentCoordinatesEquiv n).symm (v i))) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact determinant reconstruction proves the rank-one property in every
given complex coframe, including the empty frame in complex dimension zero. -/
theorem canonicalTensor_reconstruction {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : canonicalSubmodule J) (v : Fin n → Model (2 * n)) :
    s.val v = s.val (fun i => C.symm (verticalFrame n i)) *
      coordinateVolumeValue (fun i => C (v i)) := by
  have h := complexAlternating_determinant (canonicalComplexForm C J hJ s)
    (fun i => complexifyTangentCoordinates n (C (v i)))
  have hb : (fun i => C.symm ((complexifyTangentCoordinatesEquiv n).symm
      ((Pi.basisFun ℂ (Fin n)) i))) = (fun i => C.symm (verticalFrame n i)) := by
    funext i
    congr 1
    apply (complexifyTangentCoordinatesEquiv n).injective
    ext j
    by_cases hij : i = j <;> simp [Pi.basisFun_apply, verticalFrame, hij]
  simp only [canonicalComplexForm_apply, ← complexifyTangentCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply, hb] at h
  exact h

/-- Determinant reconstruction in both blocks of a separately alternating
complex tensor. No decomposability is assumed: it follows from the two
top-degree alternating conditions. -/
theorem complexSquaredTensor_reconstruction {n : ℕ}
    (s : ContinuousMultilinearMap ℂ (fun _ : Fin n ⊕ Fin n => Fin n → ℂ) ℂ)
    (hleft : ∀ v i j, i ≠ j → v (Sum.inl i) = v (Sum.inl j) → s v = 0)
    (hright : ∀ v i j, i ≠ j → v (Sum.inr i) = v (Sum.inr j) → s v = 0)
    (v : Fin n ⊕ Fin n → Fin n → ℂ) :
    s v = s (Sum.elim (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))) *
      (Matrix.det (fun i => v (Sum.inl i)) * Matrix.det (fun i => v (Sum.inr i))) := by
  let b := Pi.basisFun ℂ (Fin n)
  have hswap (w : Fin n → Fin n → ℂ) :
      (fun i => Sum.elim b w ((Equiv.sumComm (Fin n) (Fin n)) i)) = Sum.elim w b := by
    funext i; cases i <;> rfl
  let right : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
    ⟨s.currySum (fun i => v (Sum.inl i)), by
      intro w i j hw hij
      exact hright (Sum.elim (fun i => v (Sum.inl i)) w) i j hij hw⟩
  let left : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
    ⟨((s.domDomCongr (Equiv.sumComm (Fin n) (Fin n))).currySum b), by
      intro w i j hw hij
      change ((s.domDomCongr (Equiv.sumComm (Fin n) (Fin n))).currySum b) w = 0
      simpa only [ContinuousMultilinearMap.currySum_apply,
        ContinuousMultilinearMap.domDomCongr_apply, hswap] using
        hleft (Sum.elim w b) i j hij hw⟩
  have hright' := complexAlternating_determinant right (fun i => v (Sum.inr i))
  have hleft' := complexAlternating_determinant left (fun i => v (Sum.inl i))
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i; cases i <;> rfl
  change s (Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))) =
    s (Sum.elim (fun i => v (Sum.inl i)) b) * Matrix.det (fun i => v (Sum.inr i)) at hright'
  simp only [left, ContinuousAlternatingMap.coe_mk,
    ContinuousMultilinearMap.currySum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    hswap] at hleft'
  rw [hv, hleft'] at hright'
  exact hright'.trans (mul_assoc _ _ _)

/-- Exact reconstruction of every concrete squared-canonical tensor from
its two-frame value in a given complex coframe. -/
theorem squaredCanonicalTensor_reconstruction {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : squaredCanonicalSubmodule J) (v : Fin n ⊕ Fin n → Model (2 * n)) :
    s.val v = s.val (fun i => C.symm (verticalFrame n (i.elim id id))) *
      coordinateSquaredVolumeValue (fun i => C (v i)) := by
  let e := C.trans (complexifyTangentCoordinatesEquiv n)
  let f := s.val.compContinuousLinearMap (fun _ => e.symm.toContinuousLinearMap)
  have hi (z : Fin n → ℂ) : e.symm (Complex.I • z) = J (e.symm z) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change Complex.I • z = complexifyTangentCoordinates n (C (J (e.symm z)))
    rw [hJ, complexify_coordinateComplexStructure]
    exact congrArg (fun a => Complex.I • a) (e.apply_symm_apply z).symm
  have hI : ∀ w i, f (Function.update w i (Complex.I • w i)) = Complex.I * f w := by
    intro w i
    have hu : (fun k => e.symm (Function.update w i (Complex.I • w i) k)) =
        Function.update (fun k => e.symm (w k)) i (J (e.symm (w i))) := by
      funext k
      by_cases hk : k = i
      · subst k; simp [hi]
      · simp [hk]
    change s.val (fun k => e.symm (Function.update w i (Complex.I • w i) k)) =
      Complex.I * s.val (fun k => e.symm (w k))
    rw [hu]
    exact s.property.2.2 _ _
  let g := complexMultilinearOfI f hI
  have hleft : ∀ w i j, i ≠ j → w (Sum.inl i) = w (Sum.inl j) → g w = 0 := by
    intro w i j hij hw
    exact s.property.1 _ i j hij (congrArg e.symm hw)
  have hright : ∀ w i j, i ≠ j → w (Sum.inr i) = w (Sum.inr j) → g w = 0 := by
    intro w i j hij hw
    exact s.property.2.1 _ i j hij (congrArg e.symm hw)
  have h := complexSquaredTensor_reconstruction g hleft hright (fun i => e (v i))
  have hb (i : Fin n) : e.symm ((Pi.basisFun ℂ (Fin n)) i) = C.symm (verticalFrame n i) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (Pi.basisFun ℂ (Fin n)) i = complexifyTangentCoordinates n (C (C.symm (verticalFrame n i)))
    rw [C.apply_symm_apply]
    ext j
    by_cases hij : i = j <;> simp [Pi.basisFun_apply, verticalFrame, hij]
  change s.val (fun i => e.symm (e (v i))) =
    s.val (fun i => e.symm (Sum.elim (Pi.basisFun ℂ (Fin n))
      (Pi.basisFun ℂ (Fin n)) i)) * _ at h
  simp only [e.symm_apply_apply] at h
  have hframe : (fun i => e.symm (Sum.elim (Pi.basisFun ℂ (Fin n))
      (Pi.basisFun ℂ (Fin n)) i)) =
      (fun i => C.symm (verticalFrame n (i.elim id id))) := by
    funext i; cases i <;> exact hb _
  rw [hframe] at h
  exact h

/-- The actual complex determinant form before real restriction. -/
def complexDeterminantForm (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  ⟨complexDeterminantTensor n,
    fun v _ _ hv hij => Matrix.detRowAlternating.map_eq_zero_of_eq v hv hij⟩

/-- The unsquared form `∧ (dq_j + i dθ_j)` in coordinate pairs. -/
def coordinateVolumeTensor (n : ℕ) : TangentCoordinates n [⋀^Fin n]→L[ℝ] ℂ :=
  ((complexDeterminantForm n).restrictScalars ℝ).compContinuousLinearMap
    (complexifyTangentCoordinates n)

@[simp] theorem coordinateVolumeTensor_apply {n : ℕ} (v : Fin n → TangentCoordinates n) :
    coordinateVolumeTensor n v = coordinateVolumeValue v := rfl

/-- The canonical generator defined by a genuine tangent coframe. -/
def coframeVolumeTensor {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n) : CanonicalTensor n :=
  (coordinateVolumeTensor n).compContinuousLinearMap C.toContinuousLinearMap

@[simp] theorem coframeVolumeTensor_apply {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n) (v : Fin n → Model (2 * n)) :
    coframeVolumeTensor C v = coordinateVolumeValue (fun i => C (v i)) := rfl

theorem coframeVolumeTensor_canonical {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    IsCanonicalTensor J (coframeVolumeTensor C) := by
  intro v i
  let w := fun k => complexifyTangentCoordinates n (C (v k))
  have hu : (fun k => complexifyTangentCoordinates n (C
      (Function.update v i (J (v i)) k))) = Function.update w i (Complex.I • w i) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Function.update_self, hJ, complexify_coordinateComplexStructure]
      rfl
    · simp only [Function.update_of_ne hk]
      rfl
  change complexDeterminantTensor n
    (fun k => complexifyTangentCoordinates n (C (Function.update v i (J (v i)) k))) =
      Complex.I * complexDeterminantTensor n w
  rw [hu, ContinuousMultilinearMap.map_update_smul, Function.update_eq_self]
  rfl

def coframeCanonicalVector {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) : canonicalSubmodule J :=
  ⟨coframeVolumeTensor C, coframeVolumeTensor_canonical C J hJ⟩

def coframeSquaredCanonicalVector {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    squaredCanonicalSubmodule J :=
  ⟨(coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C.toContinuousLinearMap),
    isSquaredCanonicalTensor_coordinateSquaredVolumeTensor C.toContinuousLinearMap J hJ⟩

/-- Every canonical fiber with the displayed complex coframe is a complex
line. The equivalence evaluates on the ordered frame and reconstructs by
the determinant generator. -/
def canonicalFiberCoordinateEquiv {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    canonicalSubmodule J ≃ₗ[ℂ] ℂ where
  toFun := fun s => s.val (fun i => C.symm (verticalFrame n i))
  invFun := fun c => c • coframeCanonicalVector C J hJ
  left_inv := by
    intro s
    apply Subtype.ext
    ext v
    simpa [coframeCanonicalVector, smul_eq_mul] using
      (canonicalTensor_reconstruction C J hJ s v).symm
  right_inv := by
    intro c
    simp [coframeCanonicalVector, coframeVolumeTensor_apply, coordinateVolumeValue_verticalFrame]
  map_add' := by intro s t; simp
  map_smul' := by intro c s; simp

/-- The concrete squared-canonical fiber is also a complex line, with the
two-frame evaluation as its coordinate. -/
def squaredCanonicalFiberCoordinateEquiv {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    squaredCanonicalSubmodule J ≃ₗ[ℂ] ℂ where
  toFun := fun s => s.val (fun i => C.symm (verticalFrame n (i.elim id id)))
  invFun := fun c => c • coframeSquaredCanonicalVector C J hJ
  left_inv := by
    intro s
    apply Subtype.ext
    ext v
    simpa [coframeSquaredCanonicalVector, smul_eq_mul] using
      (squaredCanonicalTensor_reconstruction C J hJ s v).symm
  right_inv := by
    intro c
    simp [coframeSquaredCanonicalVector, coordinateSquaredVolumeTensor_apply,
      coordinateSquaredVolumeValue_verticalFrame]
  map_add' := by intro s t; simp
  map_smul' := by intro c s; simp

/-- The actual tensor square of the canonical line is equivalent to the
concrete two-block tensor fiber. -/
def canonicalSquareEquiv {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    TensorProduct ℂ (canonicalSubmodule J) (canonicalSubmodule J) ≃ₗ[ℂ]
      squaredCanonicalSubmodule J :=
  ((TensorProduct.congr (canonicalFiberCoordinateEquiv C J hJ)
      (canonicalFiberCoordinateEquiv C J hJ)).trans (TensorProduct.lid ℂ ℂ)).trans
    (squaredCanonicalFiberCoordinateEquiv C J hJ).symm

/-- The equivalence is precisely the natural multiplication map on tensors,
so it agrees with the original concrete Maslov representation. -/
theorem canonicalSquareEquiv_toLinearMap {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    (canonicalSquareEquiv C J hJ).toLinearMap = canonicalSquareMap J := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro t
  apply (squaredCanonicalFiberCoordinateEquiv C J hJ).injective
  change (squaredCanonicalFiberCoordinateEquiv C J hJ)
      (canonicalSquareEquiv C J hJ (s ⊗ₜ[ℂ] t)) =
    (squaredCanonicalFiberCoordinateEquiv C J hJ) (canonicalSquareMap J (s ⊗ₜ[ℂ] t))
  simp only [canonicalSquareEquiv,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply]
  change s.val (fun i => C.symm (verticalFrame n i)) *
      t.val (fun i => C.symm (verticalFrame n i)) =
    (canonicalSquareMap J (s ⊗ₜ[ℂ] t)).val (fun i => C.symm (verticalFrame n (i.elim id id)))
  rw [canonicalSquareMap_tmul]
  simp [canonicalTensorProduct_apply]

/-- Rank one is a proved property of the concrete canonical fiber in this coframe. -/
theorem canonicalFiber_finrank {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    Module.finrank ℂ (canonicalSubmodule J) = 1 := by
  rw [(canonicalFiberCoordinateEquiv C J hJ).finrank_eq]
  exact Module.finrank_self ℂ

theorem squaredCanonicalFiber_finrank {n : ℕ}
    (C : Model (2 * n) ≃L[ℝ] TangentCoordinates n)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (hJ : ∀ v, C (J v) = coordinateComplexStructure n (C v)) :
    Module.finrank ℂ (squaredCanonicalSubmodule J) = 1 := by
  rw [(squaredCanonicalFiberCoordinateEquiv C J hJ).finrank_eq]
  exact Module.finrank_self ℂ

set_option backward.isDefEq.respectTransparency false in
/-- At every actual logarithmic tangent fiber the source canonical line and
its genuine tensor square agree with the concrete Maslov fibers. -/
def logarithmicCanonicalSquareEquiv {n : ℕ} (y : (lgManifold n).Point) :
    TensorProduct ℂ (canonicalSubmodule (logarithmicAlmostComplexField n y))
      (canonicalSubmodule (logarithmicAlmostComplexField n y)) ≃ₗ[ℂ]
      squaredCanonicalSubmodule (logarithmicAlmostComplexField n y) :=
  canonicalSquareEquiv (lgTangentCoframeEquiv y) (logarithmicAlmostComplexField n y)
    (lgTangentCoframe_almostComplex y)

set_option backward.isDefEq.respectTransparency false in
def cotangentCanonicalSquareEquiv {n : ℕ} (y : (cotangentManifold n).Point) :
    TensorProduct ℂ (canonicalSubmodule (cotangentAlmostComplexField n y))
      (canonicalSubmodule (cotangentAlmostComplexField n y)) ≃ₗ[ℂ]
      squaredCanonicalSubmodule (cotangentAlmostComplexField n y) :=
  canonicalSquareEquiv (cotangentTangentCoframeEquiv y) (cotangentAlmostComplexField n y)
    (cotangentTangentCoframe_almostComplex y)

set_option backward.isDefEq.respectTransparency false in
/-- The existing prescribed source tensor is the image of the genuine square
of its canonical determinant generator. -/
theorem logarithmicSquaredVolumeTensor_tensorSquare {n : ℕ} (y : (lgManifold n).Point) :
    logarithmicSquaredVolumeTensor n y =
      (logarithmicCanonicalSquareEquiv y
        (coframeCanonicalVector (lgTangentCoframeEquiv y) (logarithmicAlmostComplexField n y)
          (lgTangentCoframe_almostComplex y) ⊗ₜ[ℂ]
        coframeCanonicalVector (lgTangentCoframeEquiv y) (logarithmicAlmostComplexField n y)
          (lgTangentCoframe_almostComplex y))).val := by
  change logarithmicSquaredVolumeTensor n y =
    ((canonicalSquareEquiv (lgTangentCoframeEquiv y) (logarithmicAlmostComplexField n y)
      (lgTangentCoframe_almostComplex y)).toLinearMap _).val
  rw [canonicalSquareEquiv_toLinearMap, canonicalSquareMap_tmul]
  ext v
  simp [logarithmicSquaredVolumeTensor, canonicalTensorProduct_apply,
    coframeCanonicalVector, coordinateSquaredVolumeValue]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cotangent prescribed square likewise comes from the canonical line;
the generator evaluates to one on the ordered vertical frame. -/
theorem cotangentSquaredVolumeTensor_tensorSquare {n : ℕ} (y : (cotangentManifold n).Point) :
    cotangentSquaredVolumeTensor n y =
      (cotangentCanonicalSquareEquiv y
        (coframeCanonicalVector (cotangentTangentCoframeEquiv y) (cotangentAlmostComplexField n y)
          (cotangentTangentCoframe_almostComplex y) ⊗ₜ[ℂ]
        coframeCanonicalVector (cotangentTangentCoframeEquiv y) (cotangentAlmostComplexField n y)
          (cotangentTangentCoframe_almostComplex y))).val := by
  change cotangentSquaredVolumeTensor n y =
    ((canonicalSquareEquiv (cotangentTangentCoframeEquiv y) (cotangentAlmostComplexField n y)
      (cotangentTangentCoframe_almostComplex y)).toLinearMap _).val
  rw [canonicalSquareEquiv_toLinearMap, canonicalSquareMap_tmul]
  ext v
  simp [cotangentSquaredVolumeTensor, canonicalTensorProduct_apply,
    coframeCanonicalVector, coordinateSquaredVolumeValue]
  rfl

end FsFltz.Geometry
