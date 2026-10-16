import FsFltz.Geometry.OriginalRetainedCanonicalSection
import FsFltz.Geometry.OriginalBundleMaslovSectionRecovery
import FsFltz.Geometry.OriginalBundleFiniteRealization

/-!
# Original Maslov realizations from arbitrary retained native bundle sections

Source: `geoemtric-part-fsf.tex`, smooth extension (119–122),
`def:maslov` (212–232), `def:chain` (163–199), and `sec:lean` (788–814).
The compatible field is prescribed first. Its independently constructed
retained canonical-square bundle carries an arbitrary nowhere-zero section.
The full tensors and original Maslov data are constructed by natural square
multiplication; the only section overlap law is its defining geometric
covariance. Ordinary local-map extensions in the actual restricted bundle
coordinates produce the coframes consumed by both full realizations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct Classical
open Set Filter Topology Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

namespace CompletedMaslovDimension

/-- Reindex a native full tensor, without selecting or extending it. -/
def tensorFromNative {d n : ℕ} (h : d = 2 * n) (X : CompleteLiouvilleManifold d)
    (T : X.manifold.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ) :
    (ambient h X).manifold.Point → SquaredCanonicalTensor n := by
  subst d
  exact T

theorem nativeTensor_tensorFromNative {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d)
    (T : X.manifold.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ) :
    nativeTensor h X (tensorFromNative h X T) = T := by
  subst d
  rfl

theorem tensorFromNative_canonical {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d) (J : AlmostComplexField (ambient h X).manifold)
    (T : X.manifold.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ)
    (hT : ∀ x, IsSquaredCanonicalTensor
      ((modelEquiv h).symm.toContinuousLinearMap.comp
        ((nativeField h X J x).comp (modelEquiv h).toContinuousLinearMap))
      ((T x).compContinuousLinearMap (fun _ => (modelEquiv h).toContinuousLinearMap))) :
    ∀ x, IsSquaredCanonicalTensor (J x) (tensorFromNative h X T x) := by
  subst d
  intro x
  convert hT x using 1 <;> ext v <;> rfl

theorem tensorFromNative_neZero {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d)
    (T : X.manifold.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ) (hT : ∀ x, T x ≠ 0) :
    ∀ x, tensorFromNative h X T x ≠ 0 := by
  subst d
  exact hT

end CompletedMaslovDimension

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

/-- Compatible complex structures on the canonical collar-generated source,
with their defining overlap law; no section or encoded grading is selected. -/
structure OriginalRetainedMaslovComplexData
    (P : BundlePrimitiveData (k := k) (M := M) E)
    (L : OriginalBundleLiouvilleLaws P) (hdim : k + 1 = 2 * n) where
  J : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter),
    s ∈ (L.localCompletionFamily c t ht).base →
      AlmostComplexField (localMaslovAmbient hdim L c t ht s).manifold
  compatible : ∀ c t ht s hs,
    IsCompatibleAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold
      ((localMaslovAmbient hdim L c t ht s).manifold.exteriorDerivative
        (localMaslovAmbient hdim L c t ht s).primitive) (J c t ht s hs)
  covarianceJ : ∀ c d t u ht hu s hs hs',
    J c t ht s hs = pullbackAlmostComplex
      (localMaslovAmbient hdim L c t ht s).manifold
      (localMaslovAmbient hdim L d u hu s).manifold
      (localMaslovOverlap hdim L c d t u ht hu s hs hs') (J d u hu s hs')

namespace OriginalRetainedMaslovComplexData

variable (D : OriginalRetainedMaslovComplexData P L hdim)

def nativeJ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :=
  CompletedMaslovDimension.nativeField hdim
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient (D.J c t ht s hs)

def retainedNativeJ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    Model (k + 1) →L[ℝ] Model (k + 1) :=
  if hs : s ∈ (L.localCompletionFamily c t ht).base then D.nativeJ c t ht s hs x else 0

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem retainedNativeJ_eq
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    D.retainedNativeJ c t ht s x = D.nativeJ c t ht s hs x := by
  simp only [retainedNativeJ, dite_eq_left hs]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem nativeJ_sq (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) (v : Model (k + 1)) :
    D.nativeJ c t ht s hs x (D.nativeJ c t ht s hs x v) = -v :=
  CompletedMaslovDimension.nativeField_sq hdim _ _ (D.compatible c t ht s hs).2.1 x v

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem retainedNativeJ_sq (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) (v : Model (k + 1)) :
    D.retainedNativeJ c t ht s x (D.retainedNativeJ c t ht s x v) = -v := by
  rw [D.retainedNativeJ_eq c t ht s hs x]
  exact D.nativeJ_sq c t ht s hs x v

end OriginalRetainedMaslovComplexData

/-- Raw smooth-extension regularity for the independently prescribed J. -/
structure OriginalRetainedMaslovComplexRegularity
    (D : OriginalRetainedMaslovComplexData P L hdim) : Prop where
  interior : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalInteriorComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero (D.retainedNativeJ c t ht) F.base
  cylinder : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalEndComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero (D.retainedNativeJ c t ht) F.base

/-- Arbitrary sections in the actual retained canonical-square fibers. -/
abbrev OriginalRetainedMaslovSections (D : OriginalRetainedMaslovComplexData P L hdim) :=
  ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    OriginalRetainedCanonicalSection F.native.collar (D.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) F.base F.base_open

def originalRetainedMaslovNativeSection (D : OriginalRetainedMaslovComplexData P L hdim)
    (σ : OriginalRetainedMaslovSections D)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :=
  let F := L.localCompletionFamily c t ht
  originalRetainedSectionNative F.native.collar (D.retainedNativeJ c t ht)
    (interiorMaslovModelEquiv hdim) F.base F.base_open (σ c t ht)

/-- The complete original tensor is produced by the section's natural
square multiplication. No independently supplied tensor occurs. -/
def originalRetainedMaslovTensor (D : OriginalRetainedMaslovComplexData P L hdim)
    (σ : OriginalRetainedMaslovSections D)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (localMaslovAmbient hdim L c t ht s).manifold.Point → SquaredCanonicalTensor n :=
  let F := L.localCompletionFamily c t ht
  CompletedMaslovDimension.tensorFromNative hdim (F.sliceCompletion L s).ambient
    (originalNativeSectionTensor F.native.collar (D.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) (originalRetainedMaslovNativeSection D σ c t ht) s)

/-- One prescribed section on the completed family: nonvanishing, actual
overlap covariance, and ordinary smooth extensions in the retained bundle's
constructed coordinates. These are defining source laws, not output germs. -/
structure OriginalRetainedMaslovSection (D : OriginalRetainedMaslovComplexData P L hdim) where
  sectionValue : OriginalRetainedMaslovSections D
  nowhereZero : ∀ c t ht x, sectionValue c t ht x ≠ 0
  covarianceSection : ∀ c d t u ht hu s hs hs',
    originalRetainedMaslovTensor D sectionValue c t ht s hs = pullbackSquaredTensor
      (localMaslovAmbient hdim L c t ht s).manifold
      (localMaslovAmbient hdim L d u hu s).manifold
      (localMaslovOverlap hdim L c d t u ht hu s hs hs')
      (originalRetainedMaslovTensor D sectionValue d u hu s hs')
  smooth : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalRetainedLocalMapExtensions F.native.collar (D.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) F.base F.base_open F.native.width_pos F.native.embedding
      F.native.boundary F.native.zero F.native.joint F.native.smooth F.native.inverse
      (originalRetainedSectionGraph F.native.collar (D.retainedNativeJ c t ht)
        (interiorMaslovModelEquiv hdim) F.base F.base_open (sectionValue c t ht))

namespace OriginalRetainedMaslovSection

variable {D : OriginalRetainedMaslovComplexData P L hdim} (σ : OriginalRetainedMaslovSection D)

/-- Construct all original full tensors from the arbitrary bundle section. -/
def toOriginalMaslovData : OriginalLocalCompletionMaslovData P L hdim where
  J := D.J
  tensor := originalRetainedMaslovTensor D σ.sectionValue
  compatible := D.compatible
  canonical := by
    intro c t ht s hs
    apply CompletedMaslovDimension.tensorFromNative_canonical
    intro x
    simpa only [D.retainedNativeJ_eq c t ht s hs x,
      OriginalRetainedMaslovComplexData.nativeJ, interiorMaslovModelEquiv] using
      originalNativeSectionTensor_canonical (L.localCompletionFamily c t ht).native.collar
        (D.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim)
        (originalRetainedMaslovNativeSection D σ.sectionValue c t ht) s x
  nowhereZero := by
    intro c t ht s hs
    apply CompletedMaslovDimension.tensorFromNative_neZero
    intro x
    apply originalNativeSectionTensor_neZero
      (L.localCompletionFamily c t ht).native.collar (D.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) (originalRetainedMaslovNativeSection D σ.sectionValue c t ht) s x
    · exact D.retainedNativeJ_sq c t ht s hs x
    · exact originalRetainedSectionNative_neZero (L.localCompletionFamily c t ht).native.collar
        (D.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim)
        (L.localCompletionFamily c t ht).base (L.localCompletionFamily c t ht).base_open
        (σ.sectionValue c t ht) (σ.nowhereZero c t ht) s hs x
  covarianceJ := D.covarianceJ
  covarianceTensor := σ.covarianceSection

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The reconstructed source has precisely the original prescribed field. -/
theorem retainedNativeJ_toOriginalMaslovData
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    σ.toOriginalMaslovData.retainedNativeJ c t ht = D.retainedNativeJ c t ht := rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Full tensor identification, before any encoded deformation is selected. -/
theorem nativeTensor_toOriginalMaslovData
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    σ.toOriginalMaslovData.nativeTensor c t ht s hs =
      originalNativeSectionTensor (L.localCompletionFamily c t ht).native.collar
        (D.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim)
        (originalRetainedMaslovNativeSection D σ.sectionValue c t ht) s :=
  CompletedMaslovDimension.nativeTensor_tensorFromNative hdim _ _

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The produced native tensor recovers every slot of natural canonical
square multiplication of the arbitrary section, not merely its coefficient. -/
theorem normalizedTensor_toOriginalMaslovData
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    (σ.toOriginalMaslovData.nativeTensor c t ht s hs x).compContinuousLinearMap
      (fun _ => (interiorMaslovModelEquiv hdim).toContinuousLinearMap) =
    (canonicalSquareMap _ (originalRetainedMaslovNativeSection D σ.sectionValue c t ht s x)).val := by
  rw [σ.nativeTensor_toOriginalMaslovData]
  exact originalNativeSectionTensor_normalized _ _ _ _ _ _

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The canonical section reconstructed from S is exactly the originally
selected arbitrary bundle section through the actual slice restriction. -/
theorem retainedNativeSection_toOriginalMaslovData
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    σ.toOriginalMaslovData.retainedNativeSection c t ht =
      originalRetainedMaslovNativeSection D σ.sectionValue c t ht := by
  funext s x
  let F := L.localCompletionFamily c t ht
  let N := interiorMaslovModelEquiv hdim
  by_cases hs : s ∈ F.base
  · have hsq : ∀ v, (N.symm.toContinuousLinearMap.comp
        ((D.retainedNativeJ c t ht s x).comp N.toContinuousLinearMap))
        ((N.symm.toContinuousLinearMap.comp
          ((D.retainedNativeJ c t ht s x).comp N.toContinuousLinearMap)) v) = -v := by
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      rw [D.retainedNativeJ_sq c t ht s hs x, map_neg, ContinuousLinearEquiv.symm_apply_apply]
    apply (canonicalSquareMap_bijective _ hsq).1
    apply Subtype.ext
    have h := σ.toOriginalMaslovData.retainedNativeSection_tensor c t ht s hs x
    rw [σ.nativeTensor_toOriginalMaslovData] at h
    have he := congrArg (fun T => T.compContinuousLinearMap
      (fun _ => N.toContinuousLinearMap)) h
    change (originalNativeSectionTensor F.native.collar (D.retainedNativeJ c t ht) N
      (σ.toOriginalMaslovData.retainedNativeSection c t ht) s x).compContinuousLinearMap
      (fun _ => N.toContinuousLinearMap) =
      (originalNativeSectionTensor F.native.collar (D.retainedNativeJ c t ht) N
        (originalRetainedMaslovNativeSection D σ.sectionValue c t ht) s x).compContinuousLinearMap
        (fun _ => N.toContinuousLinearMap) at he
    simpa only [originalNativeSectionTensor_normalized] using he
  · change s ∉ (L.localCompletionFamily c t ht).base at hs
    simp only [OriginalLocalCompletionMaslovData.retainedNativeSection,
      originalRetainedMaslovNativeSection, originalRetainedSectionNative, dite_eq_right hs]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The recovered total graph is literally the arbitrary section's graph
on every retained point of the actual completed family. -/
theorem totalSection_toOriginalMaslovData
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (x : originalRetainedCanonicalBase (L.localCompletionFamily c t ht).native.collar
      (L.localCompletionFamily c t ht).base (L.localCompletionFamily c t ht).base_open) :
    originalTotalSection (L.localCompletionFamily c t ht).native.collar
      (D.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim)
      (σ.toOriginalMaslovData.retainedNativeSection c t ht) x.val = σ.sectionValue c t ht x := by
  rw [σ.retainedNativeSection_toOriginalMaslovData]
  rw [originalRetainedMaslovNativeSection, originalTotalSection_retainedNative]
  exact originalRetainedSectionTotal_on _ _ _ _ _ _ x

/-- Source J extensions and generic smoothness of the arbitrary section
produce all coframe/scalar germs for the exact recovered original tensors. -/
theorem coframeGerms (hD : OriginalRetainedMaslovComplexRegularity D) :
    OriginalLocalCompletionMaslovCoframeGerms σ.toOriginalMaslovData := by
  apply σ.toOriginalMaslovData.coframeGerms_of_retainedSectionMapExtensions
  · exact hD.interior
  · exact hD.cylinder
  · intro c t ht
    rw [σ.retainedNativeSection_toOriginalMaslovData]
    exact originalRetainedSectionNative_localMapExtensions
      (L.localCompletionFamily c t ht).native.collar (D.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) (L.localCompletionFamily c t ht).base
      (L.localCompletionFamily c t ht).base_open (L.localCompletionFamily c t ht).native.width_pos
      (L.localCompletionFamily c t ht).native.embedding (L.localCompletionFamily c t ht).native.boundary
      (L.localCompletionFamily c t ht).native.zero (L.localCompletionFamily c t ht).native.joint
      (L.localCompletionFamily c t ht).native.smooth (L.localCompletionFamily c t ht).native.inverse
      (σ.sectionValue c t ht) (σ.smooth c t ht)

end OriginalRetainedMaslovSection
end FsFltz.Geometry.IntrinsicSmoothBundle
