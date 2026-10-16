import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalMapExtensionOn
import FsFltz.Geometry.OriginalBundleMaslovSectionPullback
import FsFltz.Geometry.OriginalBundleMaslovSourceGerms
import FsFltz.Geometry.OriginalRetainedCanonicalChart

/-!
# Recovering the prescribed section on retained original local completions

Source: `geoemtric-part-fsf.tex`, smooth extension (119–122),
`def:maslov` (212–244), and `sec:lean` (788–814). Native canonical-square
sections are obtained from the exact full tensors of the original data.
Values outside a local completion's retained base are used only to type total
functions; no regularity, compatibility, or nonvanishing is required there.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct Classical
open Set Filter Topology Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- Cancel the fixed tangent normalization and the original invertible
chart differential in the full canonical-square reconstruction. -/
theorem nativeTensor_reconstruction_of_normalizedInverseCoordinates
    {n : ℕ} {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : Model (2 * n) ≃L[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => V) ℂ)
    (D : V →L[ℝ] F) (hD : D.IsInvertible)
    (C : F →L[ℝ] TangentCoordinates n) (a : ℂ)
    (hT : a • coframeSquaredGenerator (C.comp N.toContinuousLinearMap) =
      (T.compContinuousLinearMap (fun _ => D.inverse)).compContinuousLinearMap
        (fun _ => N.toContinuousLinearMap)) :
    T = a • (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C.comp D) := by
  apply nativeTensor_reconstruction_of_inverseCoordinates T D hD C a
  ext v
  have hv := congrArg (fun S => S (fun i => N.symm (v i))) hT
  simpa only [coframeSquaredGenerator, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hv.symm

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

local instance retainedSectionProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)

/-- The original native field on the retained base; the zero value elsewhere
is merely a total-function convention and is never required to be complex. -/
def retainedNativeJ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    Model (k + 1) →L[ℝ] Model (k + 1) :=
  if hs : s ∈ (L.localCompletionFamily c t ht).base then S.nativeJ c t ht s hs x else 0

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp]
theorem retainedNativeJ_eq (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    S.retainedNativeJ c t ht s x = S.nativeJ c t ht s hs x := by
  simp only [retainedNativeJ, dite_eq_left hs]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Only the retained field is required to satisfy the complex equation. -/
theorem retainedNativeJ_sq (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) (v : Model (k + 1)) :
    S.retainedNativeJ c t ht s x (S.retainedNativeJ c t ht s x v) = -v := by
  rw [S.retainedNativeJ_eq c t ht s hs x]
  exact S.nativeJ_sq c t ht s hs x v

/-- The exact canonical-square section of the original full tensor. It is
zero off the retained base, without any smoothness assertion at that cutoff. -/
def retainedNativeSection (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    OriginalNativeCanonicalSection (L.localCompletionFamily c t ht).native.collar
      (S.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim) := by
  intro s x
  by_cases hs : s ∈ (L.localCompletionFamily c t ht).base
  · let N := interiorMaslovModelEquiv hdim
    let J := N.symm.toContinuousLinearMap.comp
      ((S.retainedNativeJ c t ht s x).comp N.toContinuousLinearMap)
    have hsq : ∀ v, J (J v) = -v := by
      intro v
      simp only [J, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
      rw [S.retainedNativeJ_sq c t ht s hs x, map_neg, ContinuousLinearEquiv.symm_apply_apply]
    have hcan : IsSquaredCanonicalTensor J
        ((S.nativeTensor c t ht s hs x).compContinuousLinearMap (fun _ => N.toContinuousLinearMap)) := by
      simpa only [J, S.retainedNativeJ_eq c t ht s hs x] using
        S.nativeTensor_canonical c t ht s hs x
    exact (canonicalSquareEquivOfComplexStructure J hsq).symm ⟨_, hcan⟩
  · exact 0

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Natural square multiplication recovers every slot of the original
tensor at every retained parameter and on the entire original completion. -/
theorem retainedNativeSection_tensor (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : Space ((L.localCompletionFamily c t ht).native.patches s)) :
    originalNativeSectionTensor (L.localCompletionFamily c t ht).native.collar
      (S.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim)
      (S.retainedNativeSection c t ht) s x = S.nativeTensor c t ht s hs x := by
  simp only [originalNativeSectionTensor, retainedNativeSection, dite_eq_left hs]
  let N := interiorMaslovModelEquiv hdim
  let J := N.symm.toContinuousLinearMap.comp
    ((S.retainedNativeJ c t ht s x).comp N.toContinuousLinearMap)
  have hsq : ∀ v, J (J v) = -v := by
    intro v
    simp only [J, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [S.retainedNativeJ_sq c t ht s hs x, map_neg, ContinuousLinearEquiv.symm_apply_apply]
  have hcan : IsSquaredCanonicalTensor J
      ((S.nativeTensor c t ht s hs x).compContinuousLinearMap (fun _ => N.toContinuousLinearMap)) := by
    simpa only [J, S.retainedNativeJ_eq c t ht s hs x] using
      S.nativeTensor_canonical c t ht s hs x
  have h := (canonicalSquareEquivOfComplexStructure J hsq).apply_symm_apply
    ⟨(S.nativeTensor c t ht s hs x).compContinuousLinearMap (fun _ => N.toContinuousLinearMap), hcan⟩
  have he := congrArg Subtype.val h
  change (canonicalSquareMap J ((canonicalSquareEquivOfComplexStructure J hsq).symm
    ⟨(S.nativeTensor c t ht s hs x).compContinuousLinearMap (fun _ => N.toContinuousLinearMap), hcan⟩)).val =
      (S.nativeTensor c t ht s hs x).compContinuousLinearMap (fun _ => N.toContinuousLinearMap) at he
  ext v
  have hv := congrArg (fun T => T (fun i => N.symm (v i))) he
  simpa only [J, N, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using hv

variable
  (hJI : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalInteriorComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht) F.base)
  (hJE : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalEndComplexExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht) F.base)
  (hmap : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasOriginalTotalLocalMapExtensionsOn F.native.width_pos F.native.collar
      F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) F.native.joint F.native.smooth F.native.inverse
      {x | parameter F.native.patches x ∈ F.base}
      (originalTotalSectionGraph F.native.collar (S.retainedNativeJ c t ht)
        (interiorMaslovModelEquiv hdim) (S.retainedNativeSection c t ht)))

include hJI hJE hmap in
/-- The actual section of the prescribed original full tensors supplies
every original local coframe/scalar germ. Real-open field regularity and
arbitrary-map regularity of this exact graph are required only on each
retained base. No coefficient, coframe or desired grading germ is assumed. -/
theorem coframeGerms_of_retainedSectionMapExtensions :
    OriginalLocalCompletionMaslovCoframeGerms S := by
  constructor
  · intro c t ht s hs u w hw
    let F := L.localCompletionFamily c t ht
    obtain ⟨U₀, K, hpU₀, hK, heK⟩ := hJI c t ht s hs u w hw
    obtain ⟨d, hdu, hpd, _⟩ := exists_originalInteriorCanonicalChart_on F.native.width_pos
      F.native.collar F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht)
      F.native.smooth F.native.inverse F.base F.base_open
      (fun v hv x ξ => S.retainedNativeJ_sq c t ht v hv x ξ)
      (interiorMaslovModelEquiv hdim) u s hs w hw U₀ K hpU₀ hK heK
    subst u
    have hchart := originalTotalChartMapExtensionsOn_of_localMapExtensionsOn F.native.width_pos
      F.native.collar F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) F.native.joint F.native.smooth F.native.inverse F.native.mixed
      (endMaslovModelEquiv hdim) _ _ continuous_id (hmap c t ht)
    obtain ⟨U, q, hpU, hUd, hq, heq⟩ := originalInteriorCoefficientExtensionOn_of_chartMapExtensionsOn
      F.native.width_pos F.native.collar F.native.embedding F.native.boundary F.native.zero
      (S.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim) F.native.joint F.native.smooth
      F.native.inverse F.base (S.retainedNativeSection c t ht) hchart d (s, w) hpd hs
    refine ⟨U, U.isOpen, hpU, d.coframe, d.smooth_coframe.mono hUd,
      (fun z hz => d.invertible_coframe z (hUd hz)), q, hq, ?_⟩
    intro v hv z hz hVz
    have hi := F.isInvertible_interiorMaslovCoordinateDifferential v d.anchor z hz
    have hJ := d.intertwines v z hz (hUd hVz)
    have hJ' : ∀ ξ, d.coframe (v.val, chartAt (Model (k + 1)) d.anchor z)
        ((F.interiorMaslovCoordinateDifferential v d.anchor z).comp
          ((S.nativeJ c t ht v hv (interiorIn (F.native.patches v) z)).comp
            (F.interiorMaslovCoordinateDifferential v d.anchor z).inverse) ξ) =
        coordinateComplexStructure n (d.coframe (v.val, chartAt (Model (k + 1)) d.anchor z) ξ) := by
      simpa only [originalInteriorComplexInChart, S.retainedNativeJ_eq c t ht v hv,
        originalInteriorCanonicalDifferential, originalInteriorChartDifferential,
        LocalCompletionFamily.interiorMaslovCoordinateDifferential] using hJ
    constructor
    · exact coframe_intertwines_nativeConjugation _ _ hi _ hJ'
    · have hzbase : (v, z) ∈ d.baseDomain := ⟨⟨mem_univ _, hz⟩, hUd hVz⟩
      have hT := d.coordinate_reconstruction (interiorMaslovModelEquiv hdim)
        F.native.smooth F.native.inverse (S.retainedNativeSection c t ht) v z hzbase
        (q (v.val, chartAt (Model (k + 1)) d.anchor z)) (heq v hv z hz hVz)
      rw [S.retainedNativeSection_tensor c t ht v hv] at hT
      exact nativeTensor_reconstruction_of_normalizedInverseCoordinates
        (interiorMaslovModelEquiv hdim) _ _ hi _ _ hT
  · intro c t ht s hs u w hw
    let F := L.localCompletionFamily c t ht
    obtain ⟨U₀, K, hpU₀, hK, heK⟩ := hJE c t ht s hs u w hw
    obtain ⟨d, hdu, hpd, _⟩ := exists_originalEndCanonicalChart_on F.native.width_pos
      F.native.collar F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht)
      F.native.smooth F.native.inverse F.base F.base_open
      (fun v hv x ξ => S.retainedNativeJ_sq c t ht v hv x ξ)
      (endMaslovModelEquiv hdim) u s hs w hw U₀ K hpU₀ hK heK
    subst u
    have hchart := originalTotalChartMapExtensionsOn_of_localMapExtensionsOn F.native.width_pos
      F.native.collar F.native.embedding F.native.boundary F.native.zero (S.retainedNativeJ c t ht)
      (interiorMaslovModelEquiv hdim) F.native.joint F.native.smooth F.native.inverse F.native.mixed
      (endMaslovModelEquiv hdim) _ _ continuous_id (hmap c t ht)
    obtain ⟨U, q, hpU, hUd, hq, heq⟩ := originalEndCoefficientExtensionOn_of_chartMapExtensionsOn
      F.native.width_pos F.native.collar F.native.embedding F.native.boundary F.native.zero
      (S.retainedNativeJ c t ht) (interiorMaslovModelEquiv hdim) F.native.joint F.native.smooth
      F.native.inverse F.base (S.retainedNativeSection c t ht) hchart d (s, w) hpd hs
    refine ⟨U, U.isOpen, hpU, d.coframe, d.smooth_coframe.mono hUd,
      (fun z hz => d.invertible_coframe z (hUd hz)), q, hq, ?_⟩
    intro v hv z hz hVz
    have hi := F.isInvertible_endMaslovCoordinateDifferential v d.anchor z hz
    have hJ := d.intertwines v z hz (hUd hVz)
    have hJ' : ∀ ξ, d.coframe (v.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates z))
        ((F.endMaslovCoordinateDifferential v d.anchor z).comp
          ((S.nativeJ c t ht v hv (cylinder (F.native.patches v) z)).comp
            (F.endMaslovCoordinateDifferential v d.anchor z).inverse) ξ) =
        coordinateComplexStructure n
          (d.coframe (v.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates z)) ξ) := by
      simpa only [originalEndComplexInChart, S.retainedNativeJ_eq c t ht v hv,
        originalEndCanonicalDifferential, originalEndChartDifferential,
        LocalCompletionFamily.endMaslovCoordinateDifferential] using hJ
    constructor
    · exact coframe_intertwines_nativeConjugation _ _ hi _ hJ'
    · have hzbase : (v, z) ∈ d.baseDomain := ⟨⟨mem_univ _, hz⟩, hUd hVz⟩
      have hT := d.coordinate_reconstruction (interiorMaslovModelEquiv hdim)
        (endMaslovModelEquiv hdim) F.native.smooth F.native.inverse
        (S.retainedNativeSection c t ht) v z hzbase
        (q (v.val, chartAt (Model k × ℝ) d.anchor (endBandCoordinates z))) (heq v hv z hz hVz)
      rw [S.retainedNativeSection_tensor c t ht v hv] at hT
      exact nativeTensor_reconstruction_of_normalizedInverseCoordinates
        (endMaslovModelEquiv hdim) _ _ hi _ _ hT

end OriginalLocalCompletionMaslovData
end FsFltz.Geometry.IntrinsicSmoothBundle
