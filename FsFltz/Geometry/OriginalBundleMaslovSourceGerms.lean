import FsFltz.Geometry.OriginalBundleMaslovFamily
import FsFltz.Geometry.NativeCoordinateCanonicalSection

/-!
# Coframe germs produced from original source chart extensions

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The inputs are real-open extensions of the
original chart-conjugated complex fields and full pulled tensors. The
coframes and scalar coefficients needed by the completed-family consumer
are constructed. Original field laws are used only at retained parameters.

The real-open extensions are explicit conditional inputs. Constructing
them from an arbitrary section on the whole original completed bundle
remains a separate foundation. This file proves no toric chain, endpoint
grading homotopy, or categorical comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- Real-open field and full tensor extensions produce both the coframe
and its scalar; complex and canonical laws are confined to the source locus. -/
theorem exists_coordinateCoframeScalar_of_tensorExtensions {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : Model (2 * n) ≃L[ℝ] F)
    {U A : Set E} {p : E} (hU : IsOpen U) (hpU : p ∈ U) (hpA : p ∈ A)
    (K : E → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K U)
    (hsq : ∀ z ∈ U ∩ A, ∀ v, K z (K z v) = -v)
    (T : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ)
    (hT : ContDiffOn ℝ ∞ T U)
    (hcan : ∀ z ∈ U ∩ A, IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp ((K z).comp P.toContinuousLinearMap))
      ((T z).compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) :
    ∃ V ⊆ U, IsOpen V ∧ p ∈ V ∧
      ∃ C : E → F →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ C V ∧ (∀ z ∈ V, (C z).IsInvertible) ∧
        ∃ a : E → ℂ, ContDiffOn ℝ ∞ a V ∧
          ∀ z ∈ V ∩ A,
            (∀ v, C z (K z v) = coordinateComplexStructure n (C z v)) ∧
            T z = a z • (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C z) := by
  obtain ⟨c, hcU, hpc⟩ := exists_nativeCoordinateCanonicalPatch P hU hpU hpA hK hsq
  refine ⟨c.domain, hcU, c.domain.isOpen, hpc, c.coframe, c.smooth_coframe,
    c.invertible_coframe, fun z => coordinateSquaredCoframeCoefficient (c.coframe z) (T z),
    contDiffOn_coordinateSquaredCoframeCoefficient c.smooth_coframe c.invertible_coframe
      (hT.mono hcU), ?_⟩
  intro z hz
  exact ⟨c.intertwines z hz, coordinateSquaredCoframe_reconstruction P (c.coframe z)
    (c.invertible_coframe z hz.1) (K z) (c.intertwines z hz) (T z)
      (hcan z ⟨hcU hz.1, hz.2⟩)⟩

/-- Canonicality is preserved by an actual invertible spatial chart
differential, with arbitrary native coordinate normalizations. -/
theorem isSquaredCanonicalTensor_nativeConjugation {n : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : Model (2 * n) ≃L[ℝ] V) (P : Model (2 * n) ≃L[ℝ] F)
    (D : V →L[ℝ] F) (hD : D.IsInvertible) (J : V →L[ℝ] V)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => V) ℂ)
    (hT : IsSquaredCanonicalTensor
      (N.symm.toContinuousLinearMap.comp (J.comp N.toContinuousLinearMap))
      (T.compContinuousLinearMap (fun _ => N.toContinuousLinearMap))) :
    IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp
        ((D.comp (J.comp D.inverse)).comp P.toContinuousLinearMap))
      ((T.compContinuousLinearMap (fun _ => D.inverse)).compContinuousLinearMap
        (fun _ => P.toContinuousLinearMap)) := by
  let A := N.symm.toContinuousLinearMap.comp (D.inverse.comp P.toContinuousLinearMap)
  have h := isSquaredCanonicalTensor_comp_of_intertwines A
    (N.symm.toContinuousLinearMap.comp (J.comp N.toContinuousLinearMap))
    (P.symm.toContinuousLinearMap.comp ((D.comp (J.comp D.inverse)).comp P.toContinuousLinearMap))
    (by
      intro v
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, hD.inverse_apply_self])
    (T.compContinuousLinearMap (fun _ => N.toContinuousLinearMap)) hT
  convert h using 1
  ext v
  simp only [A, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Conjugation by the actual chart differential preserves the complex law. -/
theorem nativeConjugation_sq {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : V →L[ℝ] F) (hD : D.IsInvertible) (J : V →L[ℝ] V)
    (hsq : ∀ v, J (J v) = -v) (ξ : F) :
    (D.comp (J.comp D.inverse)) ((D.comp (J.comp D.inverse)) ξ) = -ξ := by
  simp only [ContinuousLinearMap.comp_apply, hD.inverse_apply_self]
  rw [hsq]
  simp only [map_neg, hD.self_apply_inverse]

/-- Pulling a constructed chart coframe back through the original chart
differential intertwines the actual source complex field. -/
theorem coframe_intertwines_nativeConjugation {n : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : F →L[ℝ] TangentCoordinates n) (D : V →L[ℝ] F) (hD : D.IsInvertible)
    (J : V →L[ℝ] V)
    (hC : ∀ ξ, C ((D.comp (J.comp D.inverse)) ξ) = coordinateComplexStructure n (C ξ))
    (ξ : V) : (C.comp D) (J ξ) = coordinateComplexStructure n ((C.comp D) ξ) := by
  simpa only [ContinuousLinearMap.comp_apply, hD.inverse_apply_self] using hC (D ξ)

/-- Reconstruction in chart coordinates gives literal reconstruction of
all original tensor slots after canceling the invertible chart differential. -/
theorem nativeTensor_reconstruction_of_inverseCoordinates {n : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => V) ℂ)
    (D : V →L[ℝ] F) (hD : D.IsInvertible) (C : F →L[ℝ] TangentCoordinates n) (a : ℂ)
    (hT : T.compContinuousLinearMap (fun _ => D.inverse) =
      a • (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C)) :
    T = a • (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C.comp D) := by
  ext ξ
  have h := congrArg (fun S => S (fun i => D (ξ i))) hT
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.comp_apply, hD.inverse_apply_self] using h

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle

namespace CompletedMaslovDimension

/-- The linear equivalence associated to dimension reindexing. -/
def modelEquiv {d e : ℕ} (h : d = e) : Model e ≃L[ℝ] Model d :=
  h.symm ▸ ContinuousLinearEquiv.refl ℝ (Model e)

theorem nativeField_sq {d e : ℕ} (h : d = e) (X : CompleteLiouvilleManifold d)
    (J : AlmostComplexField (ambient h X).manifold)
    (hsq : ∀ x v, J x (J x v) = -v) (x : X.manifold.Point) (v : Model d) :
    nativeField h X J x (nativeField h X J x v) = -v := by
  subst e
  exact hsq x v

theorem nativeTensor_canonical {d n : ℕ} (h : d = 2 * n)
    (X : CompleteLiouvilleManifold d)
    (J : AlmostComplexField (ambient h X).manifold)
    (T : (ambient h X).manifold.Point → SquaredCanonicalTensor n)
    (hc : ∀ x, IsSquaredCanonicalTensor (J x) (T x)) (x : X.manifold.Point) :
    IsSquaredCanonicalTensor
      ((modelEquiv h).symm.toContinuousLinearMap.comp
        ((nativeField h X J x).comp (modelEquiv h).toContinuousLinearMap))
      ((nativeTensor h X T x).compContinuousLinearMap
        (fun _ => (modelEquiv h).toContinuousLinearMap)) := by
  subst d
  convert hc x using 1 <;> ext v <;> rfl

end CompletedMaslovDimension

local instance {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

/-- Only a dimension reindexing of the original interior tangent model. -/
def interiorMaslovModelEquiv (h : k + 1 = 2 * n) :
    Model (2 * n) ≃L[ℝ] Model (k + 1) :=
  CompletedMaslovDimension.modelEquiv h

/-- A fixed linear normalization of the boundary–radius model. The actual
radius sign is carried by `endMaslovCoordinateDifferential`. -/
def endMaslovModelEquiv (h : k + 1 = 2 * n) :
    Model (2 * n) ≃L[ℝ] (Model k × ℝ) :=
  (interiorMaslovModelEquiv h).trans
    ((IntrinsicCollarGluing.bandModelEquiv k).symm.trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ (Model k)))

namespace LocalCompletionFamily

variable {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
  (F : LocalCompletionFamily P c t)

/-- The original interior-to-chart differential is invertible on its actual
chart source; no coordinate regularity input is added to the source data. -/
theorem isInvertible_interiorMaslovCoordinateDifferential (s : Parameter)
    (u w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) u).source) :
    (F.interiorMaslovCoordinateDifferential s u w).IsInvertible := by
  have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u
  have hi : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (chartAt (Model (k + 1)) u) w).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hw)
    have h := hm.comp_symm_deriv ((chartAt (Model (k + 1)) u).map_source hw)
    rwa [(chartAt (Model (k + 1)) u).left_inv hw] at h
  exact hi.comp (isInvertible_mfderiv_completionInterior F.native.width_pos
    (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
    (F.native.boundary s) (F.native.inverse s) (F.native.zero s) w).inverse

/-- The original full signed-cylinder differential is invertible, including
the boundary–radius sign and the actual cylinder inclusion. -/
theorem isInvertible_endMaslovCoordinateDifferential (s : Parameter)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band F.native.width (IntrinsicBoundary.Point k M))
    (hp : endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source) :
    (F.endMaslovCoordinateDifferential s u p).IsInvertible := by
  have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u
  have hi : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
      (chartAt (Model k × ℝ) u) (endBandCoordinates p)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hp)
    have h := hm.comp_symm_deriv ((chartAt (Model k × ℝ) u).map_source hp)
    rwa [(chartAt (Model k × ℝ) u).left_inv hp] at h
  exact hi.comp ((isInvertible_mfderiv_endBandCoordinates p).comp
    (isInvertible_mfderiv_completionCylinder F.native.width_pos
      (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
      (F.native.boundary s) (F.native.inverse s) (F.native.zero s) p).inverse)

end LocalCompletionFamily

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem nativeJ_sq (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient.manifold.Point)
    (v : Model (k + 1)) : S.nativeJ c t ht s hs x (S.nativeJ c t ht s hs x v) = -v := by
  exact CompletedMaslovDimension.nativeField_sq hdim _ _
    (S.compatible c t ht s hs).2.1 x v

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem nativeTensor_canonical (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient.manifold.Point) :
    IsSquaredCanonicalTensor
      ((interiorMaslovModelEquiv hdim).symm.toContinuousLinearMap.comp
        ((S.nativeJ c t ht s hs x).comp (interiorMaslovModelEquiv hdim).toContinuousLinearMap))
      ((S.nativeTensor c t ht s hs x).compContinuousLinearMap
        (fun _ => (interiorMaslovModelEquiv hdim).toContinuousLinearMap)) := by
  exact CompletedMaslovDimension.nativeTensor_canonical hdim _ _ _
    (S.canonical c t ht s hs) x

end OriginalLocalCompletionMaslovData

namespace LocalCompletionFamily

variable {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
  (F : LocalCompletionFamily P c t)

/-- Exactly the retained original interior parameters in one spatial chart. -/
def interiorMaslovLocus (u : IntrinsicInterior.Point k M) : Set (ℝ × Model (k + 1)) :=
  {q | ∃ v : Parameter, v ∈ F.base ∧ ∃ z : IntrinsicInterior.Point k M,
    z ∈ (chartAt (Model (k + 1)) u).source ∧ q = (v.val, chartAt (Model (k + 1)) u z)}

/-- Exactly the retained original full signed cylinder in one spatial chart. -/
def endMaslovLocus (u : IntrinsicBoundary.Point k M × ℝ) : Set (ℝ × (Model k × ℝ)) :=
  {z | ∃ v : Parameter, v ∈ F.base ∧ ∃ q : Band F.native.width (IntrinsicBoundary.Point k M),
    endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source ∧
      z = (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q))}

end LocalCompletionFamily

/-- The source has real-open smooth extensions of its actual conjugated
complex field and full chart tensor. No coframe, scalar, complex equation,
or canonical law off the retained original locus is assumed. -/
structure OriginalLocalCompletionMaslovTensorGerms
    (S : OriginalLocalCompletionMaslovData P L hdim) : Prop where
  interior : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
      (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
      ∃ K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1),
        ContDiffOn ℝ ∞ K U ∧
        ∃ T : (ℝ × Model (k + 1)) →
          ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ,
          ContDiffOn ℝ ∞ T U ∧
          ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
            (z : IntrinsicInterior.Point k M),
            z ∈ (chartAt (Model (k + 1)) u).source →
            (v.val, chartAt (Model (k + 1)) u z) ∈ U →
            let F := L.localCompletionFamily c t ht
            let x := interiorIn (F.native.patches v) z
            let D := F.interiorMaslovCoordinateDifferential v u z
            K (v.val, chartAt (Model (k + 1)) u z) =
              D.comp ((S.nativeJ c t ht v hv x).comp D.inverse) ∧
            T (v.val, chartAt (Model (k + 1)) u z) =
              (S.nativeTensor c t ht v hv x).compContinuousLinearMap (fun _ => D.inverse)
  cylinder : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
    endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
    ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
      ∃ K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ),
        ContDiffOn ℝ ∞ K U ∧
        ∃ T : (ℝ × (Model k × ℝ)) →
          ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model k × ℝ) ℂ,
          ContDiffOn ℝ ∞ T U ∧
          ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
            (q : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
            endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
            (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
            let F := L.localCompletionFamily c t ht
            let x := cylinder (F.native.patches v) q
            let D := F.endMaslovCoordinateDifferential v u q
            K (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              D.comp ((S.nativeJ c t ht v hv x).comp D.inverse) ∧
            T (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
              (S.nativeTensor c t ht v hv x).compContinuousLinearMap (fun _ => D.inverse)

namespace OriginalLocalCompletionMaslovTensorGerms

variable {S : OriginalLocalCompletionMaslovData P L hdim}

/-- Original raw coordinate extensions construct the entire coframe/scalar
interface used for smooth descent, with every source tensor slot preserved. -/
theorem coframeGerms (h : OriginalLocalCompletionMaslovTensorGerms S) :
    OriginalLocalCompletionMaslovCoframeGerms S := by
  constructor
  · intro c t ht s hs u w hw
    let F := L.localCompletionFamily c t ht
    obtain ⟨U, hU, hpU, K, hK, T, hT, hmatch⟩ := h.interior c t ht s hs u w hw
    have hsq : ∀ q ∈ U ∩ F.interiorMaslovLocus u, ∀ ξ, K q (K q ξ) = -ξ := by
      intro q hq ξ
      obtain ⟨v, hv, z, hz, rfl⟩ := hq.2
      have hi := F.isInvertible_interiorMaslovCoordinateDifferential v u z hz
      rw [(hmatch v hv z hz hq.1).1]
      exact nativeConjugation_sq _ hi _ (S.nativeJ_sq c t ht v hv _) ξ
    have hcan : ∀ q ∈ U ∩ F.interiorMaslovLocus u, IsSquaredCanonicalTensor
        ((interiorMaslovModelEquiv hdim).symm.toContinuousLinearMap.comp
          ((K q).comp (interiorMaslovModelEquiv hdim).toContinuousLinearMap))
        ((T q).compContinuousLinearMap (fun _ => (interiorMaslovModelEquiv hdim).toContinuousLinearMap)) := by
      intro q hq
      obtain ⟨v, hv, z, hz, rfl⟩ := hq.2
      rw [(hmatch v hv z hz hq.1).1, (hmatch v hv z hz hq.1).2]
      exact isSquaredCanonicalTensor_nativeConjugation (interiorMaslovModelEquiv hdim)
        (interiorMaslovModelEquiv hdim) _
        (F.isInvertible_interiorMaslovCoordinateDifferential v u z hz) _ _
        (S.nativeTensor_canonical c t ht v hv _)
    obtain ⟨V, hVU, hV, hpV, C, hC, hCi, a, ha, hCT⟩ :=
      exists_coordinateCoframeScalar_of_tensorExtensions (interiorMaslovModelEquiv hdim)
        hU hpU (show (s.val, chartAt (Model (k + 1)) u w) ∈ F.interiorMaslovLocus u
          from ⟨s, hs, w, hw, rfl⟩) K hK hsq T hT hcan
    refine ⟨V, hV, hpV, C, hC, hCi, a, ha, ?_⟩
    intro v hv z hz hVz
    have hi := F.isInvertible_interiorMaslovCoordinateDifferential v u z hz
    obtain ⟨hCJ, hTT⟩ := hCT _ ⟨hVz, v, hv, z, hz, rfl⟩
    obtain ⟨hJK, hTK⟩ := hmatch v hv z hz (hVU hVz)
    constructor
    · intro ξ
      rw [hJK] at hCJ
      exact coframe_intertwines_nativeConjugation _ _ hi _ hCJ ξ
    · exact nativeTensor_reconstruction_of_inverseCoordinates _ _ hi _ _ (hTK.symm.trans hTT)
  · intro c t ht s hs u p hp
    let F := L.localCompletionFamily c t ht
    obtain ⟨U, hU, hpU, K, hK, T, hT, hmatch⟩ := h.cylinder c t ht s hs u p hp
    have hsq : ∀ z ∈ U ∩ F.endMaslovLocus u, ∀ ξ, K z (K z ξ) = -ξ := by
      intro z hz ξ
      obtain ⟨v, hv, q, hq, rfl⟩ := hz.2
      have hi := F.isInvertible_endMaslovCoordinateDifferential v u q hq
      rw [(hmatch v hv q hq hz.1).1]
      exact nativeConjugation_sq _ hi _ (S.nativeJ_sq c t ht v hv _) ξ
    have hcan : ∀ z ∈ U ∩ F.endMaslovLocus u, IsSquaredCanonicalTensor
        ((endMaslovModelEquiv hdim).symm.toContinuousLinearMap.comp
          ((K z).comp (endMaslovModelEquiv hdim).toContinuousLinearMap))
        ((T z).compContinuousLinearMap (fun _ => (endMaslovModelEquiv hdim).toContinuousLinearMap)) := by
      intro z hz
      obtain ⟨v, hv, q, hq, rfl⟩ := hz.2
      rw [(hmatch v hv q hq hz.1).1, (hmatch v hv q hq hz.1).2]
      exact isSquaredCanonicalTensor_nativeConjugation (interiorMaslovModelEquiv hdim)
        (endMaslovModelEquiv hdim) _ (F.isInvertible_endMaslovCoordinateDifferential v u q hq) _ _
        (S.nativeTensor_canonical c t ht v hv _)
    obtain ⟨V, hVU, hV, hpV, C, hC, hCi, a, ha, hCT⟩ :=
      exists_coordinateCoframeScalar_of_tensorExtensions (endMaslovModelEquiv hdim)
        hU hpU (show (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ F.endMaslovLocus u
          from ⟨s, hs, p, hp, rfl⟩) K hK hsq T hT hcan
    refine ⟨V, hV, hpV, C, hC, hCi, a, ha, ?_⟩
    intro v hv q hq hVz
    have hi := F.isInvertible_endMaslovCoordinateDifferential v u q hq
    obtain ⟨hCJ, hTT⟩ := hCT _ ⟨hVz, v, hv, q, hq, rfl⟩
    obtain ⟨hJK, hTK⟩ := hmatch v hv q hq (hVU hVz)
    constructor
    · intro ξ
      rw [hJK] at hCJ
      exact coframe_intertwines_nativeConjugation _ _ hi _ hCJ ξ
    · exact nativeTensor_reconstruction_of_inverseCoordinates _ _ hi _ _ (hTK.symm.trans hTT)

end OriginalLocalCompletionMaslovTensorGerms

/-- Actual native canonical-square section germs on the real-open source
patches. Smoothness is bundle `ContMDiff`, and matching is through natural
square multiplication in every tensor slot. No smooth scalar or tensor
extension is supplied. Existence from a whole original section is pending. -/
structure OriginalLocalCompletionMaslovSectionGerms
    (S : OriginalLocalCompletionMaslovData P L hdim) : Prop where
  interior : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ g : NativeCoordinateCanonicalSectionGerm (interiorMaslovModelEquiv hdim)
      ((L.localCompletionFamily c t ht).interiorMaslovLocus u)
      (s.val, chartAt (Model (k + 1)) u w),
      ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
        (z : IntrinsicInterior.Point k M),
        z ∈ (chartAt (Model (k + 1)) u).source →
        ∀ hz : (v.val, chartAt (Model (k + 1)) u z) ∈ g.domain,
        let F := L.localCompletionFamily c t ht
        let x := interiorIn (F.native.patches v) z
        let D := F.interiorMaslovCoordinateDifferential v u z
        g.complexGerm.field (v.val, chartAt (Model (k + 1)) u z) =
          D.comp ((S.nativeJ c t ht v hv x).comp D.inverse) ∧
        (canonicalSquareMap (g.patch.complex ⟨_, hz⟩) (g.tensorSection ⟨_, hz⟩)).val =
          ((S.nativeTensor c t ht v hv x).compContinuousLinearMap (fun _ => D.inverse)).compContinuousLinearMap
            (fun _ => (interiorMaslovModelEquiv hdim).toContinuousLinearMap)
  cylinder : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
    endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
    ∃ g : NativeCoordinateCanonicalSectionGerm (endMaslovModelEquiv hdim)
      ((L.localCompletionFamily c t ht).endMaslovLocus u)
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)),
      ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
        (q : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
        endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
        ∀ hz : (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ g.domain,
        let F := L.localCompletionFamily c t ht
        let x := IntrinsicCompletionGluing.cylinder (F.native.patches v) q
        let D := F.endMaslovCoordinateDifferential v u q
        g.complexGerm.field (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
          D.comp ((S.nativeJ c t ht v hv x).comp D.inverse) ∧
        (canonicalSquareMap (g.patch.complex ⟨_, hz⟩) (g.tensorSection ⟨_, hz⟩)).val =
          ((S.nativeTensor c t ht v hv x).compContinuousLinearMap (fun _ => D.inverse)).compContinuousLinearMap
            (fun _ => (endMaslovModelEquiv hdim).toContinuousLinearMap)

namespace OriginalLocalCompletionMaslovSectionGerms

variable {S : OriginalLocalCompletionMaslovData P L hdim}

/-- Native source-section smoothness supplies the full real-open tensor
extensions. This uses the independently defined canonical bundle topology. -/
theorem tensorGerms (h : OriginalLocalCompletionMaslovSectionGerms S) :
    OriginalLocalCompletionMaslovTensorGerms S := by
  constructor
  · intro c t ht s hs u w hw
    obtain ⟨g, hmatch⟩ := h.interior c t ht s hs u w hw
    refine ⟨g.domain, g.domain.isOpen, g.mem_domain, g.complexGerm.field,
      g.smooth_field, g.tensor, g.smooth_tensor, ?_⟩
    intro v hv z hz hzg
    obtain ⟨hJ, hT⟩ := hmatch v hv z hz hzg
    exact ⟨hJ, g.patch.tensorExtension_eq_of_normalized g.tensorSection hzg _ hT⟩
  · intro c t ht s hs u p hp
    obtain ⟨g, hmatch⟩ := h.cylinder c t ht s hs u p hp
    refine ⟨g.domain, g.domain.isOpen, g.mem_domain, g.complexGerm.field,
      g.smooth_field, g.tensor, g.smooth_tensor, ?_⟩
    intro v hv q hq hzg
    obtain ⟨hJ, hT⟩ := hmatch v hv q hq hzg
    exact ⟨hJ, g.patch.tensorExtension_eq_of_normalized g.tensorSection hzg _ hT⟩

/-- Both the coframe and scalar are outputs of native source-section germs. -/
theorem coframeGerms (h : OriginalLocalCompletionMaslovSectionGerms S) :
    OriginalLocalCompletionMaslovCoframeGerms S := h.tensorGerms.coframeGerms

end OriginalLocalCompletionMaslovSectionGerms

end FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle
section PositiveRibbon

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]


/-- Real-open original field and full tensor extensions are consumed by the
original bundle realization. Its complete conclusion, including this same
completed family, actual grade and both marking-recovery laws, is retained. -/
theorem exists_pairDeformation_with_originalMaslovTensorGerms
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) EM)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
    (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
    (LP : OriginalBundlePairLaws PA PM PW PJ)
    (S : OriginalLocalCompletionMaslovData PA LA hdimA)
    (hS : OriginalLocalCompletionMaslovTensorGerms S) :
    ∃ (cA : Trivialization A (π A EA)) (cM : Trivialization M (π M EM)),
      ∃ (hbaseA : cA.baseSet = univ) (hbaseM : cM.baseSet = univ),
      ∃ (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA cA)
        (heM : CompatibleTrivialization (𝓡∂ (k + 1)) EM cM),
      let lam := PA.formInTrivialization cA
      let μ := PM.formInTrivialization cM
      let j := PJ.mapInTrivializations cM cA heA
      let b := PW.witnessInTrivialization cA heA
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x vs,
        lam t x vs = PA.form ⟨dA, hdA⟩ t (cA.coordChange dA t x)
          (fun i => mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) (cA.coordChange dA t) x (vs i))) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas M EM) t, t ∈ dM.baseSet → ∀ x vs,
        μ t x vs = PM.form ⟨dM, hdM⟩ t (cM.coordChange dM t x)
          (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (cM.coordChange dM t) x (vs i))) ∧
      (∀ dA (hdA : dA ∈ trivializationAtlas A EA) t, t ∈ dA.baseSet → ∀ x,
        b t x = PW.witness ⟨dA, hdA⟩ t
          (boundaryFamilyOn (cA.baseSet ∩ dA.baseSet) (cA.coordChange dA)
            (compatibleTransition_boundary cA dA heA (compatibleTrivialization_of_mem hdA)) t x)) ∧
      (∀ dM (hdM : dM ∈ trivializationAtlas M EM) dA (hdA : dA ∈ trivializationAtlas A EA) t,
        t ∈ dM.baseSet ∩ dA.baseSet → ∀ x,
        (j t x).val = dA.coordChange cA t (PJ.map ⟨dM, hdM⟩ ⟨dA, hdA⟩ t
          (cM.coordChange dM t x)).val) ∧
      ∃ Q : PairDeformation n,
      ∃ (eAs : ∀ t, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
          (Q.pair t).ambientDomain.domain.Point ∞)
        (eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
          (Q.pair t).ribbonDomain.domain.Point ∞)
        (eBs : ∀ t, (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
          (Q.pair t).ambientDomain.domain.boundary),
      ∃ (RA : ℝ → Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A ∞)
        (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞),
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (a + 1)) RA ∧
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eMs parameterZero (RM t.val x)).val) = (eMs t x).val) ∧
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
        (∀ t : Parameter,
        let P := Q.pair t
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map ((eBs t) x) = ((eAs t) x.val).val) ∧
        (∀ x, (P.ambientDomain.liouville.primitive ((eAs t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => ((eAs t) y).val) x) = lam t x) ∧
        (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (lam t) ∧
        (∀ x, P.ribbonEmbedding.map ((eMs t) x).val = (eBs t) (j t x)) ∧
        (∀ x, P.witness ((eBs t) x) = b t x) ∧
        (∀ x, (P.ribbonDomain.liouville.primitive ((eMs t) x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => ((eMs t) y).val) x) = μ t x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = (eBs t) '' range (j t) ∧
        P.embeddedCore = (fun x => (eBs t) (j t x)) '' {x | ∀ s : ℝ, 0 ≤ s →
          P.ribbonCompletion.ambient.completeFlow.flow s
            (P.ribbonCompletion.inclusion.map ((eMs t) x).val) ∈
              range (fun y => P.ribbonCompletion.inclusion.map ((eMs t) y).val)} ∧
        HasNativeCoordinateExtensions (k := a) P.ambientDomain.domain.extension (fun x => ((eAs t) x).val) ∧
        HasNativeCoordinateExtensions (k := k) P.ribbonDomain.domain.extension (fun x => ((eMs t) x).val)) ∧
      ∃ (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization cA s x)
        (hc : ∀ s, HasNativeCoordinateExtensions (k := a)
          (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
        (∀ s : Parameter, f.J s.val = S.descendedJ cA heA hbaseA Q eAs hp hc s) ∧
        (∀ s : Parameter, f.tensor s.val = S.descendedTensor cA heA hbaseA Q eAs hp hc s) ∧
        (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpoints := Q.maslovFamilyRepresentative f
        let grade := Q.gradedOfMaslovFamily f
        grade.etaExtension = Q.completedSymplecticExtension ∧ grade.family = f ∧
        ∃ actualGrade : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
          actualGrade = grade ∧
          (∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison cA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold (2 * n))
            (O : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ambientCompletion (W s)
              (fun y => chartValue cA (O.compact s) s ((eAs s).symm y)),
            markings = (fun s => O.ambientMarkingAt cA heA hbaseA Q hdimA eAs hp hc s) ∧
            (∀ s x, (markings s).equiv
              ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
                chartValue cA (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
              (t : Parameter) (F : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ambientEndpointSliceComparison LA cA heA hbaseA s hs Q hdimA eAs hp hc).equiv.trans
                (markings s).equiv = O.localEquiv F s hs) ∧
          ∃ (hpM : ∀ s x,
            ((Q.pair s).ribbonDomain.liouville.primitive (eMs s x).val).compContinuousLinearMap
              (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
                (fun y => (eMs s y).val) x) = PM.formInTrivialization cM s x)
            (hcM : ∀ s, HasNativeCoordinateExtensions (k := k)
              (Q.pair s).ribbonDomain.domain.extension (fun x => (eMs s x).val)),
          ∀ (H : Parameter → CompleteLiouvilleManifold (2 * n - 2))
            (R : OriginalBundleCompletionMarkingData LM H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ribbonCompletion (H s)
              (fun y => chartValue cM (R.compact s) s ((eMs s).symm y)),
            ribbonMarkings = (fun s => R.ribbonMarkingAt cM heM hbaseM Q hdimM eMs hpM hcM s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((Q.pair s).ribbonCompletion.inclusion.map (eMs s x).val) =
                chartValue cM (R.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := k) (M := M) (E := EM))
              (t : Parameter) (F : LocalCompletionFamily PM c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ribbonEndpointSliceComparison LM cM heM hbaseM s hs Q hdimM eMs hpM hcM).equiv.trans
                (ribbonMarkings s).equiv = R.localEquiv F s hs := by
  exact exists_pairDeformation_with_originalMaslovFamily hdimA hdimM PA PM PW PJ LA LM LP S hS.coframeGerms

end PositiveRibbon

section ZeroRibbon

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]


/-- Real-open original field and full tensor extensions are consumed by the
original bundle realization. Its complete conclusion, including this same
completed family, actual grade and both marking-recovery laws, is retained. -/
theorem exists_zero_pairDeformation_with_originalMaslovTensorGerms
    (PA : BundlePrimitiveData (k := 1) (M := A) EA)
    (LA : OriginalBundleLiouvilleLaws PA)
    (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ.map cM cA t))
    (PW : BundleWitnessData (k := 1) (M := A) EA)
    (μ : Parameter → (sourceManifold M).Form 1)
    (S : OriginalLocalCompletionMaslovData PA LA (n := 1) rfl)
    (hS : OriginalLocalCompletionMaslovTensorGerms S) :
    ∃ eM : Trivialization M (π M EM),
    ∃ eA : Trivialization A (π A EA), ∃ (hbaseM : eM.baseSet = univ) (hbaseA : eA.baseSet = univ),
    ∃ _heM : CompatibleTrivialization 𝓘(ℝ, Model 0) EM eM,
    ∃ heA : CompatibleTrivialization (𝓡∂ 2) EA eA,
    let α := PA.formInTrivialization eA;
    let j := PJ.mapInTrivializations eM eA heA;
    let b := PW.witnessInTrivialization eA heA;
    (∀ c hc t, t ∈ c.baseSet →
      α t = nativePullbackForm (eA.coordChange c t) (PA.form ⟨c, hc⟩ t)) ∧
    (∀ (cM : Trivialization M (π M EM)) hcM (cA : Trivialization A (π A EA)) hcA t,
      t ∈ cM.baseSet ∩ cA.baseSet → ∀ x,
      (j t x).val = cA.coordChange eA t
        (PJ.map ⟨cM, hcM⟩ ⟨cA, hcA⟩ t (eM.coordChange cM t x)).val) ∧
    (∀ c hc t, t ∈ c.baseSet → ∀ x,
      b t x = PW.witness ⟨c, hc⟩ t
        (boundaryFamilyOn (eA.baseSet ∩ c.baseSet) (eA.coordChange c)
          (compatibleTransition_boundary eA c heA (compatibleTrivialization_of_mem hc)) t x)) ∧
    ∃ Q : PairDeformation 1,
    ∃ eAs : ∀ t, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A
      (Q.pair t).ambientDomain.domain.Point ∞,
    ∃ eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞,
    ∃ eBs : ∀ t, (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary,
    ∃ (RA : ℝ → Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A A ∞)
      (RM : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞),
      IsJointlySmoothDiffeomorphFamily (𝓡∂ 2) RA ∧
      IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) RM ∧
      (∀ t x, (Q.ambientPresentation t).extensionEquiv
        ((eAs parameterZero (RA t.val x)).val) = (eAs t x).val) ∧
      (∀ t x, (Q.ribbonPresentation t).extensionEquiv
        ((eFs parameterZero (RM t.val x)).val) = (eFs t x).val) ∧
      (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eBs parameterZero x) = eBs t x) ∧
      (∀ t,
      let P := Q.pair t;
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eBs t x) = (eAs t x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eFs t x).val = eBs t (j t x)) ∧
        (∀ x, P.witness (eBs t x) = b t x) ∧
        P.embeddedCore = (eBs t) '' range (j t) ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eAs t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs t y).val) x) = α t x) ∧
        (sourceManifold M).pullback P.ribbonDomain.domain.extension
          (fun x => (eFs t x).val) P.ribbonDomain.liouville.primitive = μ t ∧
        (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary (eBs t)
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
            IntrinsicBoundary.restrictForm (α t) ∧
        HasNativeCoordinateExtensions (k := 1)
          P.ambientDomain.domain.extension (fun x => (eAs t x).val)) ∧
      ∃ (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (2)) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization eA s x)
        (hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
          (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
        (∀ s : Parameter, f.J s.val = S.descendedJ eA heA hbaseA Q eAs hp hc s) ∧
        (∀ s : Parameter, f.tensor s.val = S.descendedTensor eA heA hbaseA Q eAs hp hc s) ∧
        (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
          (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
          (hs : s ∈ (LA.localCompletionFamily c t ht).base),
          pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.J s.val) = S.J c t ht s hs ∧
          pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
            Q.source.ambientManifold (localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs)
            (f.tensor s.val) = S.tensor c t ht s hs) ∧
        let endpoints := Q.maslovFamilyRepresentative f
        let grade := Q.gradedOfMaslovFamily f
        grade.etaExtension = Q.completedSymplecticExtension ∧ grade.family = f ∧
        ∃ actualGrade : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
          actualGrade = grade ∧
          (∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
            (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
            (hs : s ∈ (LA.localCompletionFamily c t ht).base),
            pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).J = S.J c t ht s hs ∧
            pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
              (Q.pair s).ambientManifold
              ((localMaslovComparison eA heA hbaseA Q eAs hp hc c t ht s hs).trans
                (Q.ambientCompletionPresentation s).equiv) (endpoints s).tensor =
                  S.tensor c t ht s hs) ∧
          (∀ (W : Parameter → CompleteLiouvilleManifold 2)
            (O : OriginalBundleCompletionMarkingData LA W),
          ∃ markings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ambientCompletion (W s)
              (fun y => chartValue eA (O.compact s) s ((eAs s).symm y)),
            markings = (fun s => O.ambientMarkingAt eA heA hbaseA Q rfl eAs hp hc s) ∧
            (∀ s x, (markings s).equiv
              ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
                chartValue eA (O.compact s) s x) ∧
            ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
              (t : Parameter) (F : LocalCompletionFamily PA c t)
              (s : Parameter) (hs : s ∈ F.base),
              (F.ambientEndpointSliceComparison LA eA heA hbaseA s hs Q rfl eAs hp hc).equiv.trans
                (markings s).equiv = O.localEquiv F s hs) ∧
          ∀ (H : Parameter → CompleteLiouvilleManifold 0)
            (R : OriginalZeroBundleCompletionMarkingData (M := M) (E := EM) H),
          ∃ ribbonMarkings : ∀ s : Parameter,
            InclusionMarking (Q.pair s).ribbonCompletion (H s)
              (fun y => chartValue eM (R.compact s) s ((eFs s).symm y)),
            ribbonMarkings = (fun s => R.ribbonMarkingAt eM hbaseM Q eFs s) ∧
            (∀ s x, (ribbonMarkings s).equiv
              ((Q.pair s).ribbonCompletion.inclusion.map (eFs s x).val) =
                chartValue eM (R.compact s) s x) ∧
            ∀ (c : OriginalZeroCompactChart (M := M) (E := EM))
              (s : Parameter) (hs : s ∈ c.val.baseSet),
              (zeroRibbonEndpointEquiv eM hbaseM Q eFs c s hs).trans
                (ribbonMarkings s).equiv = R.chart c s hs := by
  exact exists_zero_pairDeformation_with_originalMaslovFamily PA LA PJ hPJ PW μ S hS.coframeGerms

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
