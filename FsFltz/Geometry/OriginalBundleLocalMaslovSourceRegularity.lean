import FsFltz.Geometry.OriginalBundleMaslovSourceRegularity

/-!
# Original tensor germs from retained local source sections

Source: `geoemtric-part-fsf.tex`, smooth extensions (119–122),
`def:chain` (163–199), `def:maslov` (212–244), and `sec:lean` (788–814).
A source smooth presentation is allowed to vary between retained local bases.
The given source complex field and full canonical-square section need smooth
extensions only near actual retained points. Their laws are confined to the
retained source. Differentiating actual marking germs gives the raw original
field and full tensor germs consumed by the original realization.

This produces regularity from supplied local source presentations. Constructing
these presentations and their ordinary source coefficients from a smooth
section on the retained collar-generated total family remains a separate foundation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- Ordinary local source coefficient extensions. The extension fields
carry no complex, canonical, compatible or nonvanishing law off the source. -/
def HasSmoothMaslovCoefficientGermsOn {n : ℕ} (N : SmoothManifold (2 * n))
    (B : Set Parameter) (J : ℝ → AlmostComplexField N)
    (T : ℝ → N.Point → SquaredCanonicalTensor n) : Prop :=
  ∀ s ∈ B, ∀ (a : N.Point) (y : Model (2 * n)),
    y ∈ (chartAt (Model (2 * n)) a).target →
    ∃ W : Set (ℝ × Model (2 * n)), IsOpen W ∧ (s.val, y) ∈ W ∧
      ∃ A : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n),
        ContDiffOn ℝ ∞ A W ∧
        ∃ T' : ℝ × Model (2 * n) → SquaredCanonicalTensor n,
          ContDiffOn ℝ ∞ T' W ∧
          ∀ v ∈ B, ∀ z ∈ (chartAt (Model (2 * n)) a).target,
            (v.val, z) ∈ W →
            A (v.val, z) = almostComplexInChart N a (J v.val) z ∧
            T' (v.val, z) = squaredTensorInChart N a (T v.val) z

/-- The analytic pullback needs only local source coefficient extensions.
Actual equality is retained on the original base, including its endpoints. -/
theorem exists_localCoordinatePullback_regularNeighborhood
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (N : SmoothManifold (2 * n)) (B : Set Parameter)
    (J : ℝ → AlmostComplexField N) (T : ℝ → N.Point → SquaredCanonicalTensor n)
    (hcoeff : HasSmoothMaslovCoefficientGermsOn N B J T)
    (a : N.Point) (φ : ℝ × F → Model (2 * n))
    {U : Set (ℝ × F)} (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    (s : Parameter) (hs : s ∈ B) (y : F) (hpU : (s.val, y) ∈ U)
    (hpTarget : φ (s.val, y) ∈ (chartAt (Model (2 * n)) a).target)
    (hpInv : (coordinateSpatialDerivative φ (s.val, y)).IsInvertible) :
    ∃ V : Set (ℝ × F), IsOpen V ∧ (s.val, y) ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V, φ z ∈ (chartAt (Model (2 * n)) a).target ∧
        (coordinateSpatialDerivative φ z).IsInvertible) ∧
      ∃ K : ℝ × F → F →L[ℝ] F, ContDiffOn ℝ ∞ K V ∧
        ∃ T' : ℝ × F → ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ,
          ContDiffOn ℝ ∞ T' V ∧
          ∀ v ∈ B, ∀ z : F, (v.val, z) ∈ V →
            K (v.val, z) = coordinatePullbackAlmostComplex N a J φ (v.val, z) ∧
            T' (v.val, z) = coordinatePullbackSquaredTensor N a T φ (v.val, z) := by
  obtain ⟨W, hW, hpW, A, hA, T0, hT0, hmatch⟩ := hcoeff s hs a _ hpTarget
  let U0 := U ∩ φ ⁻¹' (chartAt (Model (2 * n)) a).target
  have hU0 : IsOpen U0 := hφ.continuousOn.isOpen_inter_preimage hU
    (chartAt (Model (2 * n)) a).open_target
  obtain ⟨V, hV, hpV, hVU0, hmap, hK, hT'⟩ :=
    exists_coordinateCoefficientPullback_regularNeighborhood A T0 φ hU0 hW
      (hφ.mono inter_subset_left) hA hT0 (s.val, y) ⟨hpU, hpTarget⟩ hpW hpInv
  refine ⟨V, hV, hpV, (fun _ hz => (hVU0 hz).1),
    (fun z hz => ⟨(hVU0 hz).2, (hmap z hz).2⟩),
    _, hK, _, hT', ?_⟩
  intro v hv z hz
  obtain ⟨hAJ, hTT⟩ := hmatch v hv (φ (v.val, z)) (hVU0 hz).2 (hmap _ hz).1
  exact ⟨congrArg (fun L => (coordinateSpatialDerivative φ (v.val, z)).inverse.comp
    (L.comp (coordinateSpatialDerivative φ (v.val, z)))) hAJ,
    congrArg (fun Q => Q.compContinuousLinearMap (fun _ => coordinateSpatialDerivative φ (v.val, z))) hTT⟩

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

local instance localSourceRegularityProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance localSourceRegularityProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)
  (N : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter), t ∈ c.val.baseSet → SmoothManifold (2 * n))
  (J : ∀ c t ht, ℝ → AlmostComplexField (N c t ht))
  (T : ∀ c t ht, ℝ → (N c t ht).Point → SquaredCanonicalTensor n)
  (hcoeff : ∀ c t ht, HasSmoothMaslovCoefficientGermsOn (N c t ht)
    (L.localCompletionFamily c t ht).base (J c t ht) (T c t ht))
  (e : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base),
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient.manifold.SmoothEquiv (N c t ht))
  (hJ : ∀ c t ht s hs, S.J c t ht s hs =
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold (N c t ht)
      (CompletedMaslovDimension.comparison hdim
        ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient (N c t ht) (e c t ht s hs))
      (J c t ht s.val))
  (hT : ∀ c t ht s hs, S.tensor c t ht s hs =
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold (N c t ht)
      (CompletedMaslovDimension.comparison hdim
        ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient (N c t ht) (e c t ht s hs))
      (T c t ht s.val))
  (hmi : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) u).source →
    ∃ U : Set (ℝ × Model (k + 1)), IsOpen U ∧
      (s.val, chartAt (Model (k + 1)) u w) ∈ U ∧
      ∃ β : ℝ × Model (k + 1) → (N c t ht).Point,
        ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ β U ∧
        ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
          (z : IntrinsicInterior.Point k M),
          z ∈ (chartAt (Model (k + 1)) u).source →
          (v.val, chartAt (Model (k + 1)) u z) ∈ U →
          β (v.val, chartAt (Model (k + 1)) u z) =
            e c t ht v hv (interiorIn ((L.localCompletionFamily c t ht).native.patches v) z))
  (hme : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (_hs : s ∈ (L.localCompletionFamily c t ht).base)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (p : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
    endBandCoordinates p ∈ (chartAt (Model k × ℝ) u).source →
    ∃ U : Set (ℝ × (Model k × ℝ)), IsOpen U ∧
      (s.val, chartAt (Model k × ℝ) u (endBandCoordinates p)) ∈ U ∧
      ∃ β : ℝ × (Model k × ℝ) → (N c t ht).Point,
        ContMDiffOn 𝓘(ℝ, ℝ × (Model k × ℝ)) 𝓘(ℝ, Model (2 * n)) ∞ β U ∧
        ∀ (v : Parameter) (hv : v ∈ (L.localCompletionFamily c t ht).base)
          (q : Band (L.localCompletionFamily c t ht).native.width (IntrinsicBoundary.Point k M)),
          endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source →
          (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) ∈ U →
          β (v.val, chartAt (Model k × ℝ) u (endBandCoordinates q)) =
            e c t ht v hv (cylinder ((L.localCompletionFamily c t ht).native.patches v) q))

include hJ hT hmi hme hcoeff in
/-- Joint source smoothness and ordinary real marking-map germs produce
all retained original field/full-tensor germs. Only the original retained
parameters carry the identification with the prescribed source section. -/
theorem tensorGerms_of_localSource_markingMapGerms : OriginalLocalCompletionMaslovTensorGerms S := by
  constructor
  · intro c t ht s hs u w hw
    let F := L.localCompletionFamily c t ht
    let NC := N c t ht
    let JC := J c t ht
    let TC := T c t ht
    let := completionChartedSpace F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hmi c t ht s hs u w hw
    let a := β (s.val, chartAt (Model (k + 1)) u w)
    let C := chartAt (Model (2 * n)) a
    let W := U ∩ β ⁻¹' C.source
    have hW : IsOpen W := hβ.continuousOn.isOpen_inter_preimage hU C.open_source
    have hpW : (s.val, chartAt (Model (k + 1)) u w) ∈ W :=
      ⟨hpU, mem_chart_source _ a⟩
    let φ := fun z : ℝ × Model (k + 1) => C (β z)
    have hφ : ContDiffOn ℝ ∞ φ W :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        (hβ.mono inter_subset_left) inter_subset_right).contDiffOn
    have hχ := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u).mdifferentiableAt hw
    have hχi := chartTangentMap_isInvertible (IntrinsicInterior.smoothManifold k M) u w hw
    have hj := (contMDiff_completionInterior F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).mdifferentiableAt (by simp) (x := w)
    have hji := isInvertible_mfderiv_completionInterior F.native.width_pos
      (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
      (F.native.boundary s) (F.native.inverse s) (F.native.zero s) w
    have hm := markingMapGerm_coordinate_pullback NC s (chartAt (Model (k + 1)) u)
      (interiorIn (F.native.patches s)) (e c t ht s hs)
      (chartAt (Model (k + 1)) u).source (chartAt (Model (k + 1)) u).open_source
      w hw U hU β hβ hpU hχ hj hχi hji (heq s hs) a
      (by exact (heq s hs w hw hpU).symm ▸ mem_chart_source _ a) JC TC
    obtain ⟨V, hV, hpV, hVW, htarget, K, hK, T', hT', hmatch⟩ :=
      exists_localCoordinatePullback_regularNeighborhood NC F.base JC TC
        (hcoeff c t ht) a φ hW hφ s hs (chartAt (Model (k + 1)) u w) hpW
      (C.map_source (mem_chart_source _ a)) hm.1
    refine ⟨V, hV, hpV, K, hK,
      T', hT', ?_⟩
    intro v hv z hz hzV
    have hzU := (hVW hzV).1
    have hzC : e c t ht v hv (interiorIn (F.native.patches v) z) ∈ C.source := by
      rw [← heq v hv z hz hzU]
      exact (hVW hzV).2
    let := completionChartedSpace F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.boundary v) (F.native.zero v)
    have hjz := (contMDiff_completionInterior F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
      (F.native.inverse v) (F.native.zero v)).mdifferentiableAt (by simp) (x := z)
    have hmz := markingMapGerm_coordinate_pullback NC v (chartAt (Model (k + 1)) u)
      (interiorIn (F.native.patches v)) (e c t ht v hv)
      (chartAt (Model (k + 1)) u).source (chartAt (Model (k + 1)) u).open_source
      z hz U hU β hβ hzU
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u).mdifferentiableAt hz) hjz
      (chartTangentMap_isInvertible (IntrinsicInterior.smoothManifold k M) u z hz)
      (isInvertible_mfderiv_completionInterior F.native.width_pos (F.native.collar v)
        (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
        (F.native.inverse v) (F.native.zero v) z) (heq v hv) a hzC JC TC
    have hnJ := CompletedMaslovDimension.nativeField_comparison_pullback hdim
      (F.sliceCompletion L v).ambient NC (e c t ht v hv) (JC v.val)
      (interiorIn (F.native.patches v) z)
    have hnT := CompletedMaslovDimension.nativeTensor_comparison_pullback hdim
      (F.sliceCompletion L v).ambient NC (e c t ht v hv) (TC v.val)
      (interiorIn (F.native.patches v) z)
    rw [← hJ c t ht v hv] at hnJ
    rw [← hT c t ht v hv] at hnT
    change S.nativeJ c t ht v hv (interiorIn (F.native.patches v) z) = _ at hnJ
    change S.nativeTensor c t ht v hv (interiorIn (F.native.patches v) z) = _ at hnT
    dsimp only [LocalCompletionFamily.interiorMaslovCoordinateDifferential]
    rw [hnJ, hnT]
    rw [(hmatch v hv _ hzV).1, (hmatch v hv _ hzV).2]
    exact ⟨hmz.2.1, hmz.2.2⟩
  · intro c t ht s hs u p hp
    let F := L.localCompletionFamily c t ht
    let NC := N c t ht
    let JC := J c t ht
    let TC := T c t ht
    let := completionChartedSpace F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.boundary s) (F.native.zero s)
    let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) F.native.width
    let χ := chartAt (Model k × ℝ) u ∘ endBandCoordinates (δ := F.native.width)
    let A := endBandCoordinates (δ := F.native.width) ⁻¹' (chartAt (Model k × ℝ) u).source
    have hA : IsOpen A := (chartAt (Model k × ℝ) u).open_source.preimage
      contMDiff_endBandCoordinates.continuous
    have hχdata (q : Band F.native.width (IntrinsicBoundary.Point k M))
        (hq : endBandCoordinates q ∈ (chartAt (Model k × ℝ) u).source) :
        MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q ∧
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q).IsInvertible := by
      have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u).mdifferentiableAt hq
      have hd := contMDiff_endBandCoordinates.mdifferentiableAt (by simp) (x := q)
      have hci : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (endBandCoordinates q)).IsInvertible := by
        have hm := mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u
        apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hm.symm_comp_deriv hq)
        have h := hm.comp_symm_deriv ((chartAt (Model k × ℝ) u).map_source hq)
        rwa [(chartAt (Model k × ℝ) u).left_inv hq] at h
      refine ⟨hc.comp q hd, ?_⟩
      dsimp only [χ]
      rw [mfderiv_comp q hc hd]
      exact hci.comp (isInvertible_mfderiv_endBandCoordinates q)
    obtain ⟨U, hU, hpU, β, hβ, heq⟩ := hme c t ht s hs u p hp
    let a := β (s.val, χ p)
    let C := chartAt (Model (2 * n)) a
    let W := U ∩ β ⁻¹' C.source
    have hW : IsOpen W := hβ.continuousOn.isOpen_inter_preimage hU C.open_source
    have hpW : (s.val, χ p) ∈ W := ⟨hpU, mem_chart_source _ a⟩
    let φ := fun z : ℝ × (Model k × ℝ) => C (β z)
    have hφ : ContDiffOn ℝ ∞ φ W :=
      ((contMDiffOn_chart (I := 𝓘(ℝ, Model (2 * n))) (x := a)).comp
        (hβ.mono inter_subset_left) inter_subset_right).contDiffOn
    have hj := (contMDiff_cylinder F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).mdifferentiableAt (by simp) (x := p)
    have hji := isInvertible_mfderiv_completionCylinder F.native.width_pos
      (F.native.collar s) (F.native.embedding s) (F.native.smooth s)
      (F.native.boundary s) (F.native.inverse s) (F.native.zero s) p
    have hm := markingMapGerm_coordinate_pullback NC s χ
      (cylinder (F.native.patches s)) (e c t ht s hs) A hA p hp U hU β hβ hpU
      (hχdata p hp).1 hj (hχdata p hp).2 hji (heq s hs) a
      (by exact (heq s hs p hp hpU).symm ▸ mem_chart_source _ a) JC TC
    obtain ⟨V, hV, hpV, hVW, htarget, K, hK, T', hT', hmatch⟩ :=
      exists_localCoordinatePullback_regularNeighborhood NC F.base JC TC
        (hcoeff c t ht) a φ hW hφ s hs (χ p) hpW (C.map_source (mem_chart_source _ a)) hm.1
    refine ⟨V, hV, hpV, K, hK,
      T', hT', ?_⟩
    intro v hv q hq hqV
    have hqU := (hVW hqV).1
    have hqC : e c t ht v hv (cylinder (F.native.patches v) q) ∈ C.source := by
      exact (heq v hv q hq hqU).symm ▸ (hVW hqV).2
    let := completionChartedSpace F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.boundary v) (F.native.zero v)
    have hjq := (contMDiff_cylinder F.native.width_pos (F.native.collar v)
      (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
      (F.native.inverse v) (F.native.zero v)).mdifferentiableAt (by simp) (x := q)
    have hmz := markingMapGerm_coordinate_pullback NC v χ
      (cylinder (F.native.patches v)) (e c t ht v hv) A hA q hq U hU β hβ hqU
      (hχdata q hq).1 hjq (hχdata q hq).2
      (isInvertible_mfderiv_completionCylinder F.native.width_pos (F.native.collar v)
        (F.native.embedding v) (F.native.smooth v) (F.native.boundary v)
        (F.native.inverse v) (F.native.zero v) q) (heq v hv) a hqC JC TC
    have hdχ : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q =
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (endBandCoordinates q)).comp
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates q) :=
      mfderiv_comp q
        ((mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u).mdifferentiableAt hq)
        (contMDiff_endBandCoordinates.mdifferentiableAt (by simp))
    have hnJ := CompletedMaslovDimension.nativeField_comparison_pullback hdim
      (F.sliceCompletion L v).ambient NC (e c t ht v hv) (JC v.val)
      (cylinder (F.native.patches v) q)
    have hnT := CompletedMaslovDimension.nativeTensor_comparison_pullback hdim
      (F.sliceCompletion L v).ambient NC (e c t ht v hv) (TC v.val)
      (cylinder (F.native.patches v) q)
    rw [← hJ c t ht v hv] at hnJ
    rw [← hT c t ht v hv] at hnT
    change S.nativeJ c t ht v hv (cylinder (F.native.patches v) q) = _ at hnJ
    change S.nativeTensor c t ht v hv (cylinder (F.native.patches v) q) = _ at hnT
    have hD : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) χ q).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
          (cylinder (F.native.patches v)) q).inverse =
        F.endMaslovCoordinateDifferential v u q := by
      rw [hdχ]
      rfl
    dsimp only
    rw [hnJ, hnT]
    dsimp only at hmz
    rw [hD] at hmz
    rw [(hmatch v hv _ hqV).1, (hmatch v hv _ hqV).2]
    exact ⟨hmz.2.1, hmz.2.2⟩

end OriginalLocalCompletionMaslovData
end FsFltz.Geometry.IntrinsicSmoothBundle
