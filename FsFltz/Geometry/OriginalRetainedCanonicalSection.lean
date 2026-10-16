import FsFltz.Geometry.OriginalRetainedCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalMapExtensionOn

/-!
# Arbitrary sections of the actual retained canonical-square bundle

Source: `geoemtric-part-fsf.tex`, smooth extension (119–122),
`def:maslov` (212–232), and `sec:lean` (788–814). Sections are selected
after the retained canonical-square bundle. The total/native identifications
use the actual slice equivalence and preserve every tensor slot. Zero values
outside the retained base are only a convention for total functions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct Classical
open Set Filter Topology Bundle

namespace FsFltz.Geometry

private theorem retainedFiberCast_section {X : Type*}
    (f : X → Model (2 * n) →L[ℝ] Model (2 * n))
    (σ : ∀ x, CanonicalTensorSquare (f x))
    {x y : X} (h : x = y) (e : f x = f y) :
    continuousLinearFiberCast CanonicalTensorSquare e (σ x) = σ y := by
  subst y
  rfl

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (B : Set Parameter) (hB : IsOpen B)

/-- A section of the independently constructed bundle on its actual open base. -/
abbrev OriginalRetainedCanonicalSection :=
  ∀ x : originalRetainedCanonicalBase (δ := δ) C B hB,
    OriginalRetainedCanonicalTensorSquare C J N B hB x

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem originalTotalComplex_sliceIn (s : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) :
    originalTotalComplex C J N (sliceIn (fun t p => C t p.val) s x) =
      N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap) := by
  have hi : (fiberEquiv (fun t p => C t p.val) s) x =
      ⟨sliceIn (fun t p => C t p.val) s x, parameter_sliceIn _ _ _⟩ := rfl
  rcases jointly_surjective (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) x with
    ⟨z, rfl⟩ | ⟨z, rfl⟩
  · rw [sliceIn_original]
    simp only [sliceIn_original] at hi
    change N.symm.toContinuousLinearMap.comp
      ((J s ((fiberEquiv (fun t p => C t p.val) s).symm _)).comp N.toContinuousLinearMap) = _
    exact congrArg (fun q => N.symm.toContinuousLinearMap.comp ((J s q).comp N.toContinuousLinearMap))
      ((congrArg (fiberEquiv (fun t p => C t p.val) s).symm hi).symm.trans
        ((fiberEquiv (fun t p => C t p.val) s).symm_apply_apply _))
  · rw [sliceIn_cylinder]
    simp only [sliceIn_cylinder] at hi
    change N.symm.toContinuousLinearMap.comp
      ((J s ((fiberEquiv (fun t p => C t p.val) s).symm _)).comp N.toContinuousLinearMap) = _
    exact congrArg (fun q => N.symm.toContinuousLinearMap.comp ((J s q).comp N.toContinuousLinearMap))
      ((congrArg (fiberEquiv (fun t p => C t p.val) s).symm hi).symm.trans
        ((fiberEquiv (fun t p => C t p.val) s).symm_apply_apply _))

/-- Restrict the arbitrary total section through the actual slice inclusion,
then fill only the unused parameters by zero. -/
def originalRetainedSectionNative (σ : OriginalRetainedCanonicalSection C J N B hB) :
    OriginalNativeCanonicalSection C J N := by
  intro s x
  by_cases hs : s ∈ B
  · exact continuousLinearFiberCast CanonicalTensorSquare
      (originalTotalComplex_sliceIn C J N s x)
      (σ ⟨sliceIn (fun t p => C t p.val) s x, by
        change parameter (fun t p => C t p.val) (sliceIn (fun t p => C t p.val) s x) ∈ B
        simpa only [parameter_sliceIn] using hs⟩)
  · exact 0

/-- The arbitrary section is extended only as a total-function convention. -/
def originalRetainedSectionTotal (σ : OriginalRetainedCanonicalSection C J N B hB)
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    OriginalTotalCanonicalTensorSquare C J N x :=
  if hx : parameter (fun t p => C t p.val) x ∈ B then σ ⟨x, hx⟩ else 0

set_option maxHeartbeats 800000 in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Nonvanishing is preserved by the actual fiber identification. -/
theorem originalRetainedSectionNative_neZero
    (σ : OriginalRetainedCanonicalSection C J N B hB) (hσ : ∀ x, σ x ≠ 0)
    (s : Parameter) (hs : s ∈ B)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) :
    originalRetainedSectionNative C J N B hB σ s x ≠ 0 := by
  simp only [originalRetainedSectionNative, dite_eq_left hs]
  let y : originalRetainedCanonicalBase (δ := δ) C B hB := ⟨sliceIn (fun t p => C t p.val) s x, by
    change parameter (fun t p => C t p.val) (sliceIn (fun t p => C t p.val) s x) ∈ B
    rw [parameter_sliceIn]
    exact hs⟩
  let e := continuousLinearFiberCast CanonicalTensorSquare (originalTotalComplex_sliceIn C J N s x)
  change e (σ y) ≠ 0
  rw [ne_eq, e.map_eq_zero_iff]
  exact hσ y

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Natural square multiplication recovers every normalized tensor slot. -/
theorem originalNativeSectionTensor_normalized
    (σ : OriginalNativeCanonicalSection C J N) (s : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) :
    (originalNativeSectionTensor C J N σ s x).compContinuousLinearMap
      (fun _ => N.toContinuousLinearMap) = (canonicalSquareMap _ (σ s x)).val := by
  ext v
  simp only [originalNativeSectionTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem originalNativeSectionTensor_canonical
    (σ : OriginalNativeCanonicalSection C J N) (s : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) :
    IsSquaredCanonicalTensor
      (N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap))
      ((originalNativeSectionTensor C J N σ s x).compContinuousLinearMap
        (fun _ => N.toContinuousLinearMap)) := by
  rw [originalNativeSectionTensor_normalized]
  exact (canonicalSquareMap _ (σ s x)).property

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem originalNativeSectionTensor_neZero
    (σ : OriginalNativeCanonicalSection C J N) (s : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val))
    (hsq : ∀ v, J s x (J s x v) = -v) (hσ : σ s x ≠ 0) :
    originalNativeSectionTensor C J N σ s x ≠ 0 := by
  intro hzero
  apply hσ
  have hcomplex : ∀ v, (N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap))
      ((N.symm.toContinuousLinearMap.comp ((J s x).comp N.toContinuousLinearMap)) v) = -v := by
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [hsq, map_neg, ContinuousLinearEquiv.symm_apply_apply]
  apply (canonicalSquareMap_bijective _ hcomplex).1
  apply Subtype.ext
  rw [map_zero]
  have h := originalNativeSectionTensor_normalized C J N σ s x
  rw [hzero] at h
  exact h.symm

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem originalRetainedSectionTotal_on
    (σ : OriginalRetainedCanonicalSection C J N B hB)
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :
    originalRetainedSectionTotal C J N B hB σ x.val = σ x := by
  have hx : parameter (fun t p => C t p.val) x.val ∈ B := x.property
  simp only [originalRetainedSectionTotal, dite_eq_left hx]

set_option maxHeartbeats 800000 in
omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Total restriction and actual slice restriction are inverse, including
the full cylinder and the seam. -/
theorem originalTotalSection_retainedNative
    (σ : OriginalRetainedCanonicalSection C J N B hB) :
    originalTotalSection C J N (originalRetainedSectionNative C J N B hB σ) =
      originalRetainedSectionTotal C J N B hB σ := by
  funext y
  let s := parameter (fun t p => C t p.val) y
  let x := (fiberEquiv (fun t p => C t p.val) s).symm ⟨y, rfl⟩
  have hx : sliceIn (fun t p => C t p.val) s x = y :=
    congrArg Subtype.val ((fiberEquiv (fun t p => C t p.val) s).apply_symm_apply ⟨y, rfl⟩)
  by_cases hs : s ∈ B
  · change originalRetainedSectionNative C J N B hB σ s x = _
    simp only [originalRetainedSectionNative, dite_eq_left hs]
    change continuousLinearFiberCast CanonicalTensorSquare
      (originalTotalComplex_sliceIn C J N s x) (σ ⟨sliceIn (fun t p => C t p.val) s x, _⟩) = _
    change _ = (if hy : s ∈ B then σ ⟨y, hy⟩ else (0 : OriginalTotalCanonicalTensorSquare C J N y))
    rw [dite_eq_left hs]
    apply retainedFiberCast_section (fun z : originalRetainedCanonicalBase (δ := δ) C B hB =>
      originalTotalComplex C J N z.val) σ (x := ⟨sliceIn (fun t p => C t p.val) s x, _⟩)
      (y := ⟨y, hs⟩) (Subtype.ext hx)
  · change originalRetainedSectionNative C J N B hB σ s x = _
    simp only [originalRetainedSectionNative, dite_eq_right hs]
    change (0 : OriginalTotalCanonicalTensorSquare C J N y) =
      (if hy : s ∈ B then σ ⟨y, hy⟩ else (0 : OriginalTotalCanonicalTensorSquare C J N y))
    rw [dite_eq_right hs]

/-- The graph in the actual retained bundle. -/
def originalRetainedSectionGraph (σ : OriginalRetainedCanonicalSection C J N B hB)
    (x : originalRetainedCanonicalBase (δ := δ) C B hB) :
    Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB) := ⟨x, σ x⟩

/-- Forget only the open-base subtype of an arbitrary map into the bundle. -/
def originalRetainedMapLift
    (f : originalRetainedCanonicalBase (δ := δ) C B hB →
      Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB))
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N) :=
  if hx : parameter (fun t p => C t p.val) x ∈ B then
    ⟨(f ⟨x, hx⟩).proj.val, (f ⟨x, hx⟩).snd⟩ else ⟨x, 0⟩

variable (hδ : 0 < δ)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- Actual coordinates in the independently constructed retained bundle. -/
def originalRetainedCanonicalCoordinateAt
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (z : Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB))
    (hz : z.proj.val ∈ c.totalDomain) : c.RealModel :=
  (c.baseCoordinate hz.choose,
    (originalRetainedCanonicalTensorPretrivialization hδ C hemb hboundary hzero hjoint
      J N hC hinv B hB c z).2)

/-- The restricted pretrivialization is used literally, so forgetting the
open subtype preserves both the spatial and full-section coordinate. -/
theorem originalRetainedCanonicalCoordinateAt_eq
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (z : Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB))
    (hz : z.proj.val ∈ c.totalDomain) :
    originalRetainedCanonicalCoordinateAt C J N B hB hδ hemb hboundary hzero hjoint hC hinv c z hz =
      c.coordinateAt N hjoint hC hinv ⟨z.proj.val, z.snd⟩ hz := by
  rw [originalRetainedCanonicalCoordinateAt,
    originalRetainedCanonicalTensorPretrivialization_apply]
  rfl

/-- Ordinary real local-map extensions in the actual restricted bundle
coordinates. This condition is generic in the map, precedes its tensor, and
requires no matching or geometric laws outside the retained base. -/
def HasOriginalRetainedLocalMapExtensions
    (f : originalRetainedCanonicalBase (δ := δ) C B hB →
      Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB)) : Prop :=
  ∀ x : originalRetainedCanonicalBase (δ := δ) C B hB,
    ∃ (c d : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
      (p : c.NativeBase), p ∈ c.nativeDomain ∧ c.inclusion p = x.val ∧
      (f x).proj.val ∈ d.totalDomain ∧
      ∃ (U : TopologicalSpace.Opens c.RealBase) (G : c.RealBase → d.RealModel),
        c.baseCoordinate p ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
        (U : Set c.RealBase) ⊆ c.realDomain ∧
        ∀ (q : c.NativeBase) (_hq : q ∈ c.nativeDomain)
          (hqB : parameter (fun t p => C t p.val) (c.inclusion q) ∈ B),
          c.baseCoordinate q ∈ U →
          ∃ hd : (f ⟨c.inclusion q, hqB⟩).proj.val ∈ d.totalDomain,
            G (c.baseCoordinate q) = originalRetainedCanonicalCoordinateAt
              C J N B hB hδ hemb hboundary hzero hjoint hC hinv d
              (f ⟨c.inclusion q, hqB⟩) hd

/-- Actual restricted bundle coordinates give the old retained-subset
interface by a proved coordinate identification, for any map. -/
theorem originalRetainedMapLift_localExtensions
    (f : originalRetainedCanonicalBase (δ := δ) C B hB →
      Bundle.TotalSpace ℂ (OriginalRetainedCanonicalTensorSquare C J N B hB))
    (hf : HasOriginalRetainedLocalMapExtensions C J N B hB hδ hemb hboundary hzero hjoint hC hinv f) :
    HasOriginalTotalLocalMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv
      {x | parameter (fun t p => C t p.val) x ∈ B} (originalRetainedMapLift C J N B hB f) := by
  intro x hx
  change parameter (fun t p => C t p.val) x ∈ B at hx
  obtain ⟨c, d, p, hp, hpx, hfd, U, G, hpU, hG, hU, hret⟩ := hf ⟨x, hx⟩
  refine ⟨c, d, p, hp, hpx, ?_, U, G, hpU, hG, hU, ?_⟩
  · simpa only [originalRetainedMapLift, dite_eq_left hx] using hfd
  · intro q hq hqB hqU
    change parameter (fun t p => C t p.val) (c.inclusion q) ∈ B at hqB
    obtain ⟨hd, he⟩ := hret q hq hqB hqU
    simp only [originalRetainedMapLift, dite_eq_left hqB]
    refine ⟨hd, ?_⟩
    rw [originalRetainedCanonicalCoordinateAt_eq] at he
    exact he

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem originalRetainedMapLift_sectionGraph
    (σ : OriginalRetainedCanonicalSection C J N B hB) :
    originalRetainedMapLift C J N B hB (originalRetainedSectionGraph C J N B hB σ) =
      originalTotalSectionGraph C J N (originalRetainedSectionNative C J N B hB σ) := by
  funext x
  change _ = (⟨x, originalTotalSection C J N (originalRetainedSectionNative C J N B hB σ) x⟩ :
    Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
  rw [originalTotalSection_retainedNative]
  by_cases hx : parameter (fun t p => C t p.val) x ∈ B
  · simp only [originalRetainedMapLift, originalRetainedSectionGraph,
      originalRetainedSectionTotal, dite_eq_left hx]
  · simp only [originalRetainedMapLift, originalRetainedSectionTotal, dite_eq_right hx]

/-- An arbitrary genuine retained section supplies the generic extension
property for its identical native graph. -/
theorem originalRetainedSectionNative_localMapExtensions
    (σ : OriginalRetainedCanonicalSection C J N B hB)
    (hσ : HasOriginalRetainedLocalMapExtensions C J N B hB hδ hemb hboundary hzero hjoint hC hinv
      (originalRetainedSectionGraph C J N B hB σ)) :
    HasOriginalTotalLocalMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv
      {x | parameter (fun t p => C t p.val) x ∈ B}
      (originalTotalSectionGraph C J N (originalRetainedSectionNative C J N B hB σ)) := by
  have h := originalRetainedMapLift_localExtensions C J N B hB hδ hemb hboundary hzero hjoint
    hC hinv (originalRetainedSectionGraph C J N B hB σ) hσ
  simpa only [originalRetainedMapLift_sectionGraph] using h

variable (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

include hmix P in
/-- Proved real transitions transfer the defining extension regularity to
every original chart, for the same arbitrary section. -/
theorem originalRetainedSectionNative_chartMapExtensions
    (σ : OriginalRetainedCanonicalSection C J N B hB)
    (hσ : HasOriginalRetainedLocalMapExtensions C J N B hB hδ hemb hboundary hzero hjoint hC hinv
      (originalRetainedSectionGraph C J N B hB σ)) :
    HasOriginalTotalChartMapExtensionsOn hδ C hemb hboundary hzero J N hjoint hC hinv
      {x | parameter (fun t p => C t p.val) x ∈ B}
      (originalTotalSectionGraph C J N (originalRetainedSectionNative C J N B hB σ)) := by
  exact originalTotalChartMapExtensionsOn_of_localMapExtensionsOn
    hδ C hemb hboundary hzero J N hjoint hC hinv hmix P _ _ continuous_id
    (originalRetainedSectionNative_localMapExtensions C J N B hB hδ hemb hboundary hzero hjoint hC hinv σ hσ)

end IntrinsicCompletionGluing
