import FsFltz.Geometry.CanonicalPretrivializationCoordinates
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionEndCanonicalBundle

/-!
# Canonical-square fibers and coordinates on the original completed total family

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 788–814. The base here is the actual original completed
quotient, with its unchanged interval parameter. A single native tangent
normalization is used on both original inclusions. The cylinder coordinate
basis appears only in the construction of its local coframe charts.

The fiber identifications and image pretrivializations are constructed
before a section is supplied. No overlap smoothness is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- Reindexing the canonical square preserves its natural two-block tensor. -/
theorem canonicalTensorSquareCast_squareMap {n : ℕ}
    {A B : Model (2 * n) →L[ℝ] Model (2 * n)} (h : A = B)
    (τ : CanonicalTensorSquare A) :
    (canonicalSquareMap B (continuousLinearFiberCast CanonicalTensorSquare h τ)).val =
      (canonicalSquareMap A τ).val := by
  cases h
  rfl

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ}
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))

/-- The original complex field evaluated in its actual completion slice. -/
def originalTotalComplex
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    Model (2 * n) →L[ℝ] Model (2 * n) :=
  let t := parameter (fun t p => C t p.val) x
  let z := (fiberEquiv (fun t p => C t p.val) t).symm ⟨x, rfl⟩
  N.symm.toContinuousLinearMap.comp ((J t z).comp N.toContinuousLinearMap)

/-- The canonical tensor square over every point of the original completed family. -/
abbrev OriginalTotalCanonicalTensorSquare
    (x : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :=
  CanonicalTensorSquare (originalTotalComplex C J N x)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem originalTotalComplex_totalInterior (p : Parameter × IntrinsicInterior.Point k M) :
    originalTotalComplex C J N (totalInterior (fun t q => C t q.val) p) =
      originalInteriorComplex C J N p := by
  have hi : (fiberEquiv (fun t q => C t q.val) p.1)
      (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2) =
      ⟨totalInterior (fun t q => C t q.val) p, rfl⟩ := by
    apply Subtype.ext
    rfl
  change N.symm.toContinuousLinearMap.comp
    ((J p.1 ((fiberEquiv (fun t q => C t q.val) p.1).symm _)).comp N.toContinuousLinearMap) = _
  rw [← hi, Equiv.symm_apply_apply]
  rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem originalTotalComplex_totalCylinder (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    originalTotalComplex C J N (totalCylinder (fun t q => C t q.val) p) =
      originalEndComplex C J N p := by
  have hi : (fiberEquiv (fun t q => C t q.val) p.1)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2) =
      ⟨totalCylinder (fun t q => C t q.val) p, rfl⟩ := by
    apply Subtype.ext
    exact sliceIn_cylinder _ _ _
  change N.symm.toContinuousLinearMap.comp
    ((J p.1 ((fiberEquiv (fun t q => C t q.val) p.1).symm _)).comp N.toContinuousLinearMap) = _
  rw [← hi, Equiv.symm_apply_apply]
  rfl

/-- Literal fiber identification over the original interior inclusion. -/
def originalTotalInteriorFiberEquiv (p : Parameter × IntrinsicInterior.Point k M) :
    OriginalTotalCanonicalTensorSquare C J N (totalInterior (fun t q => C t q.val) p) ≃L[ℂ]
      CanonicalTensorSquare (originalInteriorComplex C J N p) :=
  continuousLinearFiberCast CanonicalTensorSquare (originalTotalComplex_totalInterior C J N p)

/-- Literal fiber identification over the entire original signed cylinder. -/
def originalTotalEndFiberEquiv (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    OriginalTotalCanonicalTensorSquare C J N (totalCylinder (fun t q => C t q.val) p) ≃L[ℂ]
      CanonicalTensorSquare (originalEndComplex C J N p) :=
  continuousLinearFiberCast CanonicalTensorSquare (originalTotalComplex_totalCylinder C J N p)

variable (hδ : 0 < δ)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

variable {C J hδ hemb hboundary hzero}

namespace OriginalInteriorCanonicalChart

variable (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- The actual image of the original branch coframe domain in the completed base. -/
def totalBaseDomain : Set (TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)) :=
  totalInterior (fun t q => C t q.val) '' c.baseDomain

include hjoint in
theorem isOpen_totalBaseDomain : IsOpen c.totalBaseDomain :=
  (isOpenEmbedding_totalInterior hδ (fun t q => C t q.val) hzero hjoint).isOpenMap _ c.isOpen_baseDomain

/-- Promote the original canonical coframe coordinates through the literal
interior inclusion and its proved fiber identification. -/
def totalTensorPretrivialization : Pretrivialization ℂ (π ℂ (OriginalTotalCanonicalTensorSquare C J N)) :=
  imageCanonicalPretrivialization (totalInterior (fun t q => C t q.val)) c.baseDomain
    (originalTotalInteriorFiberEquiv C J N)
    (c.tensorCoordinateContinuousEquiv (P := N) hC hinv)
    (isOpenEmbedding_totalInterior hδ (fun t q => C t q.val) hzero hjoint) c.isOpen_baseDomain

instance totalTensorPretrivialization_complexLinear :
    (c.totalTensorPretrivialization N hjoint hC hinv).IsLinear ℂ := by
  unfold totalTensorPretrivialization
  infer_instance

instance totalTensorPretrivialization_realLinear :
    (c.totalTensorPretrivialization N hjoint hC hinv).IsLinear ℝ := by
  unfold totalTensorPretrivialization
  infer_instance

theorem totalTensorPretrivialization_apply {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain) (v : OriginalTotalCanonicalTensorSquare C J N
      (totalInterior (fun t q => C t q.val) p)) :
    c.totalTensorPretrivialization N hjoint hC hinv ⟨totalInterior (fun t q => C t q.val) p, v⟩ =
      (totalInterior (fun t q => C t q.val) p,
        c.tensorCoordinateLinearMap (P := N) p (originalTotalInteriorFiberEquiv C J N p v)) :=
  imageCanonicalPretrivialization_apply _ _ _ _ _ _ p hp v

theorem totalTensorPretrivialization_isInducing
    {x : TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)}
    (hx : x ∈ c.totalBaseDomain) :
    IsInducing (c.totalTensorPretrivialization N hjoint hC hinv ∘ Bundle.TotalSpace.mk x) :=
  imageCanonicalPretrivialization_isInducing _ _ _ _ _ _ hx

/-- The promoted coordinate is the original squared-coframe coefficient
of the same natural tensor, rather than an independently chosen scalar. -/
theorem totalTensorPretrivialization_coefficient {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain) (τ : OriginalTotalCanonicalTensorSquare C J N
      (totalInterior (fun t q => C t q.val) p)) :
    (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalInterior (fun t q => C t q.val) p, τ⟩).2 =
      squaredCoframeCoefficient (c.nativeCoframe N p)
        (canonicalSquareMap (originalTotalComplex C J N
          (totalInterior (fun t q => C t q.val) p)) τ).val := by
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hp]
  rw [← c.coefficient_squareMap]
  rw [originalTotalInteriorFiberEquiv, canonicalTensorSquareCast_squareMap]

theorem totalTensorPretrivialization_reconstruction {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain) (τ : OriginalTotalCanonicalTensorSquare C J N
      (totalInterior (fun t q => C t q.val) p)) :
    (canonicalSquareMap (originalTotalComplex C J N
      (totalInterior (fun t q => C t q.val) p)) τ).val =
      (c.totalTensorPretrivialization N hjoint hC hinv
        ⟨totalInterior (fun t q => C t q.val) p, τ⟩).2 •
          coframeSquaredGenerator (c.nativeCoframe N p) := by
  rw [c.totalTensorPretrivialization_coefficient N hjoint hC hinv hp]
  have h := c.reconstruction (P := N) hC hinv hp
    (canonicalSquareMap (originalInteriorComplex C J N p)
      (originalTotalInteriorFiberEquiv C J N p τ))
  simpa only [originalTotalInteriorFiberEquiv, canonicalTensorSquareCast_squareMap] using h

theorem totalTensorPretrivialization_coefficient_at {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain)
    {x : TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)}
    (hx : totalInterior (fun t q => C t q.val) p = x)
    (τ : OriginalTotalCanonicalTensorSquare C J N x) :
    (c.totalTensorPretrivialization N hjoint hC hinv ⟨x, τ⟩).2 =
      squaredCoframeCoefficient (c.nativeCoframe N p)
        (canonicalSquareMap (originalTotalComplex C J N x) τ).val := by
  subst x
  exact c.totalTensorPretrivialization_coefficient N hjoint hC hinv hp τ

end OriginalInteriorCanonicalChart

namespace OriginalEndCanonicalChart

variable (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))

def totalBaseDomain : Set (TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)) :=
  totalCylinder (fun t q => C t q.val) '' c.baseDomain

include hjoint in
theorem isOpen_totalBaseDomain : IsOpen c.totalBaseDomain :=
  (isOpenEmbedding_totalCylinder (fun t q => C t q.val) hjoint).isOpenMap _ c.isOpen_baseDomain

def totalTensorPretrivialization : Pretrivialization ℂ (π ℂ (OriginalTotalCanonicalTensorSquare C J N)) :=
  imageCanonicalPretrivialization (totalCylinder (fun t q => C t q.val)) c.baseDomain
    (originalTotalEndFiberEquiv C J N)
    (c.tensorCoordinateContinuousEquiv (N := N) hC hinv)
    (isOpenEmbedding_totalCylinder (fun t q => C t q.val) hjoint) c.isOpen_baseDomain

instance totalTensorPretrivialization_complexLinear :
    (c.totalTensorPretrivialization N hjoint hC hinv).IsLinear ℂ := by
  unfold totalTensorPretrivialization
  infer_instance

instance totalTensorPretrivialization_realLinear :
    (c.totalTensorPretrivialization N hjoint hC hinv).IsLinear ℝ := by
  unfold totalTensorPretrivialization
  infer_instance

theorem totalTensorPretrivialization_apply {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain) (v : OriginalTotalCanonicalTensorSquare C J N
      (totalCylinder (fun t q => C t q.val) p)) :
    c.totalTensorPretrivialization N hjoint hC hinv ⟨totalCylinder (fun t q => C t q.val) p, v⟩ =
      (totalCylinder (fun t q => C t q.val) p,
        c.tensorCoordinateLinearMap (N := N) p (originalTotalEndFiberEquiv C J N p v)) :=
  imageCanonicalPretrivialization_apply _ _ _ _ _ _ p hp v

theorem totalTensorPretrivialization_isInducing
    {x : TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)}
    (hx : x ∈ c.totalBaseDomain) :
    IsInducing (c.totalTensorPretrivialization N hjoint hC hinv ∘ Bundle.TotalSpace.mk x) :=
  imageCanonicalPretrivialization_isInducing _ _ _ _ _ _ hx

theorem totalTensorPretrivialization_coefficient {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain) (τ : OriginalTotalCanonicalTensorSquare C J N
      (totalCylinder (fun t q => C t q.val) p)) :
    (c.totalTensorPretrivialization N hjoint hC hinv
      ⟨totalCylinder (fun t q => C t q.val) p, τ⟩).2 =
      squaredCoframeCoefficient (c.nativeCoframe N p)
        (canonicalSquareMap (originalTotalComplex C J N
          (totalCylinder (fun t q => C t q.val) p)) τ).val := by
  rw [c.totalTensorPretrivialization_apply N hjoint hC hinv hp]
  rw [← c.coefficient_squareMap]
  rw [originalTotalEndFiberEquiv, canonicalTensorSquareCast_squareMap]

theorem totalTensorPretrivialization_reconstruction {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain) (τ : OriginalTotalCanonicalTensorSquare C J N
      (totalCylinder (fun t q => C t q.val) p)) :
    (canonicalSquareMap (originalTotalComplex C J N
      (totalCylinder (fun t q => C t q.val) p)) τ).val =
      (c.totalTensorPretrivialization N hjoint hC hinv
        ⟨totalCylinder (fun t q => C t q.val) p, τ⟩).2 •
          coframeSquaredGenerator (c.nativeCoframe N p) := by
  rw [c.totalTensorPretrivialization_coefficient N hjoint hC hinv hp]
  have h := c.reconstruction (N := N) hC hinv hp
    (canonicalSquareMap (originalEndComplex C J N p)
      (originalTotalEndFiberEquiv C J N p τ))
  simpa only [originalTotalEndFiberEquiv, canonicalTensorSquareCast_squareMap] using h

theorem totalTensorPretrivialization_coefficient_at {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain)
    {x : TotalSpace (fun t (q : Half δ (IntrinsicBoundary.Point k M)) => C t q.val)}
    (hx : totalCylinder (fun t q => C t q.val) p = x)
    (τ : OriginalTotalCanonicalTensorSquare C J N x) :
    (c.totalTensorPretrivialization N hjoint hC hinv ⟨x, τ⟩).2 =
      squaredCoframeCoefficient (c.nativeCoframe N p)
        (canonicalSquareMap (originalTotalComplex C J N x) τ).val := by
  subst x
  exact c.totalTensorPretrivialization_coefficient N hjoint hC hinv hp τ

end OriginalEndCanonicalChart
end FsFltz.Geometry.IntrinsicCompletionGluing
