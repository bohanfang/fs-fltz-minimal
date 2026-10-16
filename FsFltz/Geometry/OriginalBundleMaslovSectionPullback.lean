import FsFltz.Geometry.OriginalBundleCompletionMarking
import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovData

/-!
# Original local Maslov data from one independently prescribed section

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–244; and `sec:lean`, lines 788–814.
One completed ambient and one Maslov representative are prescribed at each
actual parameter. Original primitive-preserving inclusion markings pull this
same representative back to every retained local completion. The actual
completed comparison cocycle proves covariance, including every tensor slot.

These are pointwise and slice-smooth constructions. Parameterwise markings
do not imply joint smoothness; real-open section regularity on each retained
base remains a separate obligation. No grading on auxiliary cutoff parameters,
toric comparison chain, or endpoint grading homotopy is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P}
  {Z : Parameter → CompleteLiouvilleManifold (2 * n)}

namespace OriginalBundleCompletionMarkingData

variable (O : OriginalBundleCompletionMarkingData L Z) (hdim : k + 1 = 2 * n)
  {c c' : OriginalCompactChart (k := k) (M := M) (E := E)} {t t' : Parameter}

/-- The actual local inclusion marking, reindexed for the canonical-square API. -/
def localMaslovEquiv (F : LocalCompletionFamily P c t) (s : Parameter) (hs : s ∈ F.base) :
    (CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient).manifold.SmoothEquiv
      (Z s).manifold :=
  CompletedMaslovDimension.comparison hdim (F.sliceCompletion L s).ambient
    (Z s).manifold (O.localEquiv F s hs)

theorem localMaslovEquiv_primitive (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) :
    (CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient).manifold.pullback
      (Z s).manifold (O.localMaslovEquiv hdim F s hs) (Z s).primitive =
        (CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient).primitive :=
  CompletedMaslovDimension.comparison_primitive hdim (F.sliceCompletion L s).ambient
    (Z s).manifold (O.localEquiv F s hs) (Z s).primitive (O.localEquiv_primitive F s hs)

/-- The exterior-derivative law is derived from the actual preserved primitive. -/
theorem localMaslovEquiv_symplecticForm (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) :
    let X := CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient
    X.manifold.pullback (Z s).manifold (O.localMaslovEquiv hdim F s hs)
      ((Z s).manifold.exteriorDerivative (Z s).primitive) =
        X.manifold.exteriorDerivative X.primitive := by
  dsimp only
  let X := CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient
  have hd := X.manifold.exteriorDerivative_pullback (Z s).manifold
    (O.localMaslovEquiv hdim F s hs).toContMDiffMap (Z s).primitive (Z s).smooth_primitive
  exact hd.symm.trans (congrArg X.manifold.exteriorDerivative
    (O.localMaslovEquiv_primitive hdim F s hs))

/-- The cocycle is proved from the independently prescribed compact inclusion. -/
theorem localMaslovEquiv_overlap (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P c' t') (s : Parameter)
    (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (CompletedMaslovDimension.equiv hdim (F.sliceCompletion L s).ambient
      (G.sliceCompletion L s).ambient (F.overlapEquiv G L s hF hG)).trans
        (O.localMaslovEquiv hdim G s hG) = O.localMaslovEquiv hdim F s hF := by
  dsimp only [localMaslovEquiv]
  rw [CompletedMaslovDimension.equiv_trans_comparison, O.localEquiv_overlap]

/-- Pull back the prescribed representative on one actual retained slice. -/
def localMaslovRepresentative (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base)
    (σ : MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive)) :
    let X := CompletedMaslovDimension.ambient hdim (F.sliceCompletion L s).ambient
    MaslovRepresentative X.manifold (X.manifold.exteriorDerivative X.primitive) :=
  σ.pullbackTo (O.localMaslovEquiv hdim F s hs)
    (O.localMaslovEquiv_symplecticForm hdim F s hs)

/-- One independently prescribed section produces all original local fields.
Overlap covariance is a theorem of the actual maps, not an input field. -/
def originalMaslovData
    (σ : ∀ s, MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive)) :
    OriginalLocalCompletionMaslovData P L hdim where
  J := fun c t ht s hs =>
    (O.localMaslovRepresentative hdim (L.localCompletionFamily c t ht) s hs (σ s)).J
  tensor := fun c t ht s hs =>
    (O.localMaslovRepresentative hdim (L.localCompletionFamily c t ht) s hs (σ s)).tensor
  compatible := fun c t ht s hs =>
    (O.localMaslovRepresentative hdim (L.localCompletionFamily c t ht) s hs (σ s)).compatible
  canonical := fun c t ht s hs =>
    (O.localMaslovRepresentative hdim (L.localCompletionFamily c t ht) s hs (σ s)).canonical
  nowhereZero := fun c t ht s hs =>
    (O.localMaslovRepresentative hdim (L.localCompletionFamily c t ht) s hs (σ s)).nowhereZero
  covarianceJ := by
    intro c d t u ht hu s hs hs'
    change pullbackAlmostComplex _ _ (O.localMaslovEquiv hdim _ s hs) (σ s).J =
      pullbackAlmostComplex _ _ (localMaslovOverlap hdim L c d t u ht hu s hs hs')
        (pullbackAlmostComplex _ _ (O.localMaslovEquiv hdim _ s hs') (σ s).J)
    rw [← pullbackAlmostComplex_trans, O.localMaslovEquiv_overlap]
  covarianceTensor := by
    intro c d t u ht hu s hs hs'
    change pullbackSquaredTensor _ _ (O.localMaslovEquiv hdim _ s hs) (σ s).tensor =
      pullbackSquaredTensor _ _ (localMaslovOverlap hdim L c d t u ht hu s hs hs')
        (pullbackSquaredTensor _ _ (O.localMaslovEquiv hdim _ s hs') (σ s).tensor)
    rw [← pullbackSquaredTensor_trans, O.localMaslovEquiv_overlap]

variable (σ : ∀ s, MaslovRepresentative (Z s).manifold
  ((Z s).manifold.exteriorDerivative (Z s).primitive))

@[simp]
theorem originalMaslovData_J (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim σ).J c t ht s hs =
      pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold (Z s).manifold
        (O.localMaslovEquiv hdim (L.localCompletionFamily c t ht) s hs) (σ s).J := rfl

@[simp]
theorem originalMaslovData_tensor (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim σ).tensor c t ht s hs =
      pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold (Z s).manifold
        (O.localMaslovEquiv hdim (L.localCompletionFamily c t ht) s hs) (σ s).tensor := rfl

/-- Inverting any retained original marking recovers the same prescribed
field and full tensor on the entire target, before choosing a realization. -/
theorem originalMaslovData_recovers_prescribed
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (Z s).manifold (localMaslovAmbient hdim L c t ht s).manifold
      (O.localMaslovEquiv hdim (L.localCompletionFamily c t ht) s hs).symm
      ((O.originalMaslovData hdim σ).J c t ht s hs) = (σ s).J ∧
    pullbackSquaredTensor (Z s).manifold (localMaslovAmbient hdim L c t ht s).manifold
      (O.localMaslovEquiv hdim (L.localCompletionFamily c t ht) s hs).symm
      ((O.originalMaslovData hdim σ).tensor c t ht s hs) = (σ s).tensor := by
  constructor
  · rw [O.originalMaslovData_J, ← pullbackAlmostComplex_trans,
      Diffeomorph.symm_trans_self, pullbackAlmostComplex_refl]
  · rw [O.originalMaslovData_tensor, ← pullbackSquaredTensor_trans,
      Diffeomorph.symm_trans_self, pullbackSquaredTensor_refl]

section EndpointRecovery

variable [NeZero n]
  (F : LocalCompletionFamily P c t) (g : Trivialization M (π M E))
  (s : Parameter) (hs : s ∈ F.base) (hg : s ∈ g.baseSet)
  (D : LiouvilleDomain (2 * n)) (C : Completion D)
  (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M D.domain.Point ∞)
  (a : LocalCompletionFamily.EndpointSliceComparison F L g s D C eM)

/-- The exact endpoint marking preserves the actual symplectic form. -/
theorem endpointMarking_symplecticForm :
    C.ambient.manifold.pullback (Z s).manifold
      (O.endpointMarking F g s hs hg D C eM a).equiv
      ((Z s).manifold.exteriorDerivative (Z s).primitive) =
        C.ambient.manifold.exteriorDerivative C.ambient.primitive := by
  have hd := C.ambient.manifold.exteriorDerivative_pullback (Z s).manifold
    (O.endpointMarking F g s hs hg D C eM a).equiv.toContMDiffMap
    (Z s).primitive (Z s).smooth_primitive
  exact hd.symm.trans (congrArg C.ambient.manifold.exteriorDerivative
    (O.endpointMarking F g s hs hg D C eM a).primitive)

/-- The original prescribed section on this exact retained endpoint. -/
def endpointMaslovRepresentative :
    MaslovRepresentative C.ambient.manifold
      (C.ambient.manifold.exteriorDerivative C.ambient.primitive) :=
  (σ s).pullbackTo (O.endpointMarking F g s hs hg D C eM a).equiv
    (O.endpointMarking_symplecticForm F g s hs hg D C eM a)

/-- One chosen endpoint marking recovers the original data on every retained
chart through that chart's actual whole-completion comparison. -/
theorem endpointMaslovRepresentative_recovers_all_charts
    (c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t' : Parameter) (ht' : t' ∈ c'.val.baseSet)
    (hG : s ∈ (L.localCompletionFamily c' t' ht').base)
    (b : LocalCompletionFamily.EndpointSliceComparison
      (L.localCompletionFamily c' t' ht') L g s D C eM) :
    let e := CompletedMaslovDimension.comparison hdim
      ((L.localCompletionFamily c' t' ht').sliceCompletion L s).ambient C.ambient.manifold b.equiv
    pullbackAlmostComplex (localMaslovAmbient hdim L c' t' ht' s).manifold
      C.ambient.manifold e (O.endpointMaslovRepresentative σ F g s hs hg D C eM a).J =
        (O.originalMaslovData hdim σ).J c' t' ht' s hG ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c' t' ht' s).manifold
      C.ambient.manifold e (O.endpointMaslovRepresentative σ F g s hs hg D C eM a).tensor =
        (O.originalMaslovData hdim σ).tensor c' t' ht' s hG := by
  let G := L.localCompletionFamily c' t' ht'
  have h := congrArg (CompletedMaslovDimension.comparison hdim (G.sliceCompletion L s).ambient
      (Z s).manifold)
    (O.endpointMarking_recovers_all_charts F g s hs hg D C eM a G hG b)
  rw [← CompletedMaslovDimension.comparison_trans] at h
  dsimp only
  constructor
  · change pullbackAlmostComplex _ _ _ (pullbackAlmostComplex _ _ _ (σ s).J) = _
    rw [← pullbackAlmostComplex_trans, h]
    rfl
  · change pullbackSquaredTensor _ _ _ (pullbackSquaredTensor _ _ _ (σ s).tensor) = _
    rw [← pullbackSquaredTensor_trans, h]
    rfl

/-- The endpoint representative is independent of the retained chart and
comparison used to descend the original prescribed inclusion marking. -/
theorem endpointMaslovRepresentative_choice_independent
    (G : LocalCompletionFamily P c' t') (hG : s ∈ G.base)
    (b : LocalCompletionFamily.EndpointSliceComparison G L g s D C eM) :
    O.endpointMaslovRepresentative σ F g s hs hg D C eM a =
      O.endpointMaslovRepresentative σ G g s hG hg D C eM b := by
  apply MaslovRepresentative.ext
  · change pullbackAlmostComplex _ _ _ (σ s).J = pullbackAlmostComplex _ _ _ (σ s).J
    rw [O.endpointMarking_choice_independent F g s hs hg D C eM a G hG b]
  · change pullbackSquaredTensor _ _ _ (σ s).tensor = pullbackSquaredTensor _ _ _ (σ s).tensor
    rw [O.endpointMarking_choice_independent F g s hs hg D C eM a G hG b]

end EndpointRecovery

end OriginalBundleCompletionMarkingData

end FsFltz.Geometry.IntrinsicSmoothBundle
