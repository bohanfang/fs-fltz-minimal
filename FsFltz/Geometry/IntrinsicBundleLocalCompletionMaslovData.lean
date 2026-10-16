import FsFltz.Geometry.IntrinsicBundleLocalCompletionOverlap
import FsFltz.Geometry.MaslovClassPullback

/-!
# Preselected data on the original completed local atlas

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–243;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The fields below live on the original locally constructed completed charts,
before a represented pair deformation is chosen. Their parameter domain is
the retained base of each chart, including either interval endpoint.
Covariance uses the actual original completed overlap on every point and
every tensor slot. Auxiliary cutoff parameters impose no grading obligation.

This is data for pointwise descent. Joint smoothness, homotopy classes and
the geometric target remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

namespace CompletedMaslovDimension

/-- Reindex a completed ambient by an equality of dimensions. This changes
only the index used by the existing canonical tensor API. -/
def ambient {d e : ℕ} (h : d = e) (X : CompleteLiouvilleManifold d) :
    CompleteLiouvilleManifold e := h ▸ X

/-- The actual original completed overlap, with the same dimension reindexing
on both sides. -/
def equiv {d e : ℕ} (h : d = e) (X Y : CompleteLiouvilleManifold d)
    (f : X.manifold.SmoothEquiv Y.manifold) :
    (ambient h X).manifold.SmoothEquiv (ambient h Y).manifold := by
  subst e
  exact f

/-- The actual comparison with an ambient already of the target dimension. -/
def comparison {d e : ℕ} (h : d = e) (X : CompleteLiouvilleManifold d)
    (Y : SmoothManifold e) (f : X.manifold.SmoothEquiv Y) :
    (ambient h X).manifold.SmoothEquiv Y := by
  subst e
  exact f

/-- Dimension reindexing retains the proved primitive equation. -/
theorem comparison_primitive {d e : ℕ} (h : d = e)
    (X : CompleteLiouvilleManifold d) (Y : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y) (β : Y.Form 1)
    (hf : X.manifold.pullback Y f β = X.primitive) :
    (ambient h X).manifold.pullback Y (comparison h X Y f) β =
      (ambient h X).primitive := by
  subst e
  exact hf

/-- Reindexing the source of a comparison commutes with composition. -/
theorem comparison_trans {d e : ℕ} (h : d = e)
    (X : CompleteLiouvilleManifold d) (Y Z : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y) (g : Y.SmoothEquiv Z) :
    (comparison h X Y f).trans g = comparison h X Z (f.trans g) := by
  subst e
  rfl

theorem equiv_trans_comparison {d e : ℕ} (h : d = e)
    (X Y : CompleteLiouvilleManifold d) (Z : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y.manifold) (g : Y.manifold.SmoothEquiv Z) :
    (equiv h X Y f).trans (comparison h Y Z g) =
      comparison h X Z (f.trans g) := by
  subst e
  rfl

theorem comparison_inverse_primitive {d e : ℕ} (h : d = e)
    (X : CompleteLiouvilleManifold d) (Y : SmoothManifold e)
    (f : X.manifold.SmoothEquiv Y) (α : Y.Form 1)
    (hf : Y.pullback X.manifold f.symm X.primitive = α) :
    Y.pullback (ambient h X).manifold (comparison h X Y f).symm
      (ambient h X).primitive = α := by
  subst e
  exact hf

end CompletedMaslovDimension

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}

/-- The original retained local completed ambient, before any global pair
realization is selected. -/
abbrev localMaslovAmbient (hdim : k + 1 = 2 * n) (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter) :=
  CompletedMaslovDimension.ambient hdim
    (((L.localCompletionFamily c t ht).sliceCompletion L s).ambient)

/-- The exact original overlap on the retained local completions. -/
abbrev localMaslovOverlap (hdim : k + 1 = 2 * n) (L : OriginalBundleLiouvilleLaws P)
    (c d : OriginalCompactChart (k := k) (M := M) (E := E))
    (t u : Parameter) (ht : t ∈ c.val.baseSet) (hu : u ∈ d.val.baseSet)
    (s : Parameter) (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (hs' : s ∈ (L.localCompletionFamily d u hu).base) :=
  CompletedMaslovDimension.equiv hdim
    (((L.localCompletionFamily c t ht).sliceCompletion L s).ambient)
    (((L.localCompletionFamily d u hu).sliceCompletion L s).ambient)
    ((L.localCompletionFamily c t ht).overlapEquiv
      (L.localCompletionFamily d u hu) L s hs hs')

/-- Independently preselected almost complex fields and full canonical-square
tensors on the original completed local atlas. All obligations are restricted
to actual retained parameters. Neither a represented family nor its descended
fields occur in the data or covariance laws. -/
structure OriginalLocalCompletionMaslovData (P : BundlePrimitiveData (k := k) (M := M) E)
    (L : OriginalBundleLiouvilleLaws P) (hdim : k + 1 = 2 * n) where
  J : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter),
    s ∈ (L.localCompletionFamily c t ht).base →
      AlmostComplexField (localMaslovAmbient hdim L c t ht s).manifold
  tensor : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter),
    s ∈ (L.localCompletionFamily c t ht).base →
      (localMaslovAmbient hdim L c t ht s).manifold.Point → SquaredCanonicalTensor n
  compatible : ∀ c t ht s hs,
    IsCompatibleAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold
      ((localMaslovAmbient hdim L c t ht s).manifold.exteriorDerivative
        (localMaslovAmbient hdim L c t ht s).primitive) (J c t ht s hs)
  canonical : ∀ c t ht s hs x,
    IsSquaredCanonicalTensor (J c t ht s hs x) (tensor c t ht s hs x)
  nowhereZero : ∀ c t ht s hs x, tensor c t ht s hs x ≠ 0
  covarianceJ : ∀ c d t u ht hu s hs hs',
    J c t ht s hs = pullbackAlmostComplex
      (localMaslovAmbient hdim L c t ht s).manifold
      (localMaslovAmbient hdim L d u hu s).manifold
      (localMaslovOverlap hdim L c d t u ht hu s hs hs') (J d u hu s hs')
  covarianceTensor : ∀ c d t u ht hu s hs hs',
    tensor c t ht s hs = pullbackSquaredTensor
      (localMaslovAmbient hdim L c t ht s).manifold
      (localMaslovAmbient hdim L d u hu s).manifold
      (localMaslovOverlap hdim L c d t u ht hu s hs hs') (tensor d u hu s hs')

end FsFltz.Geometry.IntrinsicSmoothBundle
