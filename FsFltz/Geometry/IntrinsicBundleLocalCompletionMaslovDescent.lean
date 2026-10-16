import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovData
import FsFltz.Geometry.IntrinsicBundleLocalCompletionComparisonCoherence
import FsFltz.Geometry.CanonicalSquareBundle

/-!
# Pointwise descent of preselected original local completed data

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–243;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
Original overlap covariance and the proved coherence of the exact slice
comparisons descend the preselected complex field and full canonical-square
tensor to the same retained pair deformation. Their recovery is literal in
every original completed local chart, including charts at zero and one.

This module proves pointwise descent, compatibility and nonvanishing.
Joint real smoothness is a separate producer; no Maslov family, graded chain,
or geometric target is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

private theorem inverse_overlap {n : ℕ} (X Y Z : SmoothManifold (2 * n))
    (a : X.SmoothEquiv Z) (b : Y.SmoothEquiv Z) (o : X.SmoothEquiv Y)
    (h : o.trans b = a) : a.symm.trans o = b.symm := by
  apply Diffeomorph.ext
  intro z
  apply b.injective
  change b (o (a.symm z)) = b (b.symm z)
  have hh := congrArg (fun f : X.SmoothEquiv Z => f (a.symm z)) h
  change b (o (a.symm z)) = a (a.symm z) at hh
  rw [hh, a.apply_symm_apply, b.apply_symm_apply]

private theorem inverse_covarianceJ {n : ℕ} (X Y Z : SmoothManifold (2 * n))
    (a : X.SmoothEquiv Z) (b : Y.SmoothEquiv Z) (o : X.SmoothEquiv Y)
    (h : o.trans b = a) (J : AlmostComplexField X) (J' : AlmostComplexField Y)
    (hJ : J = pullbackAlmostComplex X Y o J') :
    pullbackAlmostComplex Z X a.symm J = pullbackAlmostComplex Z Y b.symm J' := by
  rw [hJ, ← pullbackAlmostComplex_trans, inverse_overlap X Y Z a b o h]

private theorem inverse_covarianceTensor {n : ℕ} (X Y Z : SmoothManifold (2 * n))
    (a : X.SmoothEquiv Z) (b : Y.SmoothEquiv Z) (o : X.SmoothEquiv Y)
    (h : o.trans b = a) (T : X.Point → SquaredCanonicalTensor n)
    (T' : Y.Point → SquaredCanonicalTensor n)
    (hT : T = pullbackSquaredTensor X Y o T') :
    pullbackSquaredTensor Z X a.symm T = pullbackSquaredTensor Z Y b.symm T' := by
  rw [hT, ← pullbackSquaredTensor_trans, inverse_overlap X Y Z a b o h]

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

/-- A timewise original chart used only to define a pointwise field.
Every other original chart is recovered below; no smoothness of this choice
is asserted or needed for pointwise descent. -/
def originalMaslovChartAt (s : Parameter) :
    OriginalCompactChart (k := k) (M := M) (E := E) :=
  ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩

theorem originalMaslovChartAt_mem (s : Parameter) :
    s ∈ (originalMaslovChartAt (k := k) (M := M) (E := E) s).val.baseSet :=
  mem_baseSet_trivializationAt _ _ _

variable
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- Reindex the actual produced comparison, using the exact original local
completion and this deformation's fixed source presentation. -/
def localMaslovComparison
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (localMaslovAmbient hdim L c t ht s).manifold.SmoothEquiv
      Q.source.ambientCompletion.ambient.manifold :=
  let F := L.localCompletionFamily c t ht
  CompletedMaslovDimension.comparison hdim (F.sliceCompletion L s).ambient
    Q.source.ambientCompletion.ambient.manifold
    (F.ambientSourceSliceEquiv L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc))

/-- The comparison coherence is derived from the original overlaps and
primitive uniqueness, before any section covariance is consumed. -/
theorem localMaslovComparison_overlap
    (c d : OriginalCompactChart (k := k) (M := M) (E := E))
    (t u : Parameter) (ht : t ∈ c.val.baseSet) (hu : u ∈ d.val.baseSet)
    (s : Parameter) (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (hs' : s ∈ (L.localCompletionFamily d u hu).base) :
    (localMaslovOverlap hdim L c d t u ht hu s hs hs').trans
      (localMaslovComparison g hg hbase Q eAs hp hc d u hu s hs') =
        localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs := by
  let F := L.localCompletionFamily c t ht
  let G := L.localCompletionFamily d u hu
  let a := F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc
  let b := G.ambientEndpointSliceComparison L g hg hbase s hs' Q hdim eAs hp hc
  have h : (F.overlapEquiv G L s hs hs').trans
      (G.ambientSourceSliceEquiv L g s Q eAs b) =
        F.ambientSourceSliceEquiv L g s Q eAs a := by
    apply Diffeomorph.ext
    exact F.ambientSourceSliceEquiv_overlap G L g s hs hs' Q eAs a b
  have hh := congrArg
    (CompletedMaslovDimension.comparison hdim (F.sliceCompletion L s).ambient
      Q.source.ambientCompletion.ambient.manifold) h
  rw [← CompletedMaslovDimension.equiv_trans_comparison] at hh
  exact hh

/-- The reindexed inverse comparison preserves the actual varying primitive. -/
theorem localMaslovComparison_inverse_primitive
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    Q.source.ambientCompletion.ambient.manifold.pullback
      (localMaslovAmbient hdim L c t ht s).manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs).symm
      (localMaslovAmbient hdim L c t ht s).primitive = Q.completedPrimitive s := by
  let F := L.localCompletionFamily c t ht
  exact CompletedMaslovDimension.comparison_inverse_primitive hdim
    (F.sliceCompletion L s).ambient Q.source.ambientCompletion.ambient.manifold
    (F.ambientSourceSliceEquiv L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc))
    (Q.completedPrimitive s)
    (F.ambientSourceSliceEquiv_inverse_primitive L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc))

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)

/-- Descend the original field by the inverse of the produced comparison.
The data `S` have already been chosen independently of `g` and `Q`. -/
def descendedJ (s : Parameter) : AlmostComplexField Q.source.ambientCompletion.ambient.manifold :=
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  pullbackAlmostComplex Q.source.ambientCompletion.ambient.manifold
    (localMaslovAmbient hdim L c s ht s).manifold
    (localMaslovComparison g hg hbase Q eAs hp hc c s ht s F.base_mem).symm
    (S.J c s ht s F.base_mem)

/-- Descend the whole tensor, retaining both labelled blocks and every slot. -/
def descendedTensor (s : Parameter) :
    Q.source.ambientCompletion.ambient.manifold.Point → SquaredCanonicalTensor n :=
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  pullbackSquaredTensor Q.source.ambientCompletion.ambient.manifold
    (localMaslovAmbient hdim L c s ht s).manifold
    (localMaslovComparison g hg hbase Q eAs hp hc c s ht s F.base_mem).symm
    (S.tensor c s ht s F.base_mem)

/-- Transport from any original completed local chart gives the same field.
Original section covariance and independently proved comparison coherence
are both consumed by this proof. -/
theorem descendedJ_eq_inverse
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    S.descendedJ g hg hbase Q eAs hp hc s =
      pullbackAlmostComplex Q.source.ambientCompletion.ambient.manifold
        (localMaslovAmbient hdim L c t ht s).manifold
        (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs).symm
        (S.J c t ht s hs) := by
  let d := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let hd := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let G := L.localCompletionFamily d s hd
  exact inverse_covarianceJ
    (localMaslovAmbient hdim L d s hd s).manifold
    (localMaslovAmbient hdim L c t ht s).manifold
    Q.source.ambientCompletion.ambient.manifold
    (localMaslovComparison g hg hbase Q eAs hp hc d s hd s G.base_mem)
    (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
    (localMaslovOverlap hdim L d c s t hd ht s G.base_mem hs)
    (localMaslovComparison_overlap g hg hbase Q eAs hp hc d c s t hd ht s G.base_mem hs)
    (S.J d s hd s G.base_mem) (S.J c t ht s hs)
    (S.covarianceJ d c s t hd ht s G.base_mem hs)

/-- Transport from any original completed local chart gives the same full
tensor, including its values on arbitrary vectors in all labelled slots. -/
theorem descendedTensor_eq_inverse
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    S.descendedTensor g hg hbase Q eAs hp hc s =
      pullbackSquaredTensor Q.source.ambientCompletion.ambient.manifold
        (localMaslovAmbient hdim L c t ht s).manifold
        (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs).symm
        (S.tensor c t ht s hs) := by
  let d := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let hd := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let G := L.localCompletionFamily d s hd
  exact inverse_covarianceTensor
    (localMaslovAmbient hdim L d s hd s).manifold
    (localMaslovAmbient hdim L c t ht s).manifold
    Q.source.ambientCompletion.ambient.manifold
    (localMaslovComparison g hg hbase Q eAs hp hc d s hd s G.base_mem)
    (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
    (localMaslovOverlap hdim L d c s t hd ht s G.base_mem hs)
    (localMaslovComparison_overlap g hg hbase Q eAs hp hc d c s t hd ht s G.base_mem hs)
    (S.tensor d s hd s G.base_mem) (S.tensor c t ht s hs)
    (S.covarianceTensor d c s t hd ht s G.base_mem hs)

/-- Every original chart recovers its preselected almost complex field
literally, with the derivative of the actual produced comparison. -/
theorem pullback_descendedJ
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
      (S.descendedJ g hg hbase Q eAs hp hc s) = S.J c t ht s hs := by
  rw [S.descendedJ_eq_inverse g hg hbase Q eAs hp hc c t ht s hs,
    ← pullbackAlmostComplex_trans, Diffeomorph.self_trans_symm, pullbackAlmostComplex_refl]

/-- Every original chart recovers the preselected whole tensor literally. -/
theorem pullback_descendedTensor
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
      (S.descendedTensor g hg hbase Q eAs hp hc s) = S.tensor c t ht s hs := by
  rw [S.descendedTensor_eq_inverse g hg hbase Q eAs hp hc c t ht s hs,
    ← pullbackSquaredTensor_trans, Diffeomorph.self_trans_symm, pullbackSquaredTensor_refl]

/-- Exact recovery evaluated on arbitrary vectors in both labelled blocks. -/
theorem pullback_descendedTensor_apply
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (x : (localMaslovAmbient hdim L c t ht s).manifold.Point)
    (v : Fin n ⊕ Fin n → Model (2 * n)) :
    S.descendedTensor g hg hbase Q eAs hp hc s
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs) x (v i)) =
      S.tensor c t ht s hs x v :=
  congrArg (fun T => T x v) (S.pullback_descendedTensor g hg hbase Q eAs hp hc c t ht s hs)

/-- Exact recovery at the initial endpoint in every original chart retaining
that endpoint. No interval interior restriction is introduced. -/
theorem pullback_descended_zero
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (hs : parameterZero ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht parameterZero).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterZero hs)
      (S.descendedJ g hg hbase Q eAs hp hc parameterZero) = S.J c t ht parameterZero hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht parameterZero).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterZero hs)
      (S.descendedTensor g hg hbase Q eAs hp hc parameterZero) =
        S.tensor c t ht parameterZero hs :=
  ⟨S.pullback_descendedJ g hg hbase Q eAs hp hc c t ht parameterZero hs,
    S.pullback_descendedTensor g hg hbase Q eAs hp hc c t ht parameterZero hs⟩

/-- Exact recovery at the terminal endpoint in every original chart retaining
that endpoint, through the same comparison used throughout the family. -/
theorem pullback_descended_one
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (hs : parameterOne ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht parameterOne).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterOne hs)
      (S.descendedJ g hg hbase Q eAs hp hc parameterOne) = S.J c t ht parameterOne hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht parameterOne).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterOne hs)
      (S.descendedTensor g hg hbase Q eAs hp hc parameterOne) =
        S.tensor c t ht parameterOne hs :=
  ⟨S.pullback_descendedJ g hg hbase Q eAs hp hc c t ht parameterOne hs,
    S.pullback_descendedTensor g hg hbase Q eAs hp hc c t ht parameterOne hs⟩

/-- The descended field is uniquely determined by literal recovery in the
original local charts. A chart centered at the actual parameter suffices. -/
theorem descendedJ_unique (s : Parameter)
    (J : AlmostComplexField Q.source.ambientCompletion.ambient.manifold)
    (hJ : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (hs : s ∈ (L.localCompletionFamily c t ht).base),
      pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold
        Q.source.ambientCompletion.ambient.manifold
        (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs) J = S.J c t ht s hs) :
    J = S.descendedJ g hg hbase Q eAs hp hc s := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  let e := localMaslovComparison (hdim := hdim) g hg hbase Q eAs hp hc c s ht s F.base_mem
  have h := congrArg
    (pullbackAlmostComplex Q.source.ambientCompletion.ambient.manifold
      (localMaslovAmbient hdim L c s ht s).manifold e.symm) (hJ c s ht F.base_mem)
  rw [← pullbackAlmostComplex_trans, Diffeomorph.symm_trans_self, pullbackAlmostComplex_refl] at h
  exact h

/-- The descended whole tensor is uniquely determined by the original local
data; this is equality of tensors rather than of a chosen coefficient. -/
theorem descendedTensor_unique (s : Parameter)
    (T : Q.source.ambientCompletion.ambient.manifold.Point → SquaredCanonicalTensor n)
    (hT : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (hs : s ∈ (L.localCompletionFamily c t ht).base),
      pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold
        Q.source.ambientCompletion.ambient.manifold
        (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs) T = S.tensor c t ht s hs) :
    T = S.descendedTensor g hg hbase Q eAs hp hc s := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  let e := localMaslovComparison (hdim := hdim) g hg hbase Q eAs hp hc c s ht s F.base_mem
  have h := congrArg
    (pullbackSquaredTensor Q.source.ambientCompletion.ambient.manifold
      (localMaslovAmbient hdim L c s ht s).manifold e.symm) (hT c s ht F.base_mem)
  rw [← pullbackSquaredTensor_trans, Diffeomorph.symm_trans_self, pullbackSquaredTensor_refl] at h
  exact h

/-- Primitive preservation identifies the transported two-form with this
same deformation's completed primitive, so all compatibility equations hold. -/
theorem descendedJ_compatible (s : Parameter) :
    IsCompatibleAlmostComplex Q.source.ambientCompletion.ambient.manifold
      (Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive s))
      (S.descendedJ g hg hbase Q eAs hp hc s) := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  let X := localMaslovAmbient hdim L c s ht s
  let N := Q.source.ambientCompletion.ambient.manifold
  let e := localMaslovComparison (hdim := hdim) g hg hbase Q eAs hp hc c s ht s F.base_mem
  have hprim : N.pullback X.manifold e.symm X.primitive = Q.completedPrimitive s :=
    localMaslovComparison_inverse_primitive g hg hbase Q eAs hp hc c s ht s F.base_mem
  have hd : N.exteriorDerivative (Q.completedPrimitive s) =
      N.pullback X.manifold e.symm (X.manifold.exteriorDerivative X.primitive) := by
    rw [← hprim]
    exact N.exteriorDerivative_pullback X.manifold e.symm.toContMDiffMap X.primitive X.smooth_primitive
  rw [hd]
  exact isCompatibleAlmostComplex_pullback N X.manifold e.symm
    (X.manifold.exteriorDerivative X.primitive) (S.J c s ht s F.base_mem)
    (S.compatible c s ht s F.base_mem)

/-- The full descended tensor is in the squared complex canonical fiber
for the descended field at every reference completed point. -/
theorem descendedTensor_canonical (s : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    IsSquaredCanonicalTensor (S.descendedJ g hg hbase Q eAs hp hc s x)
      (S.descendedTensor g hg hbase Q eAs hp hc s x) := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  exact pullbackSquaredTensor_canonical Q.source.ambientCompletion.ambient.manifold
    (localMaslovAmbient hdim L c s ht s).manifold
    (localMaslovComparison g hg hbase Q eAs hp hc c s ht s F.base_mem).symm
    (S.J c s ht s F.base_mem) (S.tensor c s ht s F.base_mem)
    (S.canonical c s ht s F.base_mem) x

/-- Nonvanishing survives the derivative of the same produced inverse
comparison on the whole completion. -/
theorem descendedTensor_ne_zero (s : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    S.descendedTensor g hg hbase Q eAs hp hc s x ≠ 0 := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  let F := L.localCompletionFamily c s ht
  exact pullbackSquaredTensor_ne_zero Q.source.ambientCompletion.ambient.manifold
    (localMaslovAmbient hdim L c s ht s).manifold
    (localMaslovComparison g hg hbase Q eAs hp hc c s ht s F.base_mem).symm
    (S.tensor c s ht s F.base_mem) (S.nowhereZero c s ht s F.base_mem) x

/-- The actual canonical tensor-product square recovered from the descended
full two-block tensor. This is a pointwise section; joint smoothness is still
a separate obligation. -/
def descendedTensorSquareSection (s : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    CanonicalTensorSquare (S.descendedJ g hg hbase Q eAs hp hc s x) :=
  (canonicalSquareEquivOfComplexStructure
    (S.descendedJ g hg hbase Q eAs hp hc s x)
    ((S.descendedJ_compatible g hg hbase Q eAs hp hc s).2.1 x)).symm
    ⟨S.descendedTensor g hg hbase Q eAs hp hc s x,
      S.descendedTensor_canonical g hg hbase Q eAs hp hc s x⟩

/-- Natural tensor-square multiplication gives exactly the descended full
tensor, without selecting a scalar coefficient or a square root. -/
theorem canonicalSquareMap_descendedTensorSquareSection (s : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    canonicalSquareMap (S.descendedJ g hg hbase Q eAs hp hc s x)
      (S.descendedTensorSquareSection g hg hbase Q eAs hp hc s x) =
        ⟨S.descendedTensor g hg hbase Q eAs hp hc s x,
          S.descendedTensor_canonical g hg hbase Q eAs hp hc s x⟩ :=
  (canonicalSquareEquivOfComplexStructure
    (S.descendedJ g hg hbase Q eAs hp hc s x)
    ((S.descendedJ_compatible g hg hbase Q eAs hp hc s).2.1 x)).apply_symm_apply _

theorem descendedTensorSquareSection_ne_zero (s : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    S.descendedTensorSquareSection g hg hbase Q eAs hp hc s x ≠ 0 := by
  intro hz
  have h := S.canonicalSquareMap_descendedTensorSquareSection g hg hbase Q eAs hp hc s x
  rw [hz, map_zero] at h
  exact S.descendedTensor_ne_zero g hg hbase Q eAs hp hc s x (congrArg Subtype.val h).symm

/-- The natural full tensor of the recovered tensor-square section pulls
back to the originally preselected tensor in every local chart. -/
theorem pullback_descendedTensorSquareSection
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold
      Q.source.ambientCompletion.ambient.manifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
      (fun x => (canonicalSquareMap (S.descendedJ g hg hbase Q eAs hp hc s x)
        (S.descendedTensorSquareSection g hg hbase Q eAs hp hc s x)).val) =
          S.tensor c t ht s hs := by
  simp_rw [S.canonicalSquareMap_descendedTensorSquareSection g hg hbase Q eAs hp hc s]
  exact S.pullback_descendedTensor g hg hbase Q eAs hp hc c t ht s hs

end OriginalLocalCompletionMaslovData

end FsFltz.Geometry.IntrinsicSmoothBundle
