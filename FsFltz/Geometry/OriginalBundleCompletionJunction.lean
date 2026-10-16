import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovDescent
import FsFltz.Geometry.OriginalNativeCompletionJunctionGrading

/-!
# Original local bundle junctions on independently retained endpoints

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–194;
`def:maslov`, lines 225–234; and `sec:lean`, lines 788–814.
The strict map and its boundary map, arbitrary real shift and whole-ribbon
square are supplied on independently chosen original local completions.
The actual original-to-endpoint comparison constructs the native junction
on the retained endpoint domains and completions. No represented pair or
comparison occurs in the original geometric data.

These are conditional foundational producers. Original strict junctions
and the endpoint realization laws are premises; their toric existence,
the finite comparison chain and the endpoint core equality remain pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

namespace CompletedMaslovDimension

/-- The same original end map after the ambient dimension is reindexed. -/
def endMap {d e : ℕ} (h : d = e) {D : LiouvilleDomain d} (C : Completion D) :
    D.domain.boundary.Point × ℝ → (ambient h C.ambient).manifold.Point := by
  subst e
  exact C.endMap

/-- Dimension reindexing retains the whole original end square. -/
theorem comparison_end {d e : ℕ} (h : d = e)
    {D : LiouvilleDomain d} (C : Completion D) (Y : SmoothManifold e)
    (f : C.ambient.manifold.SmoothEquiv Y) (z : D.domain.boundary.Point × ℝ) :
    comparison h C.ambient Y f (endMap h C z) = f (C.endMap z) := by
  subst e
  rfl

end CompletedMaslovDimension

section OriginalRibbonEndpoint

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {EM : Parameter → Type*} [∀ u, TopologicalSpace (EM u)]
  [TopologicalSpace (TotalSpace M EM)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]
  {PM : BundlePrimitiveData (k := k) (M := M) EM}
  {cM : OriginalCompactChart (k := k) (M := M) (E := EM)}
  {t s : Parameter}
  (gM : Trivialization M (π M EM))
  (hgM : CompatibleTrivialization (𝓡∂ (k + 1)) EM gM)
  (hbaseM : gM.baseSet = univ) (hsM : s ∈ cM.val.baseSet)
  (F : PairDeformation n)
  (eMs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (F.pair u).ribbonDomain.domain.Point ∞)

/-- The actual original ribbon chart maps to the retained compact endpoint
through its original bundle transition, followed by the existing native
compact correspondence. -/
def originalRibbonEndpointEquiv :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
      (F.pair s).ribbonDomain.domain.Point ∞ :=
  (transitionDiffeomorphOfCompatible cM.val gM
    (compatibleTrivialization_of_mem cM.property) hgM
    ⟨hsM, by rw [hbaseM]; exact mem_univ s⟩).trans (eMs s)

variable
  (hpM : ∀ u x, ((F.pair u).ribbonDomain.liouville.primitive (eMs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs u y).val) x) =
      PM.formInTrivialization gM u x)

include hpM

/-- The original full covector is recovered by bundle covariance and the
chain rule on the actual original compact transition. -/
theorem originalRibbonEndpointEquiv_primitive (x : M) :
    ((F.pair s).ribbonDomain.liouville.primitive
      (originalRibbonEndpointEquiv gM hgM hbaseM hsM F eMs x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
        (fun y => (originalRibbonEndpointEquiv gM hgM hbaseM hsM F eMs y).val) x) = PM.form cM s x := by
  let q := transitionDiffeomorphOfCompatible cM.val gM
    (compatibleTrivialization_of_mem cM.property) hgM
    ⟨hsM, by rw [hbaseM]; exact mem_univ s⟩
  have hc := PM.formInTrivialization_covariance cM.val gM
    (compatibleTrivialization_of_mem cM.property) hgM
    ⟨hsM, by rw [hbaseM]; exact mem_univ s⟩
  rw [PM.formInTrivialization_eq_original cM.val cM.property hsM] at hc
  have hd := mfderiv_comp (f := q) (g := fun y => (eMs s y).val) x
    (((F.pair s).ribbonDomain.domain.contMDiff_subtype_val.comp (eMs s).contMDiff).mdifferentiableAt (by simp))
    (q.contMDiff.mdifferentiableAt (by simp))
  change ((F.pair s).ribbonDomain.liouville.primitive (eMs s (q x)).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
      ((fun y => (eMs s y).val) ∘ q) x) = _
  rw [hd]
  change (((F.pair s).ribbonDomain.liouville.primitive (eMs s (q x)).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs s y).val)
      (q x))).compContinuousLinearMap (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) q x) = _
  rw [hpM]
  exact (congrFun hc x).symm

/-- Original native coordinate germs are transported through the proved
whole ribbon-completion comparison and its smooth inverse. No new compact
coordinate certificate is required for the original chart. -/
theorem originalRibbonEndpointEquiv_coordinates
    (LM : OriginalBundleLiouvilleLaws PM) (W : LocalCompletionFamily PM cM t)
    (hsW : s ∈ W.base) (hdimM : k + 1 = 2 * n - 2)
    (hcM : ∀ u, HasNativeCoordinateExtensions (k := k)
      (F.pair u).ribbonDomain.domain.extension (fun x => (eMs u x).val)) :
    HasNativeCoordinateExtensions (k := k) (F.pair s).ribbonDomain.domain.extension
      (fun x => (originalRibbonEndpointEquiv gM hgM hbaseM hsM F eMs x).val) := by
  let q := W.endpointSliceComparison LM gM hgM hbaseM s hsW hdimM
    (F.pair s).ribbonDomain (F.pair s).ribbonCompletion (eMs s) (hpM s) (hcM s)
  apply HasNativeCoordinateExtensions.of_smooth_square
    (W.sliceCompletion LM s).ambient.manifold (F.pair s).ribbonDomain.domain.extension
    (IntrinsicCompletionGluing.original (W.native.patches s))
    (fun x => (originalRibbonEndpointEquiv gM hgM hbaseM hsM F eMs x).val)
    (W.sliceNativePresentation LM s).coordinates
    (fun z => q.equiv.symm ((F.pair s).ribbonCompletion.inclusion.map z))
    (q.equiv.symm.contMDiff.comp (F.pair s).ribbonCompletion.inclusion.map.contMDiff)
  intro x
  change q.equiv.symm ((F.pair s).ribbonCompletion.inclusion.map
    (eMs s (transitionDiffeomorphOfCompatible cM.val gM
      (compatibleTrivialization_of_mem cM.property) hgM
      ⟨hsM, by rw [hbaseM]; exact mem_univ s⟩ x)).val) = _
  rw [transitionDiffeomorphOfCompatible_apply]
  simpa only [Diffeomorph.symm_apply_apply] using
    (congrArg q.equiv.symm (q.compact x)).symm

variable {a : ℕ} {A : Type} [TopologicalSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  {EA : Parameter → Type*} [∀ u, TopologicalSpace (EA u)]
  [TopologicalSpace (TotalSpace A EA)]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]

omit hpM in
/-- Original ribbon covariance and the actual compact source transition
derive the entire endpoint embedding equation. Only the already realized
global-chart embedding is supplied, never a junction-shaped comparison. -/
theorem originalRibbonEndpointEquiv_embedding
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
    (cA : OriginalCompactChart (k := a) (M := A) (E := EA))
    (gA : Trivialization A (π A EA))
    (hgA : CompatibleTrivialization (𝓡∂ (a + 1)) EA gA)
    (hbaseA : gA.baseSet = univ) (hsA : s ∈ cA.val.baseSet)
    (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv (F.pair s).ambientDomain.domain.boundary)
    (hj : ∀ x, (F.pair s).ribbonEmbedding.map (eMs s x).val =
      eB (PJ.mapInTrivializations gM gA hgA s x)) (x : M) :
    (F.pair s).ribbonEmbedding.map
      (originalRibbonEndpointEquiv gM hgM hbaseM hsM F eMs x).val = eB
      (compatibleBoundaryTransitionDiffeomorph cA.val gA
        (compatibleTrivialization_of_mem cA.property) hgA
        ⟨hsA, by rw [hbaseA]; exact mem_univ s⟩ (PJ.map cM cA s x)) := by
  have hsGlobalM : s ∈ gM.baseSet := by rw [hbaseM]; exact mem_univ s
  have hsGlobalA : s ∈ gA.baseSet := by rw [hbaseA]; exact mem_univ s
  change (F.pair s).ribbonEmbedding.map
    (eMs s (transitionDiffeomorphOfCompatible cM.val gM
      (compatibleTrivialization_of_mem cM.property) hgM
      ⟨hsM, hsGlobalM⟩ x)).val = _
  rw [transitionDiffeomorphOfCompatible_apply, hj]
  congr 1
  apply Subtype.ext
  rw [PJ.mapInTrivializations_eq_local_val gM gA hgA cM.val cM.property
    cA.val cA.property ⟨⟨hsGlobalM, hsM⟩, ⟨hsGlobalA, hsA⟩⟩,
    compatibleBoundaryTransitionDiffeomorph_val,
    cM.val.coordChange_coordChange gM cM.val hsM hsGlobalM,
    cM.val.coordChange_same hsM]
  rfl

end OriginalRibbonEndpoint

section Ambient

variable {a a' n : ℕ} [NeZero n]
  {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [ChartedSpace (EuclideanHalfSpace (a' + 1)) A']
  {EA EA' : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [∀ t, TopologicalSpace (EA' t)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  [SmoothCompactBundle (𝓡∂ (a' + 1)) (F := A') EA']
  {PA : BundlePrimitiveData (k := a) (M := A) EA}
  {PA' : BundlePrimitiveData (k := a') (M := A') EA'}
  {c : OriginalCompactChart (k := a) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := a') (M := A') (E := EA')}
  {t t' : Parameter}

/-- A strict junction of two original local completed bundle slices.
Its maps and end law are independent of any represented realization. -/
structure OriginalBundleAmbientJunction
    (LA : OriginalBundleLiouvilleLaws PA) (LA' : OriginalBundleLiouvilleLaws PA')
    (U : LocalCompletionFamily PA c t) (V : LocalCompletionFamily PA' c' t')
    (s s' : Parameter) (hdim : a + 1 = 2 * n) (hdim' : a' + 1 = 2 * n) where
  Ψ : (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).manifold.SmoothEquiv
    (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).manifold
  strictPrimitive :
    (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).manifold.pullback
      (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).manifold Ψ
      (CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient).primitive =
        (CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient).primitive
  ψ : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
    (IntrinsicBoundary.smoothManifold a' A')
  shift : IntrinsicBoundary.Point a A → ℝ
  smoothShift : ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, ℝ) ∞ shift
  eventualEnd : ∀ x, ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r →
    Ψ (CompletedMaslovDimension.endMap hdim (U.sliceCompletion LA s) (x, r)) =
      CompletedMaslovDimension.endMap hdim' (V.sliceCompletion LA' s') (ψ x, r + shift x)

/-- Whole original native ribbons for the original ambient junction.
The compact maps, primitive scale and across-boundary map germs contain
no represented endpoint or endpoint comparison. -/
structure OriginalBundlePositiveRibbonJunction
    {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
    {U : LocalCompletionFamily PA c t} {V : LocalCompletionFamily PA' c' t'}
    {s s' : Parameter} {hdim : a + 1 = 2 * n} {hdim' : a' + 1 = 2 * n}
    (O : OriginalBundleAmbientJunction LA LA' U V s s' hdim hdim') where
  [positiveDimension : NeZero (2 * n - 2)]
  k : ℕ
  dimension : k + 1 = 2 * n - 2
  M : Type
  N : Type
  [topologyM : TopologicalSpace M]
  [topologyN : TopologicalSpace N]
  [chartedM : ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [chartedN : ChartedSpace (EuclideanHalfSpace (k + 1)) N]
  [manifoldM : IsManifold (𝓡∂ (k + 1)) ∞ M]
  [manifoldN : IsManifold (𝓡∂ (k + 1)) ∞ N]
  [compactM : CompactSpace M]
  μ : Form k M 1
  ν : Form k N 1
  h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞
  mapGerm : IsLocallyExtendibleNativeMap (k := k) h
  scale : ℝ
  positiveScale : 0 < scale
  primitiveScale : ∀ x, (ν (h x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = scale • μ x
  j : M → IntrinsicBoundary.Point a A
  j' : N → IntrinsicBoundary.Point a' A'
  ribbonSquare : ∀ x, O.ψ (j x) = j' (h x)

attribute [instance] OriginalBundlePositiveRibbonJunction.topologyM
  OriginalBundlePositiveRibbonJunction.topologyN
  OriginalBundlePositiveRibbonJunction.chartedM OriginalBundlePositiveRibbonJunction.chartedN
  OriginalBundlePositiveRibbonJunction.manifoldM OriginalBundlePositiveRibbonJunction.manifoldN
  OriginalBundlePositiveRibbonJunction.compactM

namespace OriginalBundleAmbientJunction

variable {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
  {U : LocalCompletionFamily PA c t} {V : LocalCompletionFamily PA' c' t'}
  {s s' : Parameter} {hdim : a + 1 = 2 * n} {hdim' : a' + 1 = 2 * n}
  (O : OriginalBundleAmbientJunction LA LA' U V s s' hdim hdim')
  (g : Trivialization A (π A EA)) (g' : Trivialization A' (π A' EA'))
  (hg : CompatibleTrivialization (𝓡∂ (a + 1)) EA g)
  (hg' : CompatibleTrivialization (𝓡∂ (a' + 1)) EA' g')
  (hbase : g.baseSet = univ) (hbase' : g'.baseSet = univ)
  (hs : s ∈ U.base) (hs' : s' ∈ V.base)
  (F G : PairDeformation n)
  (eAs : ∀ u, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
    (F.pair u).ambientDomain.domain.Point ∞)
  (eAs' : ∀ u, Diffeomorph (𝓡∂ (a' + 1)) (𝓡∂ (2 * n)) A'
    (G.pair u).ambientDomain.domain.Point ∞)
  (hp : ∀ u x, ((F.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs u y).val) x) =
      PA.formInTrivialization g u x)
  (hp' : ∀ u x, ((G.pair u).ambientDomain.liouville.primitive (eAs' u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (a' + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs' u y).val) x) =
      PA'.formInTrivialization g' u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := a)
    (F.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val))
  (hc' : ∀ u, HasNativeCoordinateExtensions (k := a')
    (G.pair u).ambientDomain.domain.extension (fun x => (eAs' u x).val))

/-- Construct the native ambient junction using the actual comparison of
each original local completion with its independently retained endpoint. -/
def toNativeAmbient : NativeAmbientJunction (F.pair s) (G.pair s') := by
  let X := CompletedMaslovDimension.ambient hdim (U.sliceCompletion LA s).ambient
  let Y := CompletedMaslovDimension.ambient hdim' (V.sliceCompletion LA' s').ambient
  let q := U.ambientEndpointSliceComparison LA g hg hbase s hs F hdim eAs hp hc
  let q' := V.ambientEndpointSliceComparison LA' g' hg' hbase' s' hs' G hdim' eAs' hp' hc'
  exact
    { X := X.manifold
      Y := Y.manifold
      boundaryDimension := a
      targetBoundaryDimension := a'
      B := IntrinsicBoundary.smoothManifold a A
      B' := IntrinsicBoundary.smoothManifold a' A'
      α := X.primitive
      β := Y.primitive
      S := CompletedMaslovDimension.comparison hdim (U.sliceCompletion LA s).ambient
        (F.pair s).ambientManifold q.equiv
      S' := CompletedMaslovDimension.comparison hdim' (V.sliceCompletion LA' s').ambient
        (G.pair s').ambientManifold q'.equiv
      sourcePrimitive := CompletedMaslovDimension.comparison_primitive hdim
        (U.sliceCompletion LA s).ambient (F.pair s).ambientManifold q.equiv _ q.primitive
      targetPrimitive := CompletedMaslovDimension.comparison_primitive hdim'
        (V.sliceCompletion LA' s').ambient (G.pair s').ambientManifold q'.equiv _ q'.primitive
      Ψ := O.Ψ
      strictPrimitive := O.strictPrimitive
      endX := CompletedMaslovDimension.endMap hdim (U.sliceCompletion LA s)
      endY := CompletedMaslovDimension.endMap hdim' (V.sliceCompletion LA' s')
      bS := q.boundary
      bS' := q'.boundary
      sourceEnd := fun x r _ =>
        (CompletedMaslovDimension.comparison_end hdim (U.sliceCompletion LA s)
          (F.pair s).ambientManifold q.equiv (x, r)).trans (q.end_square x r)
      targetEnd := fun x r _ =>
        (CompletedMaslovDimension.comparison_end hdim' (V.sliceCompletion LA' s')
          (G.pair s').ambientManifold q'.equiv (x, r)).trans (q'.end_square x r)
      ψ := O.ψ
      shift := O.shift
      smoothShift := O.smoothShift
      eventualEnd := O.eventualEnd }

variable [NeZero (2 * n - 2)] (R : OriginalBundlePositiveRibbonJunction O)
  (eM : Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.M
    (F.pair s).ribbonDomain.domain.Point ∞)
  (eN : Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.N
    (G.pair s').ribbonDomain.domain.Point ∞)
  (hμ : ∀ x, ((F.pair s).ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = R.μ x)
  (hν : ∀ x, ((G.pair s').ribbonDomain.liouville.primitive (eN x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eN y).val) x) = R.ν x)
  (hcoordM : HasNativeCoordinateExtensions (k := R.k)
    (F.pair s).ribbonDomain.domain.extension (fun x => (eM x).val))
  (hcoordN : HasNativeCoordinateExtensions (k := R.k)
    (G.pair s').ribbonDomain.domain.extension (fun x => (eN x).val))
  (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv (F.pair s).ambientDomain.domain.boundary)
  (eB' : (IntrinsicBoundary.smoothManifold a' A').SmoothEquiv (G.pair s').ambientDomain.domain.boundary)
  (hb : ∀ b, (F.pair s).ambientDomain.domain.boundaryInclusion.map (eB b) = (eAs s b.val).val)
  (hb' : ∀ b, (G.pair s').ambientDomain.domain.boundaryInclusion.map (eB' b) = (eAs' s' b.val).val)
  (hj : ∀ x, (F.pair s).ribbonEmbedding.map (eM x).val = eB
    (compatibleBoundaryTransitionDiffeomorph c.val g
      (compatibleTrivialization_of_mem c.property) hg
      ⟨U.base_subset hs, by rw [hbase]; exact mem_univ s⟩ (R.j x)))
  (hj' : ∀ x, (G.pair s').ribbonEmbedding.map (eN x).val = eB'
    (compatibleBoundaryTransitionDiffeomorph c'.val g'
      (compatibleTrivialization_of_mem c'.property) hg'
      ⟨V.base_subset hs', by rw [hbase']; exact mem_univ s'⟩ (R.j' x)))

/-- Represent the whole original ribbon square on the exact independently
retained endpoint tuples. Native compact coordinate laws supply the ribbon
presentations; the proved original boundary comparison supplies both
embedding equations. No completion junction is assumed. -/
def toNativePositiveRibbon :
    NativePositiveRibbonJunction (F.pair s) (G.pair s')
      (O.toNativeAmbient g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc') := by
  let q := U.ambientEndpointSliceComparison LA g hg hbase s hs F hdim eAs hp hc
  let q' := V.ambientEndpointSliceComparison LA' g' hg' hbase' s' hs' G hdim' eAs' hp' hc'
  exact
    { positiveDimension := R.positiveDimension
      k := R.k
      dimension := R.dimension
      M := R.M
      N := R.N
      μ := R.μ
      ν := R.ν
      eM := eM
      eN := eN
      sourcePrimitive := hμ
      targetPrimitive := hν
      sourceCoordinates := hcoordM
      targetCoordinates := hcoordN
      h := R.h
      mapGerm := R.mapGerm
      scale := R.scale
      positiveScale := R.positiveScale
      primitiveScale := R.primitiveScale
      j := R.j
      j' := R.j'
      sourceEmbedding := fun x => (hj x).trans
        (q.boundary_eq_native U LA g hg hbase s hs (F.pair s).ambientDomain
          (F.pair s).ambientCompletion (eAs s) eB hb (R.j x)).symm
      targetEmbedding := fun x => (hj' x).trans
        (q'.boundary_eq_native V LA' g' hg' hbase' s' hs' (G.pair s').ambientDomain
          (G.pair s').ambientCompletion (eAs' s') eB' hb' (R.j' x)).symm
      ribbonSquare := R.ribbonSquare }

/-- The source-only original strict map and whole ribbon data construct
an actual native completion junction between the retained endpoints. -/
def toNativeCompletionJunction : NativeCompletionJunction (F.pair s) (G.pair s') :=
  .positive
    (O.toNativeAmbient g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc')
    (O.toNativePositiveRibbon g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc'
      R eM eN hμ hν hcoordM hcoordN eB eB' hb hb' hj hj')

/-- The identification generated from the original bundle junction retains
both directions of the prescribed full ribbon map and its positive scale. -/
theorem toNativeCompletionJunction_ribbon_spec :
    let J := O.toNativeCompletionJunction g g' hg hg' hbase hbase' hs hs' F G
      eAs eAs' hp hp' hc hc' R eM eN hμ hν hcoordM hcoordN eB eB' hb hb' hj hj'
    J.identification.scale = R.scale ∧
    (∀ x, J.identification.ribbonEquiv.map (eM x).val = (eN (R.h x)).val) ∧
    (∀ y, J.identification.ribbonEquiv.inverse (eN y).val = (eM (R.h.symm y)).val) := by
  let r := O.toNativePositiveRibbon g g' hg hg' hbase hbase' hs hs' F G
    eAs eAs' hp hp' hc hc' R eM eN hμ hν hcoordM hcoordN eB eB' hb hb' hj hj'
  obtain ⟨_, hscale, _, _, hmap, hinverse⟩ := r.identification_spec
  exact ⟨hscale, hmap, hinverse⟩

/-- The same generated identification uses the conjugate of the original
strict map and boundary map, and the original arbitrary real end shift. -/
theorem toNativeCompletionJunction_ambient_spec :
    let J := O.toNativeCompletionJunction g g' hg hg' hbase hbase' hs hs' F G
      eAs eAs' hp hp' hc hc' R eM eN hμ hν hcoordM hcoordN eB eB' hb hb' hj hj'
    J.identification.ambientEquiv = (J.ambient.S.symm.trans O.Ψ).trans J.ambient.S' ∧
    J.identification.boundaryEquiv = (J.ambient.bS.symm.trans O.ψ).trans J.ambient.bS' ∧
    J.identification.shift = O.shift ∘ J.ambient.bS.symm := by
  let r := O.toNativePositiveRibbon g g' hg hg' hbase hbase' hs hs' F G
    eAs eAs' hp hp' hc hc' R eM eN hμ hν hcoordM hcoordN eB eB' hb hb' hj hj'
  obtain ⟨hambient, _, hboundary, hshift, _, _⟩ := r.identification_spec
  exact ⟨hambient, hboundary, hshift⟩

section OriginalRibbonBundles

variable {EM EN : Parameter → Type*}
  [∀ u, TopologicalSpace (EM u)] [∀ u, TopologicalSpace (EN u)]
  [TopologicalSpace (TotalSpace R.M EM)] [TopologicalSpace (TotalSpace R.N EN)]
  [SmoothCompactBundle (𝓡∂ (R.k + 1)) (F := R.M) EM]
  [SmoothCompactBundle (𝓡∂ (R.k + 1)) (F := R.N) EN]
  (PM : BundlePrimitiveData (k := R.k) (M := R.M) EM)
  (PN : BundlePrimitiveData (k := R.k) (M := R.N) EN)
  (LM : OriginalBundleLiouvilleLaws PM) (LN : OriginalBundleLiouvilleLaws PN)
  (PJ : BundleRibbonData (a := a) (M := R.M) (A := A) (𝓡∂ (R.k + 1)) EM EA)
  (PJ' : BundleRibbonData (a := a') (M := R.N) (A := A') (𝓡∂ (R.k + 1)) EN EA')
  (cM : OriginalCompactChart (k := R.k) (M := R.M) (E := EM))
  (cN : OriginalCompactChart (k := R.k) (M := R.N) (E := EN))
  {tM tN : Parameter}
  (W : LocalCompletionFamily PM cM tM) (W' : LocalCompletionFamily PN cN tN)
  (hsW : s ∈ W.base) (hsW' : s' ∈ W'.base)
  (hμoriginal : PM.form cM s = R.μ) (hνoriginal : PN.form cN s' = R.ν)
  (hjoriginal : PJ.map cM c s = R.j) (hj'original : PJ'.map cN c' s' = R.j')
  (gM : Trivialization R.M (π R.M EM)) (gN : Trivialization R.N (π R.N EN))
  (hgM : CompatibleTrivialization (𝓡∂ (R.k + 1)) EM gM)
  (hgN : CompatibleTrivialization (𝓡∂ (R.k + 1)) EN gN)
  (hbaseM : gM.baseSet = univ) (hbaseN : gN.baseSet = univ)
  (eMs : ∀ u, Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.M
    (F.pair u).ribbonDomain.domain.Point ∞)
  (eNs : ∀ u, Diffeomorph (𝓡∂ (R.k + 1)) (𝓡∂ (2 * n - 2)) R.N
    (G.pair u).ribbonDomain.domain.Point ∞)
  (hpM : ∀ u x, ((F.pair u).ribbonDomain.liouville.primitive (eMs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs u y).val) x) =
      PM.formInTrivialization gM u x)
  (hpN : ∀ u x, ((G.pair u).ribbonDomain.liouville.primitive (eNs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (R.k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eNs u y).val) x) =
      PN.formInTrivialization gN u x)
  (hcM : ∀ u, HasNativeCoordinateExtensions (k := R.k)
    (F.pair u).ribbonDomain.domain.extension (fun x => (eMs u x).val))
  (hcN : ∀ u, HasNativeCoordinateExtensions (k := R.k)
    (G.pair u).ribbonDomain.domain.extension (fun x => (eNs u x).val))
  (hjGlobal : ∀ x, (F.pair s).ribbonEmbedding.map (eMs s x).val =
    eB (PJ.mapInTrivializations gM g hg s x))
  (hjGlobal' : ∀ x, (G.pair s').ribbonEmbedding.map (eNs s' x).val =
    eB' (PJ'.mapInTrivializations gN g' hg' s' x))

/-- Consume original ribbon-bundle data and the existing independent
global realizations. All original-chart primitive, coordinate and full
embedding correspondences needed by the junction are proved from bundle
covariance and the actual ribbon-completion comparison. -/
def toNativeCompletionJunction_of_originalRibbonBundleData :
    NativeCompletionJunction (F.pair s) (G.pair s') := by
  let m := originalRibbonEndpointEquiv gM hgM hbaseM (W.base_subset hsW) F eMs
  let m' := originalRibbonEndpointEquiv gN hgN hbaseN (W'.base_subset hsW') G eNs
  have hm := originalRibbonEndpointEquiv_coordinates gM hgM hbaseM
    (W.base_subset hsW) F eMs hpM LM W hsW R.dimension hcM
  have hm' := originalRibbonEndpointEquiv_coordinates gN hgN hbaseN
    (W'.base_subset hsW') G eNs hpN LN W' hsW' R.dimension hcN
  refine O.toNativeCompletionJunction g g' hg hg' hbase hbase' hs hs' F G
    eAs eAs' hp hp' hc hc' R m m' ?_ ?_ hm hm' eB eB' hb hb' ?_ ?_
  · intro x
    exact (originalRibbonEndpointEquiv_primitive gM hgM hbaseM
      (W.base_subset hsW) F eMs hpM x).trans (congrFun hμoriginal x)
  · intro x
    exact (originalRibbonEndpointEquiv_primitive gN hgN hbaseN
      (W'.base_subset hsW') G eNs hpN x).trans (congrFun hνoriginal x)
  · intro x
    rw [← hjoriginal]
    exact originalRibbonEndpointEquiv_embedding gM hgM hbaseM (W.base_subset hsW)
      F eMs PJ c g hg hbase (U.base_subset hs) eB hjGlobal x
  · intro x
    rw [← hj'original]
    exact originalRibbonEndpointEquiv_embedding gN hgN hbaseN (W'.base_subset hsW')
      G eNs PJ' c' g' hg' hbase' (V.base_subset hs') eB' hjGlobal' x

end OriginalRibbonBundles

end OriginalBundleAmbientJunction
end Ambient

end FsFltz.Geometry.IntrinsicSmoothBundle
