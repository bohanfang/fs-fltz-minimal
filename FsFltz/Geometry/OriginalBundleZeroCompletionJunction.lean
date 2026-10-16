import FsFltz.Geometry.OriginalBundleCompletionJunction
import FsFltz.Geometry.OriginalBundleRibbonCompletionMarking

/-!
# Original zero-dimensional bundle ribbons at retained junctions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–161;
`def:chain`, lines 171–194; and `sec:lean`, lines 788–814 and 825–830.
For rank one the whole finite ribbon, its native diffeomorphism and its
full boundary square are retained on independently selected endpoints.
Original bundle transitions and ribbon covariance derive the embedding
equations. Zero-dimensional primitives vanish, so no ribbon primitive
or coordinate-extension certificates are required.

These are conditional selected-realization junction producers. The
original geometric junction and existing global realization are supplied;
their toric existence, grading homotopies and finite itinerary remain pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

section OriginalZeroRibbonEndpoint

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {EM : Parameter → Type*} [∀ u, TopologicalSpace (EM u)]
  [TopologicalSpace (TotalSpace M EM)]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {s : Parameter}
  (gM : Trivialization M (π M EM)) (hbaseM : gM.baseSet = univ)
  (cM : OriginalZeroCompactChart (M := M) (E := EM)) (hsM : s ∈ cM.val.baseSet)
  (F : PairDeformation 1)
  (eMs : ∀ u, letI := (F.pair u).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (F.pair u).ribbonDomain.domain.Point ∞)

/-- The original zero ribbon chart maps to the retained compact endpoint
through its actual bundle transition and existing compact correspondence. -/
def originalZeroRibbonEndpointEquiv :
    letI := (F.pair s).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (F.pair s).ribbonDomain.domain.Point ∞ :=
  (zeroBundleTransition cM.val gM s
    ⟨hsM, by rw [hbaseM]; exact mem_univ s⟩).trans (eMs s)

variable {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EA : Parameter → Type*} [∀ u, TopologicalSpace (EA u)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]

/-- Original zero-ribbon covariance and the actual compact source cocycle
derive the full embedding equation on every finite ribbon point. -/
theorem originalZeroRibbonEndpointEquiv_embedding
    (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (cA : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (gA : Trivialization A (π A EA))
    (hgA : CompatibleTrivialization (𝓡∂ 2) EA gA)
    (hbaseA : gA.baseSet = univ) (hsA : s ∈ cA.val.baseSet)
    (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv (F.pair s).ambientDomain.domain.boundary)
    (hj : ∀ x, (F.pair s).ribbonEmbedding.map (eMs s x).val =
      eB (PJ.mapInTrivializations gM gA hgA s x)) (x : M) :
    (F.pair s).ribbonEmbedding.map
      (originalZeroRibbonEndpointEquiv gM hbaseM cM hsM F eMs x).val = eB
      (compatibleBoundaryTransitionDiffeomorph cA.val gA
        (compatibleTrivialization_of_mem cA.property) hgA
        ⟨hsA, by rw [hbaseA]; exact mem_univ s⟩ (PJ.map cM cA s x)) := by
  have hsGlobalM : s ∈ gM.baseSet := by rw [hbaseM]; exact mem_univ s
  have hsGlobalA : s ∈ gA.baseSet := by rw [hbaseA]; exact mem_univ s
  change (F.pair s).ribbonEmbedding.map
    (eMs s (zeroBundleTransition cM.val gM s ⟨hsM, hsGlobalM⟩ x)).val = _
  rw [zeroBundleTransition_apply, hj]
  congr 1
  apply Subtype.ext
  rw [PJ.mapInTrivializations_eq_local_val gM gA hgA cM.val cM.property
    cA.val cA.property ⟨⟨hsGlobalM, hsM⟩, ⟨hsGlobalA, hsA⟩⟩,
    compatibleBoundaryTransitionDiffeomorph_val,
    cM.val.coordChange_coordChange gM cM.val hsM hsGlobalM,
    cM.val.coordChange_same hsM]
  rfl

end OriginalZeroRibbonEndpoint

section ZeroJunction

variable {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace 2) A] [ChartedSpace (EuclideanHalfSpace 2) A']
  {EA EA' : Parameter → Type*} [∀ u, TopologicalSpace (EA u)] [∀ u, TopologicalSpace (EA' u)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ 2) (F := A) EA] [SmoothCompactBundle (𝓡∂ 2) (F := A') EA']
  {PA : BundlePrimitiveData (k := 1) (M := A) EA}
  {PA' : BundlePrimitiveData (k := 1) (M := A') EA'}
  {c : OriginalCompactChart (k := 1) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := 1) (M := A') (E := EA')}
  {t t' s s' : Parameter}
  {LA : OriginalBundleLiouvilleLaws PA} {LA' : OriginalBundleLiouvilleLaws PA'}
  {U : LocalCompletionFamily PA c t} {V : LocalCompletionFamily PA' c' t'}

/-- Whole original zero-dimensional ribbon maps and their full boundary
square. The data contain no represented endpoint or comparison map. -/
structure OriginalBundleZeroRibbonJunction
    (O : OriginalBundleAmbientJunction LA LA' U V s s' (n := 1) rfl rfl) where
  M : Type
  N : Type
  [topologyM : TopologicalSpace M]
  [topologyN : TopologicalSpace N]
  [chartedM : ChartedSpace (Model 0) M]
  [chartedN : ChartedSpace (Model 0) N]
  h : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N ∞
  scale : ℝ
  positiveScale : 0 < scale
  j : M → IntrinsicBoundary.Point 1 A
  j' : N → IntrinsicBoundary.Point 1 A'
  ribbonSquare : ∀ x, O.ψ (j x) = j' (h x)

attribute [instance] OriginalBundleZeroRibbonJunction.topologyM
  OriginalBundleZeroRibbonJunction.topologyN
  OriginalBundleZeroRibbonJunction.chartedM OriginalBundleZeroRibbonJunction.chartedN

namespace OriginalBundleAmbientJunction

variable (O : OriginalBundleAmbientJunction LA LA' U V s s' (n := 1) rfl rfl)
  (g : Trivialization A (π A EA)) (g' : Trivialization A' (π A' EA'))
  (hg : CompatibleTrivialization (𝓡∂ 2) EA g)
  (hg' : CompatibleTrivialization (𝓡∂ 2) EA' g')
  (hbase : g.baseSet = univ) (hbase' : g'.baseSet = univ)
  (hs : s ∈ U.base) (hs' : s' ∈ V.base) (F G : PairDeformation 1)
  (eAs : ∀ u, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A (F.pair u).ambientDomain.domain.Point ∞)
  (eAs' : ∀ u, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A' (G.pair u).ambientDomain.domain.Point ∞)
  (hp : ∀ u x, ((F.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs u y).val) x) = PA.formInTrivialization g u x)
  (hp' : ∀ u x, ((G.pair u).ambientDomain.liouville.primitive (eAs' u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs' u y).val) x) = PA'.formInTrivialization g' u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := 1)
    (F.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val))
  (hc' : ∀ u, HasNativeCoordinateExtensions (k := 1)
    (G.pair u).ambientDomain.domain.extension (fun x => (eAs' u x).val))
  (R : OriginalBundleZeroRibbonJunction O)
  (eM : letI := (F.pair s).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.M (F.pair s).ribbonDomain.domain.Point ∞)
  (eN : letI := (G.pair s').ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.N (G.pair s').ribbonDomain.domain.Point ∞)
  (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv (F.pair s).ambientDomain.domain.boundary)
  (eB' : (IntrinsicBoundary.smoothManifold 1 A').SmoothEquiv (G.pair s').ambientDomain.domain.boundary)
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

/-- The actual original ambient boundary comparisons transport the whole
zero-dimensional ribbon square to the exact retained endpoint tuples. -/
def toNativeZeroRibbon : NativeZeroRibbonJunction (F.pair s) (G.pair s')
    (O.toNativeAmbient g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc') := by
  let q := U.ambientEndpointSliceComparison LA g hg hbase s hs F rfl eAs hp hc
  let q' := V.ambientEndpointSliceComparison LA' g' hg' hbase' s' hs' G rfl eAs' hp' hc'
  exact
    { M := R.M
      N := R.N
      eM := eM
      eN := eN
      h := R.h
      scale := R.scale
      positiveScale := R.positiveScale
      j := R.j
      j' := R.j'
      sourceEmbedding := fun x => (hj x).trans
        (q.boundary_eq_native U LA g hg hbase s hs (F.pair s).ambientDomain
          (F.pair s).ambientCompletion (eAs s) eB hb (R.j x)).symm
      targetEmbedding := fun x => (hj' x).trans
        (q'.boundary_eq_native V LA' g' hg' hbase' s' hs' (G.pair s').ambientDomain
          (G.pair s').ambientCompletion (eAs' s') eB' hb' (R.j' x)).symm
      ribbonSquare := R.ribbonSquare }

/-- Construct the zero-dimensional native junction from original ambient
and finite whole-ribbon maps, retaining both independent endpoints. -/
def toNativeZeroCompletionJunction : NativeCompletionJunction (F.pair s) (G.pair s') :=
  .zero
    (O.toNativeAmbient g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc')
    (O.toNativeZeroRibbon g g' hg hg' hbase hbase' hs hs' F G eAs eAs' hp hp' hc hc'
      R eM eN eB eB' hb hb' hj hj')

/-- The generated identification retains the original ambient/boundary
conjugates, arbitrary real shift, positive scale and both full ribbon-map
directions, including when the finite ribbon is empty. -/
theorem toNativeZeroCompletionJunction_spec :
    let J := O.toNativeZeroCompletionJunction g g' hg hg' hbase hbase' hs hs' F G
      eAs eAs' hp hp' hc hc' R eM eN eB eB' hb hb' hj hj'
    J.identification.ambientEquiv = (J.ambient.S.symm.trans O.Ψ).trans J.ambient.S' ∧
    J.identification.scale = R.scale ∧
    J.identification.boundaryEquiv = (J.ambient.bS.symm.trans O.ψ).trans J.ambient.bS' ∧
    J.identification.shift = O.shift ∘ J.ambient.bS.symm ∧
    (∀ x, J.identification.ribbonEquiv.map (eM x).val = (eN (R.h x)).val) ∧
    (∀ y, J.identification.ribbonEquiv.inverse (eN y).val = (eM (R.h.symm y)).val) :=
  (O.toNativeZeroRibbon g g' hg hg' hbase hbase' hs hs' F G
    eAs eAs' hp hp' hc hc' R eM eN eB eB' hb hb' hj hj').identification_spec

section OriginalRibbonBundles

variable {EM EN : Parameter → Type*}
  [∀ u, TopologicalSpace (EM u)] [∀ u, TopologicalSpace (EN u)]
  [TopologicalSpace (TotalSpace R.M EM)] [TopologicalSpace (TotalSpace R.N EN)]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.M) EM]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := R.N) EN]
  (PJ : BundleRibbonData (a := 1) (M := R.M) (A := A) 𝓘(ℝ, Model 0) EM EA)
  (PJ' : BundleRibbonData (a := 1) (M := R.N) (A := A') 𝓘(ℝ, Model 0) EN EA')
  (cM : OriginalZeroCompactChart (M := R.M) (E := EM))
  (cN : OriginalZeroCompactChart (M := R.N) (E := EN))
  (hsM : s ∈ cM.val.baseSet) (hsN : s' ∈ cN.val.baseSet)
  (hjoriginal : PJ.map cM c s = R.j) (hj'original : PJ'.map cN c' s' = R.j')
  (gM : Trivialization R.M (π R.M EM)) (gN : Trivialization R.N (π R.N EN))
  (hbaseM : gM.baseSet = univ) (hbaseN : gN.baseSet = univ)
  (eMs : ∀ u, letI := (F.pair u).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.M (F.pair u).ribbonDomain.domain.Point ∞)
  (eNs : ∀ u, letI := (G.pair u).ribbonDomain.domain.zeroChartedSpace;
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) R.N (G.pair u).ribbonDomain.domain.Point ∞)
  (hjGlobal : ∀ x, (F.pair s).ribbonEmbedding.map (eMs s x).val =
    eB (PJ.mapInTrivializations gM g hg s x))
  (hjGlobal' : ∀ x, (G.pair s').ribbonEmbedding.map (eNs s' x).val =
    eB' (PJ'.mapInTrivializations gN g' hg' s' x))

/-- Consume the original finite ribbon bundles and their existing global
realizations. Original chart transitions and bundle covariance derive both
whole embedding laws before constructing the actual zero-dimensional
junction. No ribbon primitive or coordinate germs are input. -/
def toNativeZeroCompletionJunction_of_originalRibbonBundleData :
    NativeCompletionJunction (F.pair s) (G.pair s') := by
  let m := originalZeroRibbonEndpointEquiv gM hbaseM cM hsM F eMs
  let m' := originalZeroRibbonEndpointEquiv gN hbaseN cN hsN G eNs
  refine O.toNativeZeroCompletionJunction g g' hg hg' hbase hbase' hs hs' F G
    eAs eAs' hp hp' hc hc' R m m' eB eB' hb hb' ?_ ?_
  · intro x
    rw [← hjoriginal]
    exact originalZeroRibbonEndpointEquiv_embedding gM hbaseM cM hsM F eMs
      PJ c g hg hbase (U.base_subset hs) eB hjGlobal x
  · intro x
    rw [← hj'original]
    exact originalZeroRibbonEndpointEquiv_embedding gN hbaseN cN hsN G eNs
      PJ' c' g' hg' hbase' (V.base_subset hs') eB' hjGlobal' x

end OriginalRibbonBundles
end OriginalBundleAmbientJunction
end ZeroJunction

end FsFltz.Geometry.IntrinsicSmoothBundle
