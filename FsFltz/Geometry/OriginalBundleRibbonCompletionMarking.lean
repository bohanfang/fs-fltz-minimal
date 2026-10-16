import FsFltz.Geometry.OriginalBundleCompletionMarking
import FsFltz.Geometry.IntrinsicNativeRibbonCompletionFamily

/-!
# Original ribbon completion markings on retained bundle endpoints

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–161;
`g:initial`, lines 374–384; and `sec:lean`, lines 788–814.
Independently prescribed original ribbon markings descend to the exact
ribbon completion of a retained pair deformation. Their whole-completion
covariance and all-chart recovery are proved from their original compact
inclusions. Existence of geometric full-fiber markings remains pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P}
  {c c' : OriginalCompactChart (k := k) (M := M) (E := E)} {t t' : Parameter}

namespace LocalCompletionFamily

/-- Compare the original local ribbon completion with the exact retained
ribbon completion using its already produced native endpoint laws. -/
def ribbonEndpointSliceComparison {n : ℕ} [NeZero (2 * n - 2)]
    (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
    (s : Parameter) (hs : s ∈ F.base) (Q : PairDeformation n) (hdim : k + 1 = 2 * n - 2)
    (eMs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2))
      M (Q.pair u).ribbonDomain.domain.Point ∞)
    (hp : ∀ u x, ((Q.pair u).ribbonDomain.liouville.primitive (eMs u x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs u y).val) x) =
        P.formInTrivialization g u x)
    (hc : ∀ u, HasNativeCoordinateExtensions (k := k)
      (Q.pair u).ribbonDomain.domain.extension (fun x => (eMs u x).val)) :
    EndpointSliceComparison F L g s (Q.pair s).ribbonDomain
      (Q.pair s).ribbonCompletion (eMs s) :=
  F.endpointSliceComparison L g hg hbase s hs hdim (Q.pair s).ribbonDomain
    (Q.pair s).ribbonCompletion (eMs s) (hp s) (hc s)

end LocalCompletionFamily

namespace OriginalBundleCompletionMarkingData

section PositiveRibbon

variable {n : ℕ} [NeZero (2 * n - 2)] {W : Parameter → CompleteLiouvilleManifold (2 * n - 2)}
  (A : OriginalBundleCompletionMarkingData L W)
  (F : LocalCompletionFamily P c t)
  (g : Trivialization M (π M E))
  (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n - 2)
  (eMs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2))
    M (Q.pair u).ribbonDomain.domain.Point ∞)
  (hp : ∀ u x, ((Q.pair u).ribbonDomain.liouville.primitive (eMs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eMs u y).val) x) =
      P.formInTrivialization g u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := k)
    (Q.pair u).ribbonDomain.domain.extension (fun x => (eMs u x).val))

/-- The source-only original marking data produce an inclusion marking on
the exact ribbon completion of the same already supplied deformation.
The endpoint comparison is constructed from its actual native laws. -/
def ribbonMarking (s : Parameter) (hs : s ∈ F.base) :
    InclusionMarking (Q.pair s).ribbonCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eMs s).symm y)) :=
  A.endpointMarking F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc)

/-- The same deformation's literal retained compact inclusion recovers
the prescribed original common compact bundle map. -/
theorem ribbonMarking_native (s : Parameter) (hs : s ∈ F.base) (x : M) :
    (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv
      ((Q.pair s).ribbonCompletion.inclusion.map (eMs s x).val) =
        chartValue g (A.compact s) s x :=
  A.endpointMarking_native F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc) x

/-- The whole original local marking is recovered through the exact
endpoint comparison used on this same pair deformation. -/
theorem ribbonMarking_recovers_original (s : Parameter) (hs : s ∈ F.base) :
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc).equiv.trans
      (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv =
        A.localEquiv F s hs :=
  A.endpointMarking_recovers_original F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc)

/-- The exact same ribbon completion and its complete flow satisfy the
transport equation at every real time. -/
theorem ribbonMarking_flow (s : Parameter) (hs : s ∈ F.base)
    (y : (Q.pair s).ribbonCompletion.ambient.manifold.Point) (r : ℝ) :
    (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv
      ((Q.pair s).ribbonCompletion.ambient.completeFlow.flow r y) =
      (W s).completeFlow.flow r
        ((A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv y) :=
  A.endpointMarking_flow F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc) y r

/-- On every real boundary orbit, the same ribbon marking recovers the
prescribed inclusion of the original compact boundary point. -/
theorem ribbonMarking_end_native (s : Parameter) (hs : s ∈ F.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv
      ((Q.pair s).ribbonCompletion.endMap
        ((F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc).boundary b, r)) =
      (W s).completeFlow.flow r (chartValue c.val (A.compact s) s b.val) :=
  A.endpointMarking_end_native F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc) b r

/-- The same ribbon marking is independent of the original local chart
used to construct it, throughout each whole completed endpoint. -/
theorem ribbonMarking_choice_independent (G : LocalCompletionFamily P c' t')
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hF).equiv =
      (A.ribbonMarking G g hg hbase Q hdim eMs hp hc s hG).equiv :=
  A.endpointMarking_choice_independent F g s hF (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eMs s)
    (F.ribbonEndpointSliceComparison L g hg hbase s hF Q hdim eMs hp hc) G hG
    (G.ribbonEndpointSliceComparison L g hg hbase s hG Q hdim eMs hp hc)

/-- Descend at every actual parameter using an original atlas chart that
contains it and the already constructed local completion family. This
pointwise choice imposes no smoothness on the choice of chart. -/
def ribbonMarkingAt (s : Parameter) :
    InclusionMarking (Q.pair s).ribbonCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eMs s).symm y)) := by
  let c₀ : OriginalCompactChart (k := k) (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs₀ : s ∈ c₀.val.baseSet := mem_baseSet_trivializationAt _ _ _
  let F₀ := L.localCompletionFamily c₀ s hs₀
  exact A.ribbonMarking F₀ g hg hbase Q hdim eMs hp hc s F₀.base_mem

/-- The parameterwise descended marking recovers every supplied original
local chart on its whole completion. Thus the arbitrary original chart
used to define it has no effect on the returned marking. -/
theorem ribbonMarkingAt_recovers_original (s : Parameter) (hs : s ∈ F.base) :
    (F.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc).equiv.trans
      (A.ribbonMarkingAt g hg hbase Q hdim eMs hp hc s).equiv =
        A.localEquiv F s hs := by
  let c₀ : OriginalCompactChart (k := k) (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs₀ : s ∈ c₀.val.baseSet := mem_baseSet_trivializationAt _ _ _
  let F₀ := L.localCompletionFamily c₀ s hs₀
  have he : (A.ribbonMarkingAt g hg hbase Q hdim eMs hp hc s).equiv =
      (A.ribbonMarking F g hg hbase Q hdim eMs hp hc s hs).equiv :=
    A.ribbonMarking_choice_independent F₀ g hg hbase Q hdim eMs hp hc
      F s F₀.base_mem hs
  rw [he]
  exact A.ribbonMarking_recovers_original F g hg hbase Q hdim eMs hp hc s hs

/-- Source-only original markings give an actual endpoint inclusion
marking at every parameter, together with literal recovery in all
original local charts. Only marking existence on the source is supplied. -/
theorem exists_ribbonMarking (s : Parameter) :
    ∃ q : InclusionMarking (Q.pair s).ribbonCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eMs s).symm y)),
      ∀ (c₀ : OriginalCompactChart (k := k) (M := M) (E := E)) (t₀ : Parameter)
        (G : LocalCompletionFamily P c₀ t₀) (hs : s ∈ G.base),
        (G.ribbonEndpointSliceComparison L g hg hbase s hs Q hdim eMs hp hc).equiv.trans
          q.equiv = A.localEquiv G s hs := by
  refine ⟨A.ribbonMarkingAt g hg hbase Q hdim eMs hp hc s, ?_⟩
  intro c₀ t₀ G hs
  exact A.ribbonMarkingAt_recovers_original G g hg hbase Q hdim eMs hp hc s hs

end PositiveRibbon

end OriginalBundleCompletionMarkingData
section ZeroRibbon
open IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) E]

/-- The actual original atlas of the boundaryless finite ribbon bundle. -/
abbrev OriginalZeroCompactChart :=
  {c : Trivialization M (π M E) // c ∈ trivializationAtlas M E}

/-- In dimension zero the original source itself is its whole completion.
Only original chart markings and their common compact inclusion are inputs.
Primitive preservation and chart covariance are consequences. -/
structure OriginalZeroBundleCompletionMarkingData
    (Z : Parameter → CompleteLiouvilleManifold 0) where
  compact : ∀ s, TotalSpace M E → (Z s).manifold.Point
  chart : ∀ (c : OriginalZeroCompactChart (M := M) (E := E)) s
    (_hs : s ∈ c.val.baseSet), (sourceManifold M).SmoothEquiv (Z s).manifold
  native : ∀ c s hs x, chart c s hs x = chartValue c.val (compact s) s x

/-- The actual compact coordinate change is a smooth equivalence on the
zero-dimensional native completion. No arbitrary extension is chosen. -/
def zeroBundleTransition (g g' : Trivialization M (π M E))
    (s : Parameter) (hs : s ∈ g.baseSet ∩ g'.baseSet) :
    (sourceManifold M).SmoothEquiv (sourceManifold M) := by
  letI := source_discreteTopology M
  exact
    { __ := (g.coordChangeHomeomorph g' hs.1 hs.2).toEquiv
      contMDiff_toFun := contMDiff_of_discreteTopology
      contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem zeroBundleTransition_apply (g g' : Trivialization M (π M E))
    (s : Parameter) (hs : s ∈ g.baseSet ∩ g'.baseSet) (x : M) :
    zeroBundleTransition g g' s hs x = g.coordChange g' s x := rfl

/-- The whole original zero ribbon chart maps to the exact retained endpoint
completion by its actual coordinate change and canonical compact inclusion. -/
def zeroRibbonEndpointEquiv (g : Trivialization M (π M E)) (hbase : g.baseSet = univ)
    (Q : PairDeformation 1)
    (eFs : ∀ u, letI := (Q.pair u).ribbonDomain.domain.zeroChartedSpace
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair u).ribbonDomain.domain.Point ∞)
    (c : OriginalZeroCompactChart (M := M) (E := E))
    (s : Parameter) (hs : s ∈ c.val.baseSet) :
    (sourceManifold M).SmoothEquiv (Q.pair s).ribbonCompletion.ambient.manifold :=
  (zeroBundleTransition c.val g s ⟨hs, by rw [hbase]; exact mem_univ s⟩).trans
    (endpointCompletionDiffeomorph (Q.pair s).ribbonDomain (Q.pair s).ribbonCompletion (eFs s))

namespace OriginalZeroBundleCompletionMarkingData

variable {Z : Parameter → CompleteLiouvilleManifold 0}
  (R : OriginalZeroBundleCompletionMarkingData (M := M) (E := E) Z)

/-- Original compact inclusion agreement proves covariance everywhere,
since every original zero-dimensional completion point is native. -/
theorem chart_overlap (c c' : OriginalZeroCompactChart (M := M) (E := E))
    (s : Parameter) (hs : s ∈ c.val.baseSet ∩ c'.val.baseSet) :
    (zeroBundleTransition c.val c'.val s hs).trans (R.chart c' s hs.2) =
      R.chart c s hs.1 := by
  apply Diffeomorph.ext
  intro x
  change R.chart c' s hs.2 (zeroBundleTransition c.val c'.val s hs x) = _
  rw [zeroBundleTransition_apply, R.native, R.native]
  exact chartValue_coordChange c.val c'.val (R.compact s) hs x

/-- A marking in any globally retained compact chart is obtained from an
original local chart containing the parameter. -/
def globalEquiv (g : Trivialization M (π M E)) (hbase : g.baseSet = univ)
    (s : Parameter) : (sourceManifold M).SmoothEquiv (Z s).manifold := by
  let c : OriginalZeroCompactChart (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs : s ∈ c.val.baseSet := mem_baseSet_trivializationAt _ _ _
  exact (zeroBundleTransition g c.val s ⟨by rw [hbase]; exact mem_univ s, hs⟩).trans
    (R.chart c s hs)

/-- The global marking retains the one prescribed original bundle inclusion. -/
theorem globalEquiv_native (g : Trivialization M (π M E)) (hbase : g.baseSet = univ)
    (s : Parameter) (x : M) :
    R.globalEquiv g hbase s x = chartValue g (R.compact s) s x := by
  let c : OriginalZeroCompactChart (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs : s ∈ c.val.baseSet := mem_baseSet_trivializationAt _ _ _
  change R.chart c s hs (zeroBundleTransition g c.val s _ x) = _
  rw [zeroBundleTransition_apply, R.native]
  exact chartValue_coordChange g c.val (R.compact s)
    ⟨by rw [hbase]; exact mem_univ s, hs⟩ x

variable (g : Trivialization M (π M E)) (hbase : g.baseSet = univ)
  (Q : PairDeformation 1)
  (eFs : ∀ u, letI := (Q.pair u).ribbonDomain.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair u).ribbonDomain.domain.Point ∞)

/-- Original zero ribbon markings descend to the same retained completion.
All one-forms vanish, so primitive preservation has no additional premise. -/
def ribbonMarkingAt (s : Parameter) :
    InclusionMarking (Q.pair s).ribbonCompletion (Z s)
      (fun y => chartValue g (R.compact s) s ((eFs s).symm y)) := by
  let a := endpointCompletionDiffeomorph (Q.pair s).ribbonDomain
    (Q.pair s).ribbonCompletion (eFs s)
  exact (Q.pair s).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv
    (sourceManifold M) 0 a
    (((sourceManifold M).oneForm_eq_zero_of_dimension_zero _))
    (eFs s).toEquiv id (fun _ => rfl) (Z s)
    (chartValue g (R.compact s) s) (R.globalEquiv g hbase s)
    ((sourceManifold M).oneForm_eq_zero_of_dimension_zero _)
    (R.globalEquiv_native g hbase s)

/-- Every original atlas marking is recovered on its whole completion,
through the same retained endpoint's canonical comparison. -/
theorem ribbonMarkingAt_recovers_original
    (c : OriginalZeroCompactChart (M := M) (E := E))
    (s : Parameter) (hs : s ∈ c.val.baseSet) :
    (zeroRibbonEndpointEquiv g hbase Q eFs c s hs).trans
      (R.ribbonMarkingAt g hbase Q eFs s).equiv = R.chart c s hs := by
  apply Diffeomorph.ext
  intro x
  change R.globalEquiv g hbase s
    ((endpointCompletionDiffeomorph (Q.pair s).ribbonDomain
      (Q.pair s).ribbonCompletion (eFs s)).symm
      (endpointCompletionDiffeomorph (Q.pair s).ribbonDomain
        (Q.pair s).ribbonCompletion (eFs s)
          (zeroBundleTransition c.val g s _ x))) = _
  rw [Diffeomorph.symm_apply_apply, R.globalEquiv_native, zeroBundleTransition_apply, R.native]
  exact (chartValue_coordChange c.val g (R.compact s)
    ⟨hs, by rw [hbase]; exact mem_univ s⟩ x)

/-- The native compact equation retains every original finite ribbon point. -/
theorem ribbonMarkingAt_native (s : Parameter) (x : M) :
    (R.ribbonMarkingAt g hbase Q eFs s).equiv
      ((Q.pair s).ribbonCompletion.inclusion.map (eFs s x).val) =
        chartValue g (R.compact s) s x := by
  simpa only [(eFs s).symm_apply_apply] using
    (R.ribbonMarkingAt g hbase Q eFs s).inclusion (eFs s x)

/-- The actual endpoint and target complete flows agree at every real time. -/
theorem ribbonMarkingAt_flow (s : Parameter)
    (x : (Q.pair s).ribbonCompletion.ambient.manifold.Point) (r : ℝ) :
    (R.ribbonMarkingAt g hbase Q eFs s).equiv
      ((Q.pair s).ribbonCompletion.ambient.completeFlow.flow r x) =
      (Z s).completeFlow.flow r ((R.ribbonMarkingAt g hbase Q eFs s).equiv x) :=
  (Q.pair s).ribbonCompletion.ambient.map_flow (Z s)
    (R.ribbonMarkingAt g hbase Q eFs s).equiv
    (R.ribbonMarkingAt g hbase Q eFs s).primitive x r

/-- The original finite ribbon atlas produces an actual inclusion marking
with recovery of every original chart, without an endpoint compatibility input. -/
theorem exists_ribbonMarking (s : Parameter) :
    ∃ q : InclusionMarking (Q.pair s).ribbonCompletion (Z s)
        (fun y => chartValue g (R.compact s) s ((eFs s).symm y)),
      ∀ (c : OriginalZeroCompactChart (M := M) (E := E)) (hs : s ∈ c.val.baseSet),
        (zeroRibbonEndpointEquiv g hbase Q eFs c s hs).trans q.equiv = R.chart c s hs := by
  refine ⟨R.ribbonMarkingAt g hbase Q eFs s, ?_⟩
  intro c hs
  exact R.ribbonMarkingAt_recovers_original g hbase Q eFs c s hs

end OriginalZeroBundleCompletionMarkingData
end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
