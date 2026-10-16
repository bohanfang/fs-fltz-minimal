import FsFltz.Geometry.IntrinsicBundleLocalCompletionComparisonCoherence
import FsFltz.Geometry.NativeSliceInclusionMarking

/-!
# Descent of independently prescribed original completion markings

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 143–158;
`def:chain`, lines 163–199; `g:initial`, lines 374–384; and `sec:lean`,
lines 788–814. Original chart markings into one completed target at each
parameter are supplied independently of any represented pair deformation.
Only their primitive and original compact inclusion laws are inputs.
Strict-map uniqueness derives overlap covariance on the whole completion.
The same markings then descend to an independently retained endpoint.

The target may vary with the parameter. Each marking is a smooth
diffeomorphism on its slice; no joint smoothness of this marking family is
asserted. Existence of the source markings, in particular the geometric
full-fiber markings of `g:initial`, remains a separate obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}

/-- Markings prescribed on the original compact bundle atlas. There is
one target and one original compact inclusion per actual parameter.
Neither a represented deformation nor completed overlap covariance is
part of these data. Flow and end laws follow from strictness. -/
structure OriginalBundleCompletionMarkingData (L : OriginalBundleLiouvilleLaws P)
    (Z : Parameter → CompleteLiouvilleManifold d) where
  compact : ∀ s, TotalSpace M E → (Z s).manifold.Point
  chart : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E)) s
    (hs : s ∈ c.val.baseSet),
    (L.chartCompletion c s hs).ambient.manifold.SmoothEquiv (Z s).manifold
  primitive : ∀ c s hs,
    (L.chartCompletion c s hs).ambient.manifold.pullback (Z s).manifold (chart c s hs)
      (Z s).primitive = (L.chartCompletion c s hs).ambient.primitive
  native : ∀ c s hs x,
    chart c s hs ((L.chartCompletion c s hs).inclusion.map
      ((L.chartNativePresentation c s hs).localized.inclusion x)) =
        chartValue c.val (compact s) s x

namespace OriginalBundleCompletionMarkingData

variable {L : OriginalBundleLiouvilleLaws P} {Z : Parameter → CompleteLiouvilleManifold d}
  (O : OriginalBundleCompletionMarkingData L Z)

/-- The common original inclusion forces covariance through the actual
completed chart transition. This is the dimension-flexible strict-map
version of `OriginalBundleLiouvilleLaws.completedChartTransition_marking`. -/
theorem chart_overlap (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (s : Parameter) (hs : s ∈ c.val.baseSet ∩ c'.val.baseSet) :
    (L.completedChartTransition c c' s hs).equiv.trans (O.chart c' s hs.2) =
      O.chart c s hs.1 := by
  let a := L.completedChartTransition c c' s hs
  let A := (L.chartNativePresentation c s hs.1).localized
  apply (L.chartCompletion c s hs.1).equiv_eq_of_scaled_primitive_on_compact
    (Z s) (a.equiv.trans (O.chart c' s hs.2)) (O.chart c s hs.1) 1 1
  · change (L.chartCompletion c s hs.1).ambient.manifold.pullback (Z s).manifold
      (O.chart c' s hs.2 ∘ a.equiv) (Z s).primitive = _
    rw [(L.chartCompletion c s hs.1).ambient.manifold.pullback_comp
      (L.chartCompletion c' s hs.2).ambient.manifold (Z s).manifold
      (a.equiv.mdifferentiable (by simp)) ((O.chart c' s hs.2).mdifferentiable (by simp)),
      O.primitive, a.primitive, one_smul]
  · simpa only [one_smul] using O.primitive c s hs.1
  · intro z hz
    rw [← A.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    change O.chart c' s hs.2 (a.equiv _) = O.chart c s hs.1 _
    rw [a.compact, O.native, O.native]
    exact chartValue_coordChange c.val c'.val (O.compact s) hs x

variable {c c' : OriginalCompactChart (k := k) (M := M) (E := E)} {t t' : Parameter}

/-- The independent original marking on the retained local quotient. -/
def localEquiv (F : LocalCompletionFamily P c t) (s : Parameter) (hs : s ∈ F.base) :
    (F.sliceCompletion L s).ambient.manifold.SmoothEquiv (Z s).manifold :=
  (F.baseSliceComparison L s hs).equiv.trans (O.chart c s (F.base_subset hs))

theorem localEquiv_primitive (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) :
    (F.sliceCompletion L s).ambient.manifold.pullback (Z s).manifold
      (O.localEquiv F s hs) (Z s).primitive = (F.sliceCompletion L s).ambient.primitive := by
  change (F.sliceCompletion L s).ambient.manifold.pullback (Z s).manifold
    (O.chart c s (F.base_subset hs) ∘ (F.baseSliceComparison L s hs).equiv) _ = _
  rw [(F.sliceCompletion L s).ambient.manifold.pullback_comp
    (L.chartCompletion c s (F.base_subset hs)).ambient.manifold (Z s).manifold
    ((F.baseSliceComparison L s hs).equiv.mdifferentiable (by simp))
    ((O.chart c s (F.base_subset hs)).mdifferentiable (by simp)),
    O.primitive, (F.baseSliceComparison L s hs).primitive]

theorem localEquiv_native (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) (x : M) :
    O.localEquiv F s hs (original (F.native.patches s) x) =
      chartValue c.val (O.compact s) s x := by
  change O.chart c s (F.base_subset hs) ((F.baseSliceComparison L s hs).equiv _) = _
  rw [(F.baseSliceComparison L s hs).compact, O.native]

/-- Covariance on the entire retained quotient is derived from the
original chart covariance and the retained slice comparisons. -/
theorem localEquiv_overlap (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P c' t') (s : Parameter)
    (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (F.overlapEquiv G L s hF hG).trans (O.localEquiv G s hG) =
      O.localEquiv F s hF := by
  apply Diffeomorph.ext
  intro x
  change O.chart c' s (G.base_subset hG) ((G.baseSliceComparison L s hG).equiv
    ((G.baseSliceComparison L s hG).equiv.symm
      ((L.completedChartTransition c c' s ⟨F.base_subset hF, G.base_subset hG⟩).equiv
        ((F.baseSliceComparison L s hF).equiv x)))) = _
  rw [(G.baseSliceComparison L s hG).equiv.apply_symm_apply]
  exact congrArg (fun e => e ((F.baseSliceComparison L s hF).equiv x))
    (O.chart_overlap c c' s ⟨F.base_subset hF, G.base_subset hG⟩)

/-- The original local marking intertwines the actual complete flows for
every real time, as a consequence of primitive preservation. -/
theorem localEquiv_flow (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base)
    (x : (F.sliceCompletion L s).ambient.manifold.Point) (r : ℝ) :
    O.localEquiv F s hs ((F.sliceCompletion L s).ambient.completeFlow.flow r x) =
      (Z s).completeFlow.flow r (O.localEquiv F s hs x) :=
  (F.sliceCompletion L s).ambient.map_flow (Z s) (O.localEquiv F s hs)
    (O.localEquiv_primitive F s hs) x r

/-- The whole real boundary orbit retains the prescribed original
compact boundary inclusion; no end equation is an additional input. -/
theorem localEquiv_end (F : LocalCompletionFamily P c t)
    (s : Parameter) (hs : s ∈ F.base) (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    O.localEquiv F s hs ((F.sliceCompletion L s).endMap (b, r)) =
      (Z s).completeFlow.flow r (chartValue c.val (O.compact s) s b.val) := by
  rw [(F.sliceCompletion L s).end_flow, O.localEquiv_flow]
  have hz : (F.sliceCompletion L s).inclusion.map
      ((F.sliceNativePresentation L s).domain.domain.boundaryInclusion.map b) =
      original (F.native.patches s) b.val := by
    rw [← (F.sliceCompletion L s).endMap_zero]
    exact F.sliceCompletion_end_zero L s b
  rw [hz, O.localEquiv_native]

variable [NeZero d]

/-- Descend an independently prescribed original marking to this exact
retained endpoint. Its compact inclusion uses the one original bundle map
in the endpoint's global compact coordinates. -/
def endpointMarking (F : LocalCompletionFamily P c t)
    (g : Trivialization M (π M E)) (s : Parameter) (hs : s ∈ F.base)
    (hg : s ∈ g.baseSet) (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (a : LocalCompletionFamily.EndpointSliceComparison F L g s D C eM) :
    InclusionMarking C (Z s)
      (fun y => chartValue g (O.compact s) s (eM.symm y)) := by
  let ν := fun x => original (F.native.patches s) (g.coordChange c.val s x)
  have hc (x : M) : a.equiv (ν x) = C.inclusion.map (eM x).val := by
    dsimp [ν]
    rw [a.compact, g.coordChange_coordChange c.val g hg (F.base_subset hs),
      g.coordChange_same hg]
    rfl
  have hq (x : M) : O.localEquiv F s hs (ν x) = chartValue g (O.compact s) s x := by
    dsimp [ν]
    rw [O.localEquiv_native]
    exact chartValue_coordChange g c.val (O.compact s) ⟨hg, F.base_subset hs⟩ x
  exact C.inclusionMarkingOfNativeSliceEquiv
    (F.sliceCompletion L s).ambient.manifold (F.sliceCompletion L s).ambient.primitive
    a.equiv a.primitive eM.toEquiv ν hc (Z s) (chartValue g (O.compact s) s)
    (O.localEquiv F s hs) (O.localEquiv_primitive F s hs) hq

@[simp]
theorem endpointMarking_equiv (F : LocalCompletionFamily P c t)
    (g : Trivialization M (π M E)) (s : Parameter) (hs : s ∈ F.base)
    (hg : s ∈ g.baseSet) (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (a : LocalCompletionFamily.EndpointSliceComparison F L g s D C eM) :
    (O.endpointMarking F g s hs hg D C eM a).equiv =
      a.equiv.symm.trans (O.localEquiv F s hs) := rfl

/-- Descent recovers the original marking on the whole local completion. -/
theorem endpointMarking_recovers_original (F : LocalCompletionFamily P c t)
    (g : Trivialization M (π M E)) (s : Parameter) (hs : s ∈ F.base)
    (hg : s ∈ g.baseSet) (D : LiouvilleDomain d) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (a : LocalCompletionFamily.EndpointSliceComparison F L g s D C eM) :
    a.equiv.trans (O.endpointMarking F g s hs hg D C eM a).equiv =
      O.localEquiv F s hs := by
  apply Diffeomorph.ext
  intro x
  change O.localEquiv F s hs (a.equiv.symm (a.equiv x)) = O.localEquiv F s hs x
  rw [a.equiv.symm_apply_apply]

section EndpointLaws

variable (F : LocalCompletionFamily P c t)
  (g : Trivialization M (π M E)) (s : Parameter) (hs : s ∈ F.base)
  (hg : s ∈ g.baseSet) (D : LiouvilleDomain d) (C : Completion D)
  (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
  (a : LocalCompletionFamily.EndpointSliceComparison F L g s D C eM)

/-- The descended map retains the native compact inclusion in the exact
endpoint carrier, rather than selecting a new endpoint marking. -/
theorem endpointMarking_native (x : M) :
    (O.endpointMarking F g s hs hg D C eM a).equiv (C.inclusion.map (eM x).val) =
      chartValue g (O.compact s) s x := by
  simpa only [eM.symm_apply_apply] using
    (O.endpointMarking F g s hs hg D C eM a).inclusion (eM x)

/-- All real flow times use the actual endpoint and target complete flows. -/
theorem endpointMarking_flow (y : C.ambient.manifold.Point) (r : ℝ) :
    (O.endpointMarking F g s hs hg D C eM a).equiv (C.ambient.completeFlow.flow r y) =
      (Z s).completeFlow.flow r ((O.endpointMarking F g s hs hg D C eM a).equiv y) :=
  C.ambient.map_flow (Z s) (O.endpointMarking F g s hs hg D C eM a).equiv
    (O.endpointMarking F g s hs hg D C eM a).primitive y r

/-- The end law retains the original boundary inclusion for every real
radius, including the inward continuation of the boundary orbit. -/
theorem endpointMarking_end (b : D.domain.boundary.Point) (r : ℝ) :
    (O.endpointMarking F g s hs hg D C eM a).equiv (C.endMap (b, r)) =
      (Z s).completeFlow.flow r (chartValue g (O.compact s) s
        (eM.symm ⟨D.domain.boundaryInclusion.map b,
          D.domain.boundaryInclusion_mem_carrier b⟩)) := by
  let q := O.endpointMarking F g s hs hg D C eM a
  rw [q.flow_induced, q.inclusion
    ⟨D.domain.boundaryInclusion.map b, D.domain.boundaryInclusion_mem_carrier b⟩]

/-- In the original chart's native boundary coordinates the same end law
recovers the original common compact inclusion exactly. -/
theorem endpointMarking_end_native (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    (O.endpointMarking F g s hs hg D C eM a).equiv (C.endMap (a.boundary b, r)) =
      (Z s).completeFlow.flow r (chartValue c.val (O.compact s) s b.val) := by
  rw [← a.end_square]
  have h := congrArg (fun e => e ((F.sliceCompletion L s).endMap (b, r)))
    (O.endpointMarking_recovers_original F g s hs hg D C eM a)
  exact h.trans (O.localEquiv_end F s hs b r)

/-- Every original local chart and every strict endpoint comparison give
the same actual descended diffeomorphism on the whole endpoint.
The proof uses both derived original-marking covariance and the inverse
coherence of the independently constructed endpoint comparisons. -/
theorem endpointMarking_choice_independent (G : LocalCompletionFamily P c' t')
    (hG : s ∈ G.base)
    (b : LocalCompletionFamily.EndpointSliceComparison G L g s D C eM) :
    (O.endpointMarking F g s hs hg D C eM a).equiv =
      (O.endpointMarking G g s hG hg D C eM b).equiv := by
  apply Diffeomorph.ext
  intro y
  change O.localEquiv F s hs (a.equiv.symm y) = O.localEquiv G s hG (b.equiv.symm y)
  have h := congrArg (fun e => e (a.equiv.symm y))
    (O.localEquiv_overlap F G s hs hG)
  change O.localEquiv G s hG (F.overlapEquiv G L s hs hG (a.equiv.symm y)) =
    O.localEquiv F s hs (a.equiv.symm y) at h
  rw [a.overlap_inverse F G L g s hs hG D C eM b] at h
  exact h.symm

/-- The marking descended using one chart recovers every original local
marking, on its whole completion, through that chart's endpoint comparison. -/
theorem endpointMarking_recovers_all_charts (G : LocalCompletionFamily P c' t')
    (hG : s ∈ G.base)
    (b : LocalCompletionFamily.EndpointSliceComparison G L g s D C eM) :
    b.equiv.trans (O.endpointMarking F g s hs hg D C eM a).equiv =
      O.localEquiv G s hG := by
  rw [O.endpointMarking_choice_independent F g s hs hg D C eM a G hG b]
  exact O.endpointMarking_recovers_original G g s hG hg D C eM b

end EndpointLaws

section Ambient

variable {n : ℕ} [NeZero n] {W : Parameter → CompleteLiouvilleManifold (2 * n)}
  (A : OriginalBundleCompletionMarkingData L W)
  (F : LocalCompletionFamily P c t)
  (g : Trivialization M (π M E))
  (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g) (hbase : g.baseSet = univ)
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ u, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
    M (Q.pair u).ambientDomain.domain.Point ∞)
  (hp : ∀ u x, ((Q.pair u).ambientDomain.liouville.primitive (eAs u x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs u y).val) x) =
      P.formInTrivialization g u x)
  (hc : ∀ u, HasNativeCoordinateExtensions (k := k)
    (Q.pair u).ambientDomain.domain.extension (fun x => (eAs u x).val))

/-- The source-only original marking data produce an inclusion marking on
the exact ambient completion of the same already supplied deformation.
The endpoint comparison is constructed from its actual native laws. -/
def ambientMarking (s : Parameter) (hs : s ∈ F.base) :
    InclusionMarking (Q.pair s).ambientCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eAs s).symm y)) :=
  A.endpointMarking F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc)

/-- The same deformation's literal retained compact inclusion recovers
the prescribed original common compact bundle map. -/
theorem ambientMarking_native (s : Parameter) (hs : s ∈ F.base) (x : M) :
    (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv
      ((Q.pair s).ambientCompletion.inclusion.map (eAs s x).val) =
        chartValue g (A.compact s) s x :=
  A.endpointMarking_native F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) x

/-- The whole original local marking is recovered through the exact
endpoint comparison used on this same pair deformation. -/
theorem ambientMarking_recovers_original (s : Parameter) (hs : s ∈ F.base) :
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc).equiv.trans
      (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv =
        A.localEquiv F s hs :=
  A.endpointMarking_recovers_original F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc)

/-- The exact same ambient completion and its complete flow satisfy the
transport equation at every real time. -/
theorem ambientMarking_flow (s : Parameter) (hs : s ∈ F.base)
    (y : (Q.pair s).ambientCompletion.ambient.manifold.Point) (r : ℝ) :
    (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv
      ((Q.pair s).ambientCompletion.ambient.completeFlow.flow r y) =
      (W s).completeFlow.flow r
        ((A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv y) :=
  A.endpointMarking_flow F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) y r

/-- On every real boundary orbit, the same ambient marking recovers the
prescribed inclusion of the original compact boundary point. -/
theorem ambientMarking_end_native (s : Parameter) (hs : s ∈ F.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv
      ((Q.pair s).ambientCompletion.endMap
        ((F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc).boundary b, r)) =
      (W s).completeFlow.flow r (chartValue c.val (A.compact s) s b.val) :=
  A.endpointMarking_end_native F g s hs (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) b r

/-- The same ambient marking is independent of the original local chart
used to construct it, throughout each whole completed endpoint. -/
theorem ambientMarking_choice_independent (G : LocalCompletionFamily P c' t')
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hF).equiv =
      (A.ambientMarking G g hg hbase Q hdim eAs hp hc s hG).equiv :=
  A.endpointMarking_choice_independent F g s hF (by rw [hbase]; exact mem_univ s)
    (Q.pair s).ambientDomain (Q.pair s).ambientCompletion (eAs s)
    (F.ambientEndpointSliceComparison L g hg hbase s hF Q hdim eAs hp hc) G hG
    (G.ambientEndpointSliceComparison L g hg hbase s hG Q hdim eAs hp hc)

/-- Descend at every actual parameter using an original atlas chart that
contains it and the already constructed local completion family. This
pointwise choice imposes no smoothness on the choice of chart. -/
def ambientMarkingAt (s : Parameter) :
    InclusionMarking (Q.pair s).ambientCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eAs s).symm y)) := by
  let c₀ : OriginalCompactChart (k := k) (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs₀ : s ∈ c₀.val.baseSet := mem_baseSet_trivializationAt _ _ _
  let F₀ := L.localCompletionFamily c₀ s hs₀
  exact A.ambientMarking F₀ g hg hbase Q hdim eAs hp hc s F₀.base_mem

/-- The parameterwise descended marking recovers every supplied original
local chart on its whole completion. Thus the arbitrary original chart
used to define it has no effect on the returned marking. -/
theorem ambientMarkingAt_recovers_original (s : Parameter) (hs : s ∈ F.base) :
    (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc).equiv.trans
      (A.ambientMarkingAt g hg hbase Q hdim eAs hp hc s).equiv =
        A.localEquiv F s hs := by
  let c₀ : OriginalCompactChart (k := k) (M := M) (E := E) :=
    ⟨trivializationAt M E s, trivialization_mem_atlas _ _ _⟩
  have hs₀ : s ∈ c₀.val.baseSet := mem_baseSet_trivializationAt _ _ _
  let F₀ := L.localCompletionFamily c₀ s hs₀
  have he : (A.ambientMarkingAt g hg hbase Q hdim eAs hp hc s).equiv =
      (A.ambientMarking F g hg hbase Q hdim eAs hp hc s hs).equiv :=
    A.ambientMarking_choice_independent F₀ g hg hbase Q hdim eAs hp hc
      F s F₀.base_mem hs
  rw [he]
  exact A.ambientMarking_recovers_original F g hg hbase Q hdim eAs hp hc s hs

/-- Source-only original markings give an actual endpoint inclusion
marking at every parameter, together with literal recovery in all
original local charts. Only marking existence on the source is supplied. -/
theorem exists_ambientMarking (s : Parameter) :
    ∃ q : InclusionMarking (Q.pair s).ambientCompletion (W s)
      (fun y => chartValue g (A.compact s) s ((eAs s).symm y)),
      ∀ (c₀ : OriginalCompactChart (k := k) (M := M) (E := E)) (t₀ : Parameter)
        (G : LocalCompletionFamily P c₀ t₀) (hs : s ∈ G.base),
        (G.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc).equiv.trans
          q.equiv = A.localEquiv G s hs := by
  refine ⟨A.ambientMarkingAt g hg hbase Q hdim eAs hp hc s, ?_⟩
  intro c₀ t₀ G hs
  exact A.ambientMarkingAt_recovers_original G g hg hbase Q hdim eAs hp hc s hs

end Ambient

end OriginalBundleCompletionMarkingData
end FsFltz.Geometry.IntrinsicSmoothBundle
