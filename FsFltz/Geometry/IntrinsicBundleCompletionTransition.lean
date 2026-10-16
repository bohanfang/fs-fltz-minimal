import FsFltz.Geometry.IntrinsicBundlePairFamily
import FsFltz.Geometry.IntrinsicNativeMapCompletion
import FsFltz.Geometry.IntrinsicBundleNativeTransitionExtensions
import FsFltz.Geometry.CompletionMapUniqueness

/-!
# Completed transitions of the original compact bundle atlas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
Original-atlas primitive and Liouville laws construct a native presentation
and completion of each chart at each actual parameter. The original
compact chart transition germs then produce strict completed maps.
Their identity, inverse and cocycle equations follow from the compact bundle
equations and uniqueness on the whole completion, including every end orbit.
No completed comparison or completion is an input to these constructions.

The native transition extension laws are derived from the original bundle
transition and self-transition germs. Proving joint completed regularity,
gluing the completed atlas, and descending an independently preselected
section remain separate foundations. This module does not construct the geometric target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- An original atlas chart, before any global compact or completed
trivialization is selected. -/
abbrev OriginalCompactChart :=
  {e : Trivialization M (π M E) // e ∈ trivializationAtlas M E}

namespace OriginalBundleLiouvilleLaws

variable {P : BundlePrimitiveData (k := k) (M := M) E}

/-- Choose each native chart presentation from the original local
primitive laws; no represented family or completed map is supplied. -/
def chartNativePresentation (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    NativeLiouvillePresentation (P.form c t) :=
  Classical.choice (L.nativePresentation c t ht)

/-- The proved collar and cylindrical construction completes the original
chart's selected native presentation. -/
abbrev chartCompletion (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :=
  (L.chartNativePresentation c t ht).localizedCompletion

/-- The original compact atlas transition, with smoothness derived from
the bundle's joint coordinate germs. -/
def chartTransition (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet) :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞ :=
  transitionDiffeomorphOfCompatible c.val c'.val
    (compatibleTrivialization_of_mem c.property)
    (compatibleTrivialization_of_mem c'.property) ht

/-- Source covariance derives the full native primitive equation of
the actual compact transition. It is not an extra comparison assumption. -/
theorem chartTransition_primitive
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet) (x : M) :
    (P.form c' t (chartTransition c c' t ht x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (chartTransition c c' t ht) x) =
        P.form c t x := by
  exact (congrFun (P.covariance c c' t ht) x).symm

/-- This is produced comparison data on the independently constructed
original chart completions. The whole native compact map is retained. -/
structure CompletedChartTransition (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet) where
  equiv : (L.chartCompletion c t ht.1).ambient.manifold.SmoothEquiv
    (L.chartCompletion c' t ht.2).ambient.manifold
  boundary : (L.chartNativePresentation c t ht.1).domain.domain.boundary.SmoothEquiv
    (L.chartNativePresentation c' t ht.2).domain.domain.boundary
  primitive : (L.chartCompletion c t ht.1).ambient.manifold.pullback
    (L.chartCompletion c' t ht.2).ambient.manifold equiv
    (L.chartCompletion c' t ht.2).ambient.primitive =
      (L.chartCompletion c t ht.1).ambient.primitive
  compact : ∀ x, equiv ((L.chartCompletion c t ht.1).inclusion.map
      ((L.chartNativePresentation c t ht.1).localized.inclusion x)) =
    (L.chartCompletion c' t ht.2).inclusion.map
      ((L.chartNativePresentation c' t ht.2).localized.inclusion
        (c.val.coordChange c'.val t x))
  compact_inverse : ∀ x, equiv.symm ((L.chartCompletion c' t ht.2).inclusion.map
      ((L.chartNativePresentation c' t ht.2).localized.inclusion x)) =
    (L.chartCompletion c t ht.1).inclusion.map
      ((L.chartNativePresentation c t ht.1).localized.inclusion
        ((chartTransition c c' t ht).symm x))
  end_square : ∀ x r, 0 ≤ r →
    equiv ((L.chartCompletion c t ht.1).endMap (x, r)) =
      (L.chartCompletion c' t ht.2).endMap (boundary x, r)

/-- Construct a strict completed transition from the actual original
compact map and source primitive covariance. Both chart completions are
constructed from original Liouville data in this same invocation. -/
def completedChartTransition (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet) :
    CompletedChartTransition L c c' t ht := by
  exact Classical.choice (show Nonempty (CompletedChartTransition L c c' t ht) from by
    let A := L.chartNativePresentation c t ht.1
    let B := L.chartNativePresentation c' t ht.2
    obtain ⟨e, b, hp, hs, hi, _, he⟩ :=
      A.localized.exists_strictCompletionEquiv_of_nativeDiffeomorph B.localized
        (chartTransition c c' t ht)
        (isLocallyExtendibleNativeMap_coordChange c.val c'.val c.property c'.property ht)
        (chartTransition_primitive c c' t ht) A.localizedCompletion B.localizedCompletion
    exact ⟨⟨e, b, hp, hs, hi, he⟩⟩)

/-- A strict completed map is uniquely determined by the whole original
native compact chart. No end equation is a uniqueness assumption. -/
theorem CompletedChartTransition.equiv_unique (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet)
    (a b : CompletedChartTransition L c c' t ht) : a.equiv = b.equiv := by
  apply (L.chartCompletion c t ht.1).equiv_eq_of_scaled_primitive_on_compact
    (L.chartCompletion c' t ht.2).ambient a.equiv b.equiv 1 1
  · simpa only [one_smul] using a.primitive
  · simpa only [one_smul] using b.primitive
  · intro z hz
    rw [← (L.chartNativePresentation c t ht.1).localized.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact (a.compact x).trans (b.compact x).symm

/-- The strict transition carries the actual completed Liouville field;
this equation follows from its primitive equation. -/
theorem CompletedChartTransition.map_field (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet)
    (a : CompletedChartTransition L c c' t ht)
    (x : (L.chartCompletion c t ht.1).ambient.manifold.Point) :
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) a.equiv x
      ((L.chartCompletion c t ht.1).ambient.field x) =
        (L.chartCompletion c' t ht.2).ambient.field (a.equiv x) :=
  (L.chartCompletion c t ht.1).ambient.map_field
    (L.chartCompletion c' t ht.2).ambient a.equiv a.primitive x

/-- All real time directions of the same original completed flow are
preserved by the produced transition. -/
theorem CompletedChartTransition.map_flow (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet)
    (a : CompletedChartTransition L c c' t ht)
    (x : (L.chartCompletion c t ht.1).ambient.manifold.Point) (r : ℝ) :
    a.equiv ((L.chartCompletion c t ht.1).ambient.completeFlow.flow r x) =
      (L.chartCompletion c' t ht.2).ambient.completeFlow.flow r (a.equiv x) :=
  (L.chartCompletion c t ht.1).ambient.map_flow
    (L.chartCompletion c' t ht.2).ambient a.equiv a.primitive x r

/-- The end equation extends to the entire actual boundary orbit,
including negative radius, by the proved flow transport. -/
theorem CompletedChartTransition.end_square_all_real (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet)
    (a : CompletedChartTransition L c c' t ht)
    (x : (L.chartNativePresentation c t ht.1).domain.domain.boundary.Point) (r : ℝ) :
    a.equiv ((L.chartCompletion c t ht.1).endMap (x, r)) =
      (L.chartCompletion c' t ht.2).endMap (a.boundary x, r) := by
  have hzero := a.end_square x 0 (le_refl 0)
  rw [(L.chartCompletion c t ht.1).endMap_zero,
    (L.chartCompletion c' t ht.2).endMap_zero] at hzero
  rw [(L.chartCompletion c t ht.1).end_flow,
    (L.chartCompletion c' t ht.2).end_flow, a.map_flow L c c' t ht, hzero]

/-- Source chart identity extends to literal identity on its entire
constructed completion. -/
theorem completedChartTransition_self (L : OriginalBundleLiouvilleLaws P)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) :
    (L.completedChartTransition c c t ⟨ht, ht⟩).equiv =
      Diffeomorph.refl 𝓘(ℝ, Model (k + 1)) (L.chartCompletion c t ht).ambient.manifold.Point ∞ := by
  let a := L.completedChartTransition c c t ⟨ht, ht⟩
  apply (L.chartCompletion c t ht).equiv_eq_of_scaled_primitive_on_compact
    (L.chartCompletion c t ht).ambient a.equiv _ 1 1
  · simpa only [one_smul] using a.primitive
  · simpa only [one_smul, Diffeomorph.coe_refl] using
      (L.chartCompletion c t ht).ambient.manifold.pullback_id
        (L.chartCompletion c t ht).ambient.primitive
  · intro z hz
    rw [← (L.chartNativePresentation c t ht).localized.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    simpa only [c.val.coordChange_same ht, id_eq, Diffeomorph.coe_refl] using a.compact x

/-- Actual compact chart composition determines completed composition on
every compact and cylindrical point; choices of extension cancel. -/
theorem completedChartTransition_cocycle (L : OriginalBundleLiouvilleLaws P)
    (c c' c'' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (hc : t ∈ c.val.baseSet) (hc' : t ∈ c'.val.baseSet)
    (hc'' : t ∈ c''.val.baseSet) :
    (L.completedChartTransition c c' t ⟨hc, hc'⟩).equiv.trans
      (L.completedChartTransition c' c'' t ⟨hc', hc''⟩).equiv =
        (L.completedChartTransition c c'' t ⟨hc, hc''⟩).equiv := by
  let a := L.completedChartTransition c c' t ⟨hc, hc'⟩
  let b := L.completedChartTransition c' c'' t ⟨hc', hc''⟩
  let f := L.completedChartTransition c c'' t ⟨hc, hc''⟩
  apply (L.chartCompletion c t hc).equiv_eq_of_scaled_primitive_on_compact
    (L.chartCompletion c'' t hc'').ambient (a.equiv.trans b.equiv) f.equiv 1 1
  · change (L.chartCompletion c t hc).ambient.manifold.pullback
      (L.chartCompletion c'' t hc'').ambient.manifold (b.equiv ∘ a.equiv) _ = _
    rw [(L.chartCompletion c t hc).ambient.manifold.pullback_comp
      (L.chartCompletion c' t hc').ambient.manifold
      (L.chartCompletion c'' t hc'').ambient.manifold
      (a.equiv.mdifferentiable (by simp)) (b.equiv.mdifferentiable (by simp)),
      b.primitive, a.primitive, one_smul]
  · simpa only [one_smul] using f.primitive
  · intro z hz
    rw [← (L.chartNativePresentation c t hc).localized.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    change b.equiv (a.equiv _) = f.equiv _
    rw [a.compact, b.compact, f.compact,
      c.val.coordChange_coordChange c'.val c''.val hc hc' x]

/-- The opposite actual chart transition is the inverse completed map,
as a consequence of the cocycle and identity equations. -/
theorem completedChartTransition_symm (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet) :
    (L.completedChartTransition c c' t ht).equiv.symm =
      (L.completedChartTransition c' c t ⟨ht.2, ht.1⟩).equiv := by
  apply Diffeomorph.ext
  intro x
  let a := L.completedChartTransition c c' t ht
  let b := L.completedChartTransition c' c t ⟨ht.2, ht.1⟩
  have h := congrArg (fun f => f (a.equiv.symm x))
    (L.completedChartTransition_cocycle c c' c t ht.1 ht.2 ht.1)
  rw [L.completedChartTransition_self c t ht.1] at h
  change b.equiv (a.equiv (a.equiv.symm x)) = a.equiv.symm x at h
  rw [a.equiv.apply_symm_apply] at h
  exact h.symm

/-- Original inclusion markings agree through the constructed atlas
transition on the whole completed ambient. The compact comparison is the
actual coordinate identity of one original bundle map; end agreement is
derived by uniqueness, not imposed as another marking equation. -/
theorem completedChartTransition_marking (L : OriginalBundleLiouvilleLaws P)
    (c c' : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet ∩ c'.val.baseSet)
    (X : CompleteLiouvilleManifold (k + 1)) (ν : TotalSpace M E → X.manifold.Point)
    (q : InclusionMarking (L.chartCompletion c t ht.1) X
      (fun z => chartValue c.val ν t
        ((L.chartNativePresentation c t ht.1).localized.carrierEquiv.symm z)))
    (q' : InclusionMarking (L.chartCompletion c' t ht.2) X
      (fun z => chartValue c'.val ν t
        ((L.chartNativePresentation c' t ht.2).localized.carrierEquiv.symm z))) :
    (L.completedChartTransition c c' t ht).equiv.trans q'.equiv = q.equiv := by
  let a := L.completedChartTransition c c' t ht
  let A := (L.chartNativePresentation c t ht.1).localized
  let B := (L.chartNativePresentation c' t ht.2).localized
  have hq (x : M) : q.equiv ((L.chartCompletion c t ht.1).inclusion.map (A.inclusion x)) =
      chartValue c.val ν t x := by
    have h := q.inclusion (A.carrierEquiv x)
    rw [A.carrier_square, A.carrierEquiv.symm_apply_apply] at h
    exact h
  have hq' (x : M) : q'.equiv ((L.chartCompletion c' t ht.2).inclusion.map (B.inclusion x)) =
      chartValue c'.val ν t x := by
    have h := q'.inclusion (B.carrierEquiv x)
    rw [B.carrier_square, B.carrierEquiv.symm_apply_apply] at h
    exact h
  apply (L.chartCompletion c t ht.1).equiv_eq_of_scaled_primitive_on_compact
    X (a.equiv.trans q'.equiv) q.equiv 1 1
  · change (L.chartCompletion c t ht.1).ambient.manifold.pullback X.manifold
      (q'.equiv ∘ a.equiv) X.primitive = _
    rw [(L.chartCompletion c t ht.1).ambient.manifold.pullback_comp
      (L.chartCompletion c' t ht.2).ambient.manifold X.manifold
      (a.equiv.mdifferentiable (by simp)) (q'.equiv.mdifferentiable (by simp)),
      q'.primitive, a.primitive, one_smul]
  · simpa only [one_smul] using q.primitive
  · intro z hz
    rw [← A.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    change q'.equiv (a.equiv _) = q.equiv _
    rw [a.compact, hq', hq]
    exact chartValue_coordChange c.val c'.val ν ht x

end OriginalBundleLiouvilleLaws
end FsFltz.Geometry.IntrinsicSmoothBundle
