import FsFltz.Geometry.IntrinsicNativeRibbonCompletionFamily
import FsFltz.Geometry.NativeSliceInclusionMarking

/-!
# Original ribbon markings on the same retained completion slices

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 143–160;
`g:initial`, lines 374–384; and `sec:lean`, lines 788–814.
The strict and native compact equations of the already selected ribbon
slices transport a supplied original marking to the ribbon completion of
the same pair. The chosen comparison, native carrier map and original
marking are retained. In dimension zero primitive preservation is automatic.
Existence of target-specific full-fiber markings remains a geometric obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace FsFltz.Geometry.PairDeformation
open IntrinsicCompletionGluing IntrinsicLiouville

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs) (t : Parameter)
  (Z : CompleteLiouvilleManifold (2 * n - 2)) (i : M → Z.manifold.Point)
  (q : (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
    (S.collar_zero t)).SmoothEquiv Z.manifold)
  (hq : (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
    (S.collar_zero t)).pullback Z.manifold q Z.primitive = S.primitive t)
  (hcompact : ∀ x, q (original (fun p => S.collar t p.val) x) = i x)

/-- The retained ribbon slice comparison transports the supplied original
marking onto the exact ribbon completion of this same pair. -/
def transportOriginalMarking : InclusionMarking (Q.pair t).ribbonCompletion Z
    (fun y => i ((eMs t).symm y)) :=
  (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t))
    (S.primitive t) (S.comparison t) (S.comparison_primitive t)
    (eMs t).toEquiv (original (fun p => S.collar t p.val)) (S.comparison_native t)
    Z i q hq hcompact

include hq hcompact in
/-- Actual marking transport using the exact chosen ribbon slices, including
the original map on the whole source and its native boundary trajectories. -/
theorem exists_originalMarking_on_same_ribbonCompletion :
    ∃ m : InclusionMarking (Q.pair t).ribbonCompletion Z (fun y => i ((eMs t).symm y)),
      m.equiv = (S.comparison t).symm.trans q ∧
      (S.comparison t).trans m.equiv = q ∧
      (∀ x, m.equiv ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val) = i x) ∧
      (∀ (b : IntrinsicBoundary.Point k M) (r : ℝ),
        m.equiv ((Q.pair t).ribbonCompletion.endMap (S.boundary_comparison t b, r)) =
          Z.completeFlow.flow r (i b.val)) := by
  let m := S.transportOriginalMarking t Z i q hq hcompact
  refine ⟨m, rfl, ?_, ?_, ?_⟩
  · exact (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv_recovers_original
      _ _ _ _ _ _ _ _ _ _ _ _
  · intro x
    exact (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv_native
      _ _ _ _ _ _ _ _ _ _ _ _ x
  · intro b r
    rw [m.flow_induced, S.boundary_native t b]
    have hn := m.inclusion (eMs t b.val)
    simpa only [(eMs t).symm_apply_apply] using congrArg (Z.completeFlow.flow r) hn

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation

namespace FsFltz.Geometry.PairDeformation
open IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {Q : PairDeformation 1} {μ : Parameter → (sourceManifold M).Form 1}
  {eFs : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeZeroRibbonCompletionSlices

variable (S : NativeZeroRibbonCompletionSlices Q μ eFs) (t : Parameter)
  (Z : CompleteLiouvilleManifold 0) (i : M → Z.manifold.Point)
  (q : (sourceManifold M).SmoothEquiv Z.manifold) (hcompact : ∀ x, q x = i x)

/-- Zero-dimensional original ribbon markings are transported through the
same selected canonical slice. All one-forms vanish, so no primitive
preservation hypothesis is imposed on the supplied marking. -/
def transportOriginalMarking : InclusionMarking (Q.pair t).ribbonCompletion Z
    (fun y => i ((eFs t).symm y)) :=
  (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv
    (sourceManifold M) (μ t) (S.comparison t) (S.comparison_primitive t)
    (eFs t).toEquiv id (S.comparison_native t) Z i q
    (((sourceManifold M).oneForm_eq_zero_of_dimension_zero _).trans
      ((sourceManifold M).oneForm_eq_zero_of_dimension_zero _).symm) hcompact

include hcompact in
/-- The same zero ribbon completion retains the original whole-source
marking, native compact inclusion and actual complete-flow transport. -/
theorem exists_originalMarking_on_same_ribbonCompletion :
    ∃ m : InclusionMarking (Q.pair t).ribbonCompletion Z (fun y => i ((eFs t).symm y)),
      m.equiv = (S.comparison t).symm.trans q ∧
      (S.comparison t).trans m.equiv = q ∧
      (∀ x, m.equiv ((Q.pair t).ribbonCompletion.inclusion.map (eFs t x).val) = i x) ∧
      (∀ z r, m.equiv ((Q.pair t).ribbonCompletion.ambient.completeFlow.flow r z) =
        Z.completeFlow.flow r (m.equiv z)) := by
  let m := S.transportOriginalMarking t Z i q hcompact
  refine ⟨m, rfl, ?_, ?_, ?_⟩
  · exact (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv_recovers_original
      _ _ _ _ _ _ _ _ _ _ _ _
  · intro x
    exact (Q.pair t).ribbonCompletion.inclusionMarkingOfNativeSliceEquiv_native
      _ _ _ _ _ _ _ _ _ _ _ _ x
  · exact (Q.pair t).ribbonCompletion.ambient.map_flow Z m.equiv m.primitive

end NativeZeroRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
