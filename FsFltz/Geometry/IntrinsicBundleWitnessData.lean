import FsFltz.Geometry.IntrinsicBundleBoundaryTransport
import FsFltz.Geometry.IntrinsicBundleTargetComposition

/-!
# Original-atlas positive boundary witnesses

Source: `geoemtric-part-fsf.tex`, `def:pair`, 132–146, `def:chain`,
163–169, and `sec:lean`, 788–814. Witnesses are supplied only in the
original ambient bundle atlas, with local germs and actual boundary-chart
covariance. Their values, positivity and joint germs in a constructed
compatible chart are conclusions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- Positive witness data in the original ambient bundle charts. The
covariance equation compares every boundary point, not only a ribbon core. -/
structure BundleWitnessData (E : Parameter → Type*) [∀ t, TopologicalSpace (E t)]
    [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E] where
  witness : {e : Trivialization M (π M E) // e ∈ trivializationAtlas M E} →
    Parameter → IntrinsicBoundary.Point k M → ℝ
  smooth : ∀ e, HasSmoothValueFamilyOn 𝓘(ℝ, Model k) e.val.baseSet (witness e)
  positive : ∀ e t, t ∈ e.val.baseSet → ∀ x, 0 < witness e t x
  covariance : ∀ e e', ∀ t ∈ e.val.baseSet ∩ e'.val.baseSet, ∀ x,
    witness e t x = witness e' t
      (boundaryFamilyOn (e.val.baseSet ∩ e'.val.baseSet) (e.val.coordChange e'.val)
        (compatibleTransition_boundary e.val e'.val
          (compatibleTrivialization_of_mem e.property)
          (compatibleTrivialization_of_mem e'.property)) t x)

namespace BundleWitnessData

/-- Present the actual source witness through the actual induced native
boundary map into an original atlas chart at each parameter. -/
def witnessInTrivialization (P : BundleWitnessData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e) :
    Parameter → IntrinsicBoundary.Point k M → ℝ := fun t x =>
  let c := trivializationAt M E t
  let hc := trivialization_mem_atlas M E t
  P.witness ⟨c, hc⟩ t
    (boundaryFamilyOn (e.baseSet ∩ c.baseSet) (e.coordChange c)
      (compatibleTransition_boundary e c he (compatibleTrivialization_of_mem hc)) t x)

/-- On each original chart overlap, the timewise chosen original chart
can be replaced by that fixed chart using literal native boundary maps. -/
theorem witnessInTrivialization_eq (P : BundleWitnessData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (c : Trivialization M (π M E)) (hc : c ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ c.baseSet) (x : IntrinsicBoundary.Point k M) :
    P.witnessInTrivialization e he t x = P.witness ⟨c, hc⟩ t
      (boundaryFamilyOn (e.baseSet ∩ c.baseSet) (e.coordChange c)
        (compatibleTransition_boundary e c he (compatibleTrivialization_of_mem hc)) t x) := by
  let d := trivializationAt M E t
  have hd : d ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htd : t ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
  rw [P.covariance ⟨c, hc⟩ ⟨d, hd⟩ t ⟨ht.2, htd⟩]
  unfold witnessInTrivialization
  apply congrArg (P.witness ⟨d, hd⟩ t)
  apply Subtype.ext
  simp only [boundaryFamilyOn,
    dite_eq_left (show t ∈ e.baseSet ∩ (trivializationAt M E t).baseSet from ⟨ht.1, htd⟩),
    dite_eq_left (show t ∈ c.baseSet ∩ d.baseSet from ⟨ht.2, htd⟩), dite_eq_left ht]
  exact (e.coordChange_coordChange c d ht.1 ht.2 x.val).symm

/-- The descended witness recovers each original native boundary value. -/
theorem witnessInTrivialization_eq_original (P : BundleWitnessData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : e ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet) (x : IntrinsicBoundary.Point k M) :
    P.witnessInTrivialization e (compatibleTrivialization_of_mem he) t x =
      P.witness ⟨e, he⟩ t x := by
  rw [P.witnessInTrivialization_eq e (compatibleTrivialization_of_mem he) e he ⟨ht, ht⟩]
  apply congrArg (P.witness ⟨e, he⟩ t)
  apply Subtype.ext
  rw [boundaryFamilyOn_val _ (show t ∈ e.baseSet ∩ e.baseSet from ⟨ht, ht⟩), e.coordChange_same ht]
  rfl

/-- Positivity is retained at every original interval parameter. No
positivity condition on the off-interval extension is imposed. -/
theorem witnessInTrivialization_positive (P : BundleWitnessData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (t : Parameter) (x : IntrinsicBoundary.Point k M) :
    0 < P.witnessInTrivialization e he t x :=
  P.positive ⟨trivializationAt M E t, trivialization_mem_atlas M E t⟩ t
    (mem_baseSet_trivializationAt _ _ _) _

/-- Actual boundary-valued transition germs transport the original
witness germs to any compatible chart. -/
theorem smooth_in_compatible_chart (P : BundleWitnessData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e) :
    HasSmoothValueFamilyOn 𝓘(ℝ, Model k) e.baseSet (P.witnessInTrivialization e he) := by
  apply HasSmoothValueFamilyOn.of_locally
  intro t ht
  let c := trivializationAt M E t
  have hc : c ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨c.baseSet, c.open_baseSet, htc, ?_⟩
  have hb := ((P.smooth ⟨c, hc⟩).mono (T := e.baseSet ∩ c.baseSet) inter_subset_right).native_value
    (IntrinsicBoundary.smoothManifold k M)
  exact ((compatibleTransition_boundary_germs e c he (compatibleTrivialization_of_mem hc)).postcomp_value
    (IntrinsicBoundary.smoothManifold k M) hb).congr
      (fun s hs x => (P.witnessInTrivialization_eq e he c hc hs x).symm)

/-- A constructed global chart carries the original positive witness as
the native scalar family used by the completed-pair constructor. -/
theorem exists_global_chart (P : BundleWitnessData (k := k) (M := M) E) :
    ∃ e : Trivialization M (π M E), e.baseSet = univ ∧
      ∃ he : CompatibleTrivialization (𝓡∂ (k + 1)) E e,
        (IntrinsicBoundary.smoothManifold k M).IsLocallyExtendibleIntervalScalarFamily
          (P.witnessInTrivialization e he) ∧
        ∀ t x, 0 < P.witnessInTrivialization e he t x := by
  obtain ⟨e, hbase, he⟩ := exists_global_smooth_trivialization
    (I := 𝓡∂ (k + 1)) (F := M) (E := E)
  refine ⟨e, hbase, he, ?_, P.witnessInTrivialization_positive e he⟩
  apply HasSmoothValueFamilyOn.native_scalar (IntrinsicBoundary.smoothManifold k M)
  simpa only [hbase] using P.smooth_in_compatible_chart e he

end BundleWitnessData
end FsFltz.Geometry.IntrinsicSmoothBundle
