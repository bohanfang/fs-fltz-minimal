import FsFltz.Geometry.IntrinsicBundlePairFamily
import FsFltz.Geometry.IntrinsicBundleLocalCompletionJointComparison

/-!
# One original bundle realization compares all its local completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
Original positive-dimensional pair-bundle data choose one compatible global
chart and one pair deformation before quantifying over the original local
charts. Each retained local completion then maps to that same reference
completion with real open germs and its exact varying slice primitive.
No completed comparison, real extension, or represented family is an input.
Inverse joint regularity and preselected-section descent remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FsFltz.Geometry Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicSmoothBundle
open FsFltz.Geometry.IntrinsicSmoothBundle.OriginalBundleLiouvilleLaws
open FsFltz.Geometry.IntrinsicCompletionGluing
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]

/-- Choose the global realization once from the original pair bundle.
All original local charts are then compared with that same completed family.
This constructor treats positive-dimensional ribbons. -/
theorem exists_localCompletionComparisons_of_original_bundle_data
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (PA : BundlePrimitiveData (k := a) (M := A) EA)
    (PM : BundlePrimitiveData (k := k) (M := M) EM)
    (PW : BundleWitnessData (k := a) (M := A) EA)
    (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
    (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
    (LP : OriginalBundlePairLaws PA PM PW PJ)
    : ∃ (g : Trivialization A (π A EA))
      (hg : CompatibleTrivialization (𝓡∂ (a + 1)) EA g)
      (hbase : g.baseSet = Set.univ) (Q : PairDeformation n)
      (eAs : ∀ s, Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A
        (Q.pair s).ambientDomain.domain.Point ∞)
      (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization g s x)
      (hc : ∀ s, HasNativeCoordinateExtensions (k := a)
        (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
        (t : Parameter) (ht : t ∈ c.val.baseSet),
        let F := LA.localCompletionFamily c t ht
        (letI := F.native.totalCharts
         HasRealOpenMapGermsOn (familyModel (a + 1))
           Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
           (F.ambientReferenceTotalMap LA g hg hbase Q hdimA eAs hp hc)) ∧
        ∀ s (hs : s ∈ F.base),
          (F.sliceCompletion LA s).ambient.manifold.pullback Q.source.ambientCompletion.ambient.manifold
            (fun x => F.ambientReferenceTotalMap LA g hg hbase Q hdimA eAs hp hc
              ⟨sliceIn F.native.patches s x, by simpa only [LocalCompletionFamily.localSource,
                Set.mem_preimage, TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩)
            (Q.completedPrimitive s) = (F.sliceCompletion LA s).ambient.primitive := by
  obtain ⟨g, gM, hbase, hbaseM, hg, hgM, _hcovA, _hcovM, _hw, _hj,
    Q, eAs, eMs, eBs, R, RM, hR, hRM, hsquare, hsquareM, hsquareB, hpoint⟩ :=
      exists_pairDeformation_of_original_bundle_data hdimA hdimM PA PM PW PJ LA LM LP
  have hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
        PA.formInTrivialization g s x := fun s => (hpoint s).2.1
  have hc : ∀ s, HasNativeCoordinateExtensions (k := a)
      (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val) := by
    intro s
    obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := hpoint s
    exact hc
  refine ⟨g, hg, hbase, Q, eAs, hp, hc, ?_⟩
  intro c t ht
  let F := LA.localCompletionFamily c t ht
  refine ⟨?_, ?_⟩
  · exact F.ambientReferenceTotalMap_realGerms LA g hg hbase Q hdimA eAs hp hc
      eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  intro s hs
  exact F.ambientReferenceTotalMap_slice_primitive LA g hg hbase Q hdimA eAs hp hc s hs

end FsFltz.Geometry.IntrinsicSmoothBundle
