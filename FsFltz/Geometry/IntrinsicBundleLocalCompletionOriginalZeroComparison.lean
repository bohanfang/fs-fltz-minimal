import FsFltz.Geometry.IntrinsicBundleZeroPairFamily
import FsFltz.Geometry.IntrinsicBundleLocalCompletionJointComparison

/-!
# One original zero-ribbon realization compares all local ambient completions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 127–160;
`def:chain`, lines 163–199; `def:maslov`, lines 225–232;
and `sec:lean`, lines 788–830.
Original bundle data with a zero-dimensional ribbon choose one compatible
global ambient chart and one rank-one pair deformation before quantifying
over any original local ambient chart. The actual forward total comparison
has real open germs and preserves the same varying completed primitive on
every retained slice. No completion map, completed family, or real extension
is supplied as input. Inverse joint regularity and descent of preselected
sections remain separate foundational bridges.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FsFltz.Geometry Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicSmoothBundle
open FsFltz.Geometry.IntrinsicSmoothBundle.OriginalBundleLiouvilleLaws
open FsFltz.Geometry.IntrinsicCompletionGluing
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]

/-- Choose the rank-one global realization from the original zero-ribbon
bundle once. Every original local ambient completion then compares with
that same completed pair family, including both interval endpoints. -/
theorem exists_localCompletionComparisons_of_original_zero_bundle_data
    (PA : BundlePrimitiveData (k := 1) (M := A) EA)
    (LA : OriginalBundleLiouvilleLaws PA)
    (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
    (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet →
      Function.Injective (PJ.map cM cA t))
    (PW : BundleWitnessData (k := 1) (M := A) EA)
    (μ : Parameter → (sourceManifold M).Form 1)
    : ∃ (g : Trivialization A (π A EA))
      (hg : CompatibleTrivialization (𝓡∂ 2) EA g)
      (hbase : g.baseSet = Set.univ) (Q : PairDeformation 1)
      (eAs : ∀ s, Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A
        (Q.pair s).ambientDomain.domain.Point ∞)
      (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
          PA.formInTrivialization g s x)
      (hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
        (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val)),
      ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
        (t : Parameter) (ht : t ∈ c.val.baseSet),
        let F := LA.localCompletionFamily c t ht
        (letI := F.native.totalCharts
         HasRealOpenMapGermsOn (familyModel 2)
           Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
           (F.ambientReferenceTotalMap LA g hg hbase Q rfl eAs hp hc)) ∧
        ∀ s (hs : s ∈ F.base),
          (F.sliceCompletion LA s).ambient.manifold.pullback Q.source.ambientCompletion.ambient.manifold
            (fun x => F.ambientReferenceTotalMap LA g hg hbase Q rfl eAs hp hc
              ⟨sliceIn F.native.patches s x, by simpa only [LocalCompletionFamily.localSource,
                Set.mem_preimage, TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩)
            (Q.completedPrimitive s) = (F.sliceCompletion LA s).ambient.primitive := by
  obtain ⟨gM, g, hbaseM, hbase, hgM, hg, _hcovA, _hj, _hw,
    Q, eAs, eFs, eBs, R, RM, hR, hRM, hsquare, hsquareM, hsquareB, hpoint⟩ :=
      exists_zero_pairDeformation_of_original_bundle_data PA LA PJ hPJ PW μ
  have hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eAs s y).val) x) =
        PA.formInTrivialization g s x := by
    intro s
    obtain ⟨_, _, _, _, hp, _, _, _⟩ := hpoint s
    exact hp
  have hc : ∀ s, HasNativeCoordinateExtensions (k := 1)
      (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val) := by
    intro s
    obtain ⟨_, _, _, _, _, _, _, hc⟩ := hpoint s
    exact hc
  refine ⟨g, hg, hbase, Q, eAs, hp, hc, ?_⟩
  intro c t ht
  let F := LA.localCompletionFamily c t ht
  refine ⟨?_, ?_⟩
  · exact F.ambientReferenceTotalMap_realGerms LA g hg hbase Q rfl eAs hp hc
      eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  intro s hs
  exact F.ambientReferenceTotalMap_slice_primitive LA g hg hbase Q rfl eAs hp hc s hs

end FsFltz.Geometry.IntrinsicSmoothBundle
