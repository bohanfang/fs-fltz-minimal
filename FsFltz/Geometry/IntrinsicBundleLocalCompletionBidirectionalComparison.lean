import FsFltz.Geometry.IntrinsicBundleLocalCompletionInverseSmooth
import FsFltz.Geometry.IntrinsicBundleLocalCompletionOriginalZeroComparison

/-!
# One original bundle realization compares all local completions in both directions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814, 825–830.
Original positive-dimensional or zero-ribbon bundle data choose one compatible
global chart and one pair deformation before quantifying over all original
local charts. The actual forward and inverse comparisons have real open germs
over each retained local base, and their strict slices preserve the same
varying completed primitive. The parameter-retaining equivalence is the exact
native total diffeomorphism on that same local base. Completed families,
completion comparisons and
their regularity are conclusions. Descent of preselected sections and the
geometric target `thm:target` remain separate obligations.
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

section PositiveRibbon

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
All original local charts are then compared in both directions with that same
completed family.
This constructor treats positive-dimensional ribbons. -/
theorem exists_bidirectionalLocalCompletionComparisons_of_original_bundle_data
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
        HasRealOpenPatchInverseGerms F.native.patches
          Q.source.ambientCompletion.ambient.manifold F.base
          (fun z => (F.ambientReferenceTotalInverse LA g hg hbase Q hdimA eAs hp hc z).val) ∧
        (letI := F.native.totalCharts
         ∃ D : Diffeomorph (familyModel (a + 1)) (familyModel (2 * n))
           F.localSource (F.referenceTarget Q) ∞,
           D.toEquiv = F.ambientReferenceOpenEquiv LA g hg hbase Q hdimA eAs hp hc) ∧
        ∀ s (hs : s ∈ F.base),
          (F.sliceCompletion LA s).ambient.manifold.pullback Q.source.ambientCompletion.ambient.manifold
            (fun x => F.ambientReferenceTotalMap LA g hg hbase Q hdimA eAs hp hc
              ⟨sliceIn F.native.patches s x, by simpa only [LocalCompletionFamily.localSource,
                Set.mem_preimage, TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩)
            (Q.completedPrimitive s) = (F.sliceCompletion LA s).ambient.primitive ∧
          Q.source.ambientCompletion.ambient.manifold.pullback (F.sliceCompletion LA s).ambient.manifold
            (F.ambientSourceSliceEquiv LA g s Q eAs
              (F.ambientEndpointSliceComparison LA g hg hbase s hs Q hdimA eAs hp hc)).symm
            (F.sliceCompletion LA s).ambient.primitive = Q.completedPrimitive s := by
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
  have hf := F.ambientReferenceTotalMap_realGerms LA g hg hbase Q hdimA eAs hp hc
    eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  have hi := F.ambientReferenceTotalInverse_realGerms LA g hg hbase Q hdimA eAs hp hc
    eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  refine ⟨hf, hi, ?_, ?_⟩
  · let := F.native.totalCharts
    exact ⟨F.ambientReferenceTotalDiffeomorphOfRealGerms
      LA g hg hbase Q hdimA eAs hp hc hf hi, rfl⟩
  intro s hs
  exact ⟨F.ambientReferenceTotalMap_slice_primitive LA g hg hbase Q hdimA eAs hp hc s hs,
    F.ambientSourceSliceEquiv_inverse_primitive LA g s Q eAs
      (F.ambientEndpointSliceComparison LA g hg hbase s hs Q hdimA eAs hp hc)⟩

end PositiveRibbon

section ZeroRibbon

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace 2) A]
  {EM : Parameter → Type*} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]

/-- Choose the rank-one global realization from the original zero-ribbon
bundle once. Every original local ambient completion then compares with
that same completed pair family in both directions, including both interval
endpoints. -/
theorem exists_bidirectionalLocalCompletionComparisons_of_original_zero_bundle_data
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
        HasRealOpenPatchInverseGerms F.native.patches
          Q.source.ambientCompletion.ambient.manifold F.base
          (fun z => (F.ambientReferenceTotalInverse LA g hg hbase Q rfl eAs hp hc z).val) ∧
        (letI := F.native.totalCharts
         ∃ D : Diffeomorph (familyModel (2)) (familyModel 2)
           F.localSource (F.referenceTarget Q) ∞,
           D.toEquiv = F.ambientReferenceOpenEquiv LA g hg hbase Q rfl eAs hp hc) ∧
        ∀ s (hs : s ∈ F.base),
          (F.sliceCompletion LA s).ambient.manifold.pullback Q.source.ambientCompletion.ambient.manifold
            (fun x => F.ambientReferenceTotalMap LA g hg hbase Q rfl eAs hp hc
              ⟨sliceIn F.native.patches s x, by simpa only [LocalCompletionFamily.localSource,
                Set.mem_preimage, TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩)
            (Q.completedPrimitive s) = (F.sliceCompletion LA s).ambient.primitive ∧
          Q.source.ambientCompletion.ambient.manifold.pullback (F.sliceCompletion LA s).ambient.manifold
            (F.ambientSourceSliceEquiv LA g s Q eAs
              (F.ambientEndpointSliceComparison LA g hg hbase s hs Q rfl eAs hp hc)).symm
            (F.sliceCompletion LA s).ambient.primitive = Q.completedPrimitive s := by
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
  have hf := F.ambientReferenceTotalMap_realGerms LA g hg hbase Q rfl eAs hp hc
    eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  have hi := F.ambientReferenceTotalInverse_realGerms LA g hg hbase Q rfl eAs hp hc
    eBs (fun s => (hpoint s).1) hsquareB R hR hsquare
  refine ⟨hf, hi, ?_, ?_⟩
  · let := F.native.totalCharts
    exact ⟨F.ambientReferenceTotalDiffeomorphOfRealGerms
      LA g hg hbase Q rfl eAs hp hc hf hi, rfl⟩
  intro s hs
  exact ⟨F.ambientReferenceTotalMap_slice_primitive LA g hg hbase Q rfl eAs hp hc s hs,
    F.ambientSourceSliceEquiv_inverse_primitive LA g s Q eAs
      (F.ambientEndpointSliceComparison LA g hg hbase s hs Q rfl eAs hp hc)⟩

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
