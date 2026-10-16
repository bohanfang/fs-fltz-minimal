import FsFltz.Geometry.IntrinsicBundleFormTransport
import FsFltz.Geometry.IntrinsicBundleTrivialization

/-!
# Original-atlas covariant primitive data and its trivialized family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The source primitives are given only in the
original bundle atlas and agree by actual native pullback on overlaps.
Forms and their joint germs in a constructed compatible trivialization
are conclusions. No primitive family in a global chart is an input.
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
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- Covariant vertical primitive data on the designated original atlas.
The transition equation is an equality of full native tangent forms. -/
structure BundlePrimitiveData (E : Parameter → Type*) [∀ t, TopologicalSpace (E t)]
    [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E] where
  form : {e : Trivialization M (π M E) // e ∈ trivializationAtlas M E} →
    Parameter → Form k M 1
  smooth : ∀ e, HasSmoothFormFamilyOn e.val.baseSet (form e)
  covariance : ∀ e e', ∀ t ∈ e.val.baseSet ∩ e'.val.baseSet,
    form e t = nativePullbackForm (e.val.coordChange e'.val t) (form e' t)

/-- Compatible transitions are actual native diffeomorphisms; the
smoothness in each direction follows from the original transition germs. -/
def transitionDiffeomorphOfCompatible (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞ where
  __ := (e.coordChangeHomeomorph e' ht.1 ht.2).toEquiv
  contMDiff_toFun := (he.hasSmoothTransition he').contMDiff ht
  contMDiff_invFun := (he'.hasSmoothTransition he).contMDiff ⟨ht.2, ht.1⟩

@[simp]
theorem transitionDiffeomorphOfCompatible_apply (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : M) :
    transitionDiffeomorphOfCompatible e e' he he' ht x = e.coordChange e' t x := rfl

/-- Full tangent maps of compatible transitions are bijective, including
at native boundary points. No tangent bijectivity certificate is input. -/
theorem bijective_mfderiv_coordChange_of_compatible
    (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : M) :
    Function.Bijective (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (e.coordChange e' t) x) :=
  ((transitionDiffeomorphOfCompatible e e' he he' ht).isInvertible_mfderiv (by simp)).bijective

namespace BundlePrimitiveData

/-- Express the source primitive in a chart using an original atlas chart
at each parameter. The formula is defined everywhere; its geometric and
smooth assertions use only parameters in the chosen chart's base. -/
def formInTrivialization (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) : Parameter → Form k M 1 := fun t =>
  nativePullbackForm (e.coordChange (trivializationAt M E t) t)
    (P.form ⟨trivializationAt M E t, trivialization_mem_atlas M E t⟩ t)

/-- The timewise chosen atlas chart can be replaced by any fixed original
chart on its overlap. This uses source covariance and the proved native
pullback chain rule, rather than an assumed global coherence equation. -/
theorem formInTrivialization_eq_pullback (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (c : Trivialization M (π M E)) (hc : c ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ c.baseSet) :
    P.formInTrivialization e t = nativePullbackForm (e.coordChange c t) (P.form ⟨c, hc⟩ t) := by
  let d := trivializationAt M E t
  have hd : d ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htd : t ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
  rw [P.covariance ⟨c, hc⟩ ⟨d, hd⟩ t ⟨ht.2, htd⟩,
    nativePullbackForm_comp _ ((he c hc).1.contMDiff ht)
      ((SmoothCompactBundle.smoothTransition c hc d hd).contMDiff ⟨ht.2, htd⟩)]
  have hmaps : (c.coordChange d t) ∘ (e.coordChange c t) = e.coordChange d t := by
    funext x
    exact e.coordChange_coordChange c d ht.1 ht.2 x
  rw [hmaps]
  rfl

/-- The descended form recovers every original local form exactly on its
base, with no choice of additional primitive in the constructed chart. -/
theorem formInTrivialization_eq_original (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : e ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet) :
    P.formInTrivialization e t = P.form ⟨e, he⟩ t := by
  rw [P.formInTrivialization_eq_pullback e (compatibleTrivialization_of_mem he) e he ⟨ht, ht⟩,
    e.coordChange_same ht, nativePullbackForm_id]

/-- Two compatible presentations carry the same source primitive by the
actual full native differential of their transition. -/
theorem formInTrivialization_covariance (P : BundlePrimitiveData (k := k) (M := M) E)
    (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    P.formInTrivialization e t =
      nativePullbackForm (e.coordChange e' t) (P.formInTrivialization e' t) := by
  let c := trivializationAt M E t
  have hc : c ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  change nativePullbackForm (e.coordChange c t) (P.form ⟨c, hc⟩ t) =
    nativePullbackForm (e.coordChange e' t)
      (nativePullbackForm (e'.coordChange c t) (P.form ⟨c, hc⟩ t))
  rw [nativePullbackForm_comp _ ((he.hasSmoothTransition he').contMDiff ht)
    ((he' c hc).1.contMDiff ⟨ht.2, htc⟩)]
  have hmaps : (e'.coordChange c t) ∘ (e.coordChange e' t) = e.coordChange c t := by
    funext x
    exact e.coordChange_coordChange e' c ht.1 ht.2 x
  rw [hmaps]

/-- All evaluations agree on the full native tangent fiber. -/
theorem formInTrivialization_apply (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (c : Trivialization M (π M E)) (hc : c ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ c.baseSet) (x : M)
    (vs : Fin 1 → TangentSpace (𝓡∂ (k + 1)) x) :
    P.formInTrivialization e t x vs = P.form ⟨c, hc⟩ t (e.coordChange c t x)
      (fun i => mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (e.coordChange c t) x (vs i)) := by
  rw [P.formInTrivialization_eq_pullback e he c hc ht]
  rfl

/-- Original local primitive germs transport into any compatible chart.
A fixed original chart is used near each parameter, so the timewise
choice in the definition contributes no unproved regularity. -/
theorem smooth_in_compatible_chart (P : BundlePrimitiveData (k := k) (M := M) E)
    (e : Trivialization M (π M E)) (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e) :
    HasSmoothFormFamilyOn e.baseSet (P.formInTrivialization e) := by
  apply HasSmoothFormFamilyOn.of_locally
  intro t ht
  let c := trivializationAt M E t
  have hc : c ∈ trivializationAtlas M E := trivialization_mem_atlas _ _ _
  have htc : t ∈ c.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨c.baseSet, c.open_baseSet, htc, ?_⟩
  exact ((P.smooth ⟨c, hc⟩).mono inter_subset_right |>.nativePullback
    (e.open_baseSet.inter c.open_baseSet) (he c hc).1.hasSmoothFamilyOn
    (continuousOn_coordChange e c)).congr
      (fun s hs => (P.formInTrivialization_eq_pullback e he c hc hs).symm)

/-- The constructed global chart and its joint primitive family are
conclusions from the bundle and original-atlas covariant data. -/
theorem exists_global_chart (P : BundlePrimitiveData (k := k) (M := M) E) :
    ∃ e : Trivialization M (π M E), e.baseSet = univ ∧
      CompatibleTrivialization (𝓡∂ (k + 1)) E e ∧
      IsLocallyExtendibleFormFamily (P.formInTrivialization e) := by
  obtain ⟨e, hbase, he⟩ :=
    exists_global_smooth_trivialization (I := 𝓡∂ (k + 1)) (F := M) (E := E)
  refine ⟨e, hbase, he, hasSmoothFormFamilyOn_univ_iff.mp ?_⟩
  simpa only [hbase] using P.smooth_in_compatible_chart e he

end BundlePrimitiveData
end FsFltz.Geometry.IntrinsicSmoothBundle
