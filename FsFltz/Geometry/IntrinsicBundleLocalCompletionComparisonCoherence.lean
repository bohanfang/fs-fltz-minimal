import FsFltz.Geometry.IntrinsicBundleLocalCompletionInverseSmooth
import FsFltz.Geometry.IntrinsicBundleLocalCompletionOverlapSmooth

/-!
# Coherence of original local completion comparisons

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
The strict comparisons from two original local completion charts to the
same retained endpoint agree after the actual original completed chart
transition. Primitive preservation and compact inclusion determine this
identity on the whole completion by flow uniqueness. The inverse identity
and the parameter-retaining total-space identities follow for those same
maps. No overlap equality is supplied as an input.

These are foundations for descending data already chosen on a completed
family. They do not choose an ambient Maslov section or prove `thm:target`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c d : OriginalCompactChart (k := k) (M := M) (E := E)} {t u : Parameter}

/-- Strict comparisons with the exact same retained endpoint agree on
the whole completed carrier after the original local chart transition.
The proof uses primitive preservation and the compact coordinate cocycle. -/
theorem EndpointSliceComparison.overlap_equiv
    (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    {e : ℕ} [NeZero e] (D : LiouvilleDomain e) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ e) M D.domain.Point ∞)
    (a : EndpointSliceComparison F L g s D C eM)
    (b : EndpointSliceComparison G L g s D C eM) :
    (F.overlapEquiv G L s hF hG).trans b.equiv = a.equiv := by
  refine F.sliceCompletion_equiv_unique L s C.ambient
    ((F.overlapEquiv G L s hF hG).trans b.equiv) a.equiv ?_ a.primitive ?_
  · change (F.sliceCompletion L s).ambient.manifold.pullback C.ambient.manifold
      (b.equiv ∘ F.overlapEquiv G L s hF hG) C.ambient.primitive = _
    rw [(F.sliceCompletion L s).ambient.manifold.pullback_comp
      (G.sliceCompletion L s).ambient.manifold C.ambient.manifold
      ((F.overlapEquiv G L s hF hG).mdifferentiable (by simp))
      (b.equiv.mdifferentiable (by simp)), b.primitive,
      F.overlapEquiv_primitive G L s hF hG]
  · intro x
    change b.equiv (F.overlapEquiv G L s hF hG (original (F.native.patches s) x)) = _
    rw [F.overlapEquiv_compact G L s hF hG, b.compact,
      c.val.coordChange_coordChange d.val g (F.base_subset hF) (G.base_subset hG), a.compact]

/-- Pointwise overlap coherence covers every completed point, without
restricting to a compact subset or to nonnegative end coordinates. -/
theorem EndpointSliceComparison.overlap_apply
    (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    {e : ℕ} [NeZero e] (D : LiouvilleDomain e) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ e) M D.domain.Point ∞)
    (a : EndpointSliceComparison F L g s D C eM)
    (b : EndpointSliceComparison G L g s D C eM)
    (x : (F.sliceCompletion L s).ambient.manifold.Point) :
    b.equiv (F.overlapEquiv G L s hF hG x) = a.equiv x :=
  congrArg (fun f : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv C.ambient.manifold => f x)
    (a.overlap_equiv F G L g s hF hG D C eM b)

/-- The original completed chart transition carries the inverse of the
first comparison to the inverse of the second, on the entire endpoint. -/
theorem EndpointSliceComparison.overlap_inverse
    (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    {e : ℕ} [NeZero e] (D : LiouvilleDomain e) (C : Completion D)
    (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ e) M D.domain.Point ∞)
    (a : EndpointSliceComparison F L g s D C eM)
    (b : EndpointSliceComparison G L g s D C eM) (y : C.ambient.manifold.Point) :
    F.overlapEquiv G L s hF hG (a.equiv.symm y) = b.equiv.symm y := by
  apply b.equiv.injective
  change b.equiv (F.overlapEquiv G L s hF hG (a.equiv.symm y)) = b.equiv (b.equiv.symm y)
  rw [a.overlap_apply F G L g s hF hG D C eM b, a.equiv.apply_symm_apply,
    b.equiv.apply_symm_apply]

variable {n : ℕ} [NeZero n]

/-- Passing to the fixed source presentation of the same deformation
preserves the whole-carrier overlap equation. -/
theorem ambientSourceSliceEquiv_overlap
    (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) (Q : PairDeformation n)
    (eAs : ∀ v, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair v).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s))
    (b : EndpointSliceComparison G L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s))
    (x : (F.sliceCompletion L s).ambient.manifold.Point) :
    G.ambientSourceSliceEquiv L g s Q eAs b (F.overlapEquiv G L s hF hG x) =
      F.ambientSourceSliceEquiv L g s Q eAs a x :=
  congrArg (Q.ambientCompletionPresentation s).equiv.symm
    (a.overlap_apply F G L g s hF hG (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s) b x)

/-- The source presentation's inverses satisfy the same original overlap
equation at every point of the reference completion. -/
theorem ambientSourceSliceEquiv_overlap_inverse
    (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (g : Trivialization M (π M E))
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) (Q : PairDeformation n)
    (eAs : ∀ v, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n))
      M (Q.pair v).ambientDomain.domain.Point ∞)
    (a : EndpointSliceComparison F L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s))
    (b : EndpointSliceComparison G L g s (Q.pair s).ambientDomain
      (Q.pair s).ambientCompletion (eAs s))
    (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    F.overlapEquiv G L s hF hG ((F.ambientSourceSliceEquiv L g s Q eAs a).symm y) =
      (G.ambientSourceSliceEquiv L g s Q eAs b).symm y :=
  a.overlap_inverse F G L g s hF hG (Q.pair s).ambientDomain
    (Q.pair s).ambientCompletion (eAs s) b ((Q.ambientCompletionPresentation s).equiv y)

variable (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
  (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- The actual forward local-to-reference maps agree on their whole
original total overlap. The transition is the independently constructed
original chart overlap, with its literal parameter and native quotient. -/
theorem ambientReferenceTotalMap_overlap (z : F.overlapSource G) :
    G.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      ⟨F.totalOverlap G L z, by
        change parameter G.native.patches (F.totalOverlap G L z) ∈ G.base
        rw [F.totalOverlap_parameter G L]
        exact z.property.2⟩ =
      F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc ⟨z.val, z.property.1⟩ := by
  let s := parameter F.native.patches z.val
  have hs : s ∈ F.base ∩ G.base := z.property
  obtain ⟨x, hx⟩ := (fiberEquiv F.native.patches s).surjective ⟨z.val, rfl⟩
  have hz : (⟨sliceIn F.native.patches s x,
      by simpa only [mem_overlapSource, parameter_sliceIn] using hs⟩ : F.overlapSource G) = z := by
    apply Subtype.ext
    exact congrArg (fun q : {z : F.native.total // parameter F.native.patches z = s} => q.val) hx
  rw [← hz]
  have htransition : (⟨F.totalOverlap G L
      ⟨sliceIn F.native.patches s x, by simpa only [mem_overlapSource, parameter_sliceIn] using hs⟩,
      by
        change parameter G.native.patches (F.totalOverlap G L _) ∈ G.base
        rw [F.totalOverlap_parameter G L, parameter_sliceIn]
        exact hs.2⟩ : G.localSource) =
      ⟨sliceIn G.native.patches s (F.overlapEquiv G L s hs.1 hs.2 x),
        by simpa only [localSource, Set.mem_preimage, TopologicalSpace.Opens.mem_mk,
          parameter_sliceIn] using hs.2⟩ := by
    apply Subtype.ext
    exact F.totalOverlap_sliceIn G L s hs x
  rw [htransition, G.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc,
    F.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc]
  exact F.ambientSourceSliceEquiv_overlap G L g s hs.1 hs.2 Q eAs
    (F.ambientEndpointSliceComparison L g hg hbase s hs.1 Q hdim eAs hp hc)
    (G.ambientEndpointSliceComparison L g hg hbase s hs.2 Q hdim eAs hp hc) x

/-- The independently constructed original total overlap carries the
first inverse reference map to the second at every common-base parameter
and every reference completed point. -/
theorem ambientReferenceTotalInverse_overlap (s : Parameter) (hs : s ∈ F.base ∩ G.base)
    (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    F.totalOverlap G L
      ⟨(F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (⟨s, hs.1⟩, y)).val,
        by
          change parameter F.native.patches
            (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (⟨s, hs.1⟩, y)).val ∈
              F.base ∩ G.base
          rw [F.ambientReferenceTotalInverse_parameter L g hg hbase Q hdim eAs hp hc]
          exact hs⟩ =
      (G.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (⟨s, hs.2⟩, y)).val := by
  change F.totalOverlap G L
    ⟨sliceIn F.native.patches s
      ((F.ambientSourceSliceEquiv L g s Q eAs
        (F.ambientEndpointSliceComparison L g hg hbase s hs.1 Q hdim eAs hp hc)).symm y), _⟩ =
    sliceIn G.native.patches s
      ((G.ambientSourceSliceEquiv L g s Q eAs
        (G.ambientEndpointSliceComparison L g hg hbase s hs.2 Q hdim eAs hp hc)).symm y)
  rw [F.totalOverlap_sliceIn G L s hs]
  exact congrArg (sliceIn G.native.patches s)
    (F.ambientSourceSliceEquiv_overlap_inverse G L g s hs.1 hs.2 Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs.1 Q hdim eAs hp hc)
      (G.ambientEndpointSliceComparison L g hg hbase s hs.2 Q hdim eAs hp hc) y)

/-- The complete parameter-retaining reference equivalence has literally
equal values after the actual total chart transition on the common base. -/
theorem ambientReferenceOpenEquiv_overlap (z : F.overlapSource G) :
    (G.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc
      ⟨F.totalOverlap G L z, by
        change parameter G.native.patches (F.totalOverlap G L z) ∈ G.base
        rw [F.totalOverlap_parameter G L]
        exact z.property.2⟩).val =
      (F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc
        ⟨z.val, z.property.1⟩).val := by
  apply Prod.ext
  · exact F.totalOverlap_parameter G L z
  · exact F.ambientReferenceTotalMap_overlap G L g hg hbase Q hdim eAs hp hc z

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
