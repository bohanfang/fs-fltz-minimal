import FsFltz.Geometry.IntrinsicBundleLocalCompletionGlobalComparison
import FsFltz.Geometry.IntrinsicBundleLocalCompletionMapGerms
import FsFltz.Geometry.IntrinsicCompletionFamilyMapGerms

/-!
# Joint real germs of the original local-to-global completed comparison

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
The actual local completion quotient is compared fiberwise with the
specified completed pair deformation. The map is defined only over its
original relative open base. Its original compact and signed-cylinder
formulas give target-valued real germs in the retained total atlas.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A real boundary germ composes with a real end map at the same signed
radius. Only the original interval values on the specified strip are used. -/
theorem exists_realBandGerm_of_boundaryFamily {k r : ℕ}
    (B : SmoothManifold k) (N : SmoothManifold r) {δ : ℝ}
    (S : Set Parameter) (v : Parameter → B.Point → B.Point)
    (hv : HasSmoothManifoldTargetFamilyOn B B S v)
    (β : ℝ × (B.Point × ℝ) → N.Point)
    (hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model r) ∞ β)
    (a : ℝ) (w : Parameter → Band δ B.Point → N.Point)
    (hw : ∀ s ∈ S, ∀ p : Band δ B.Point, a < -p.val.1 →
      w s p = β (s.val, (v s p.val.2, -p.val.1))) :
    letI := bandChartedSpace (k := k) (B := B.Point) δ
    ∀ t ∈ S, ∀ p : Band δ B.Point, a < -p.val.1 →
      ∃ U : TopologicalSpace.Opens (ℝ × Band δ B.Point), (t.val, p) ∈ U ∧
        ∃ γ : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, Model r) ∞ γ ∧
          ∀ s ∈ S, ∀ q : Band δ B.Point, a < -q.val.1 →
            ∀ h : (s.val, q) ∈ U, γ ⟨(s.val, q), h⟩ = w s q := by
  let := bandChartedSpace (k := k) (B := B.Point) δ
  intro t ht p hp
  obtain ⟨V, hpV, η, hη, heq⟩ := hv t ht p.val.2
  let q : ℝ × Band δ B.Point → ℝ × B.Point := fun z => (z.1, z.2.val.2)
  have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ q :=
    contMDiff_fst.prodMk (contMDiff_snd.comp ((contMDiff_band_val δ).comp contMDiff_snd))
  let U : TopologicalSpace.Opens (ℝ × Band δ B.Point) :=
    ⟨q ⁻¹' V, V.isOpen.preimage hq.continuous⟩
  let Q : U → V := fun z => ⟨q z.val, z.property⟩
  have hQ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff V Q).mp
    exact hq.comp contMDiff_subtype_val
  let input : U → ℝ × (B.Point × ℝ) := fun z => (z.val.1, (η (Q z), -z.val.2.val.1))
  have hinput : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞ input :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      ((hη.comp hQ).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val δ).comp
          (contMDiff_snd.comp contMDiff_subtype_val))).neg)
  refine ⟨U, hpV, β ∘ input, hβ.comp hinput, ?_⟩
  intro s hs q' hq' h
  change β (s.val, (η ⟨(s.val, q'.val.2), h⟩, -q'.val.1)) = w s q'
  rw [heq s hs q'.val.2 h, hw s hs q' hq']

end FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

/-- The unchanged original total quotient over its retained relative base. -/
abbrev localSource (F : LocalCompletionFamily P c t) : TopologicalSpace.Opens F.native.total :=
  ⟨parameter F.native.patches ⁻¹' F.base,
    F.base_open.preimage (continuous_parameter F.native.patches)⟩

variable (F : LocalCompletionFamily P c t) (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- The actual original local-to-global map, with the unique native
slice recovered from its total quotient. No off-base value is selected. -/
def ambientReferenceTotalMap : F.localSource → Q.source.ambientCompletion.ambient.manifold.Point :=
  fun z =>
    F.ambientSourceSliceEquiv L g (parameter F.native.patches z.val) Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase (parameter F.native.patches z.val)
        z.property Q hdim eAs hp hc)
      ((fiberEquiv F.native.patches (parameter F.native.patches z.val)).symm ⟨z.val, rfl⟩)

/-- Restriction to an original slice is exactly its primitive-preserving
comparison with the same fixed source completion. -/
theorem ambientReferenceTotalMap_slice (s : Parameter) (hs : s ∈ F.base)
    (x : Space (F.native.patches s)) :
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      ⟨sliceIn F.native.patches s x, by simpa only [localSource, Set.mem_preimage,
        TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩ =
      F.ambientSourceSliceEquiv L g s Q eAs
        (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) x := by
  have hx : (fiberEquiv F.native.patches s).symm
      ⟨sliceIn F.native.patches s x, parameter_sliceIn _ _ _⟩ = x :=
    (fiberEquiv F.native.patches s).symm_apply_apply x
  rcases jointly_surjective (F.native.patches s) x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · simp only [sliceIn_original] at hx ⊢
    simp only [ambientReferenceTotalMap, parameter_original, hx]
  · simp only [sliceIn_cylinder] at hx ⊢
    simp only [ambientReferenceTotalMap, parameter_totalCylinder, hx]

/-- The compact formula uses the actual original ordered chart change. -/
theorem ambientReferenceTotalMap_compact (s : Parameter) (hs : s ∈ F.base) (x : M) :
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      ⟨original (totalCollar F.native.patches) (s, x), hs⟩ =
      Q.ambientNativeReferenceMap eAs s (c.val.coordChange g s x) := by
  simpa only [sliceIn_original, PairDeformation.ambientNativeReferenceMap] using
    (F.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc s hs
      (original (F.native.patches s) x)).trans
        (F.ambientSourceSliceEquiv_compact L g s Q eAs
          (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) x)

/-- The boundary of the actual original ordered compact chart transition. -/
abbrev referenceBoundaryTransition (_F : LocalCompletionFamily P c t) :=
  boundaryFamilyOn (c.val.baseSet ∩ g.baseSet) (c.val.coordChange g)
    (compatibleTransition_boundary c.val g (compatibleTrivialization_of_mem c.property) hg)

include hbase in
theorem base_subset_globalOverlap (s : Parameter) (hs : s ∈ F.base) :
    s ∈ c.val.baseSet ∩ g.baseSet :=
  ⟨F.base_subset hs, by rw [hbase]; exact mem_univ s⟩

/-- On every signed cylinder point, the comparison uses the same
reference boundary marking and the literal negated inward radius. -/
theorem ambientReferenceTotalMap_cylinder
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (s : Parameter) (hs : s ∈ F.base) (p : Band F.native.width (IntrinsicBoundary.Point k M)) :
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      ⟨totalCylinder F.native.patches (s, p), hs⟩ =
      (Q.ambientCompletionPresentation s).prescribedEndMap
        (eBs parameterZero (F.referenceBoundaryTransition g hg s p.val.2), -p.val.1) := by
  have htrans : compatibleBoundaryTransitionDiffeomorph c.val g
      (compatibleTrivialization_of_mem c.property) hg
      (F.base_subset_globalOverlap g hbase s hs) p.val.2 =
        F.referenceBoundaryTransition g hg s p.val.2 := by
    apply Subtype.ext
    rw [compatibleBoundaryTransitionDiffeomorph_val]
    exact (boundaryFamilyOn_val
      (compatibleTransition_boundary c.val g (compatibleTrivialization_of_mem c.property) hg)
      (F.base_subset_globalOverlap g hbase s hs) p.val.2).symm
  have h := (F.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc s hs
      (cylinder (F.native.patches s) p)).trans
    (F.ambientSourceSliceEquiv_cylinder_native L g hg hbase s hs Q eAs eBs hb
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc)
      p.val.2 p.val.1 p.property.1)
  rw [htrans, ← hsquareB s (F.referenceBoundaryTransition g hg s p.val.2),
    (Q.ambientPresentation s).boundaryEquiv.symm_apply_apply] at h
  simpa only [sliceIn_cylinder] using h

/-- Genuine real-open endpoint germs for the exact original
local-to-global total comparison. The compact realization and markings are
the retained data of the same `Q`; its completed primitive constructs the
real end strip. No real extension of the comparison is supplied as input. -/
theorem ambientReferenceTotalMap_realGerms
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val) :
    letI := F.native.totalCharts
    HasRealOpenMapGermsOn (familyModel (k + 1))
      Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
      (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) F.native.width
  let := F.native.totalCharts
  let vi : Parameter → IntrinsicInterior.Point k M →
      Q.source.ambientCompletion.ambient.manifold.Point :=
    fun s x => Q.ambientNativeReferenceMap eAs s (c.val.coordChange g s x.val)
  have hi : HasSmoothManifoldTargetFamilyOn (IntrinsicInterior.smoothManifold k M)
      Q.source.ambientCompletion.ambient.manifold F.base vi := by
    have h := compatibleTransition_referenceInterior_germs c.val g
      (compatibleTrivialization_of_mem c.property) hg Q eAs R hR hsquareA
    intro s hs x
    obtain ⟨U, hpU, β, hβ, heq⟩ := h s (F.base_subset_globalOverlap g hbase s hs) x
    exact ⟨U, hpU, β, hβ, fun u hu y hy =>
      heq u (F.base_subset_globalOverlap g hbase u hu) y hy⟩
  let v := F.referenceBoundaryTransition g hg
  have hv : HasSmoothManifoldTargetFamilyOn (IntrinsicBoundary.smoothManifold k M)
      (IntrinsicBoundary.smoothManifold k M) F.base v := by
    have h := (compatibleTransition_boundary_germs c.val g
      (compatibleTrivialization_of_mem c.property) hg).native_manifold
        (IntrinsicBoundary.smoothManifold k M) (IntrinsicBoundary.smoothManifold k M)
    intro s hs x
    obtain ⟨U, hpU, β, hβ, heq⟩ := h s (F.base_subset_globalOverlap g hbase s hs) x
    exact ⟨U, hpU, β, hβ, fun u hu y hy =>
      heq u (F.base_subset_globalOverlap g hbase u hu) y hy⟩
  obtain ⟨a, ha, γ, hγ, heγ⟩ :=
    Q.source.ambientCompletion.exists_prescribedFamily_end_strip_extension
      (fun s => (Q.pair s).ambientDomain) (fun s => (Q.pair s).ambientCompletion)
      Q.ambientPresentation Q.ambientCompletionPresentation Q.completedAmbientPrimitive_smooth
  let β : ℝ × (IntrinsicBoundary.Point k M × ℝ) →
      Q.source.ambientCompletion.ambient.manifold.Point :=
    fun p => γ p.1 (eBs parameterZero p.2.1, p.2.2)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model (2 * n)) ∞ β :=
    hγ.comp (contMDiff_fst.prodMk
      (((eBs parameterZero).contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd)))
  let vc : Parameter → Band F.native.width (IntrinsicBoundary.Point k M) →
      Q.source.ambientCompletion.ambient.manifold.Point :=
    fun s p => (Q.ambientCompletionPresentation s).prescribedEndMap
      (eBs parameterZero (v s p.val.2), -p.val.1)
  have hcyl := exists_realBandGerm_of_boundaryFamily
    (IntrinsicBoundary.smoothManifold k M) Q.source.ambientCompletion.ambient.manifold
    F.base v hv β hβ a vc (by
      intro s hs p hp
      exact (heγ s (eBs parameterZero (v s p.val.2)) (-p.val.1) hp).symm)
  exact hasRealOpenMapGermsOn_totalFamily_of_patches
    Q.source.ambientCompletion.ambient.manifold F.native.width_pos F.native.collar
    F.native.boundary F.native.zero F.native.joint a ha F.base
    (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc) vi vc
    (fun s hs x => F.ambientReferenceTotalMap_compact L g hg hbase Q hdim eAs hp hc s hs x.val)
    (fun s hs p => F.ambientReferenceTotalMap_cylinder L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB s hs p) hi hcyl

/-- The restriction of this exact total map pulls the same varying
completed primitive back to the original local completion primitive. -/
theorem ambientReferenceTotalMap_slice_primitive (s : Parameter) (hs : s ∈ F.base) :
    (F.sliceCompletion L s).ambient.manifold.pullback
      Q.source.ambientCompletion.ambient.manifold
      (fun x => F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
        ⟨sliceIn F.native.patches s x, by simpa only [localSource, Set.mem_preimage,
          TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩)
      (Q.completedPrimitive s) = (F.sliceCompletion L s).ambient.primitive := by
  have he : (fun x => F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc
      ⟨sliceIn F.native.patches s x, by simpa only [localSource, Set.mem_preimage,
        TopologicalSpace.Opens.mem_mk, parameter_sliceIn] using hs⟩) =
      F.ambientSourceSliceEquiv L g s Q eAs
        (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc) :=
    funext (F.ambientReferenceTotalMap_slice L g hg hbase Q hdim eAs hp hc s hs)
  exact (congrArg (fun f : (F.sliceCompletion L s).ambient.manifold.Point →
      Q.source.ambientCompletion.ambient.manifold.Point =>
        (F.sliceCompletion L s).ambient.manifold.pullback
          Q.source.ambientCompletion.ambient.manifold f (Q.completedPrimitive s)) he).trans
    (F.ambientSourceSliceEquiv_primitive L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc))

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
