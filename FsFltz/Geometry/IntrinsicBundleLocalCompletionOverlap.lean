import FsFltz.Geometry.IntrinsicBundleLocalCompletionFamily

/-!
# Canonical overlap maps of original-chart local completion families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
The canonical strict slice comparisons conjugate the original completed
chart transition to the retained local-family quotients. Compact uniqueness
fixes these maps independently of comparison choices. Their actual native
compact and signed-cylinder formulas are derived from the same primitives
and complete flows. Joint smoothness on the transported total overlap is a
separate foundation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c d : OriginalCompactChart (k := k) (M := M) (E := E)} {t u : Parameter}

/-- Native compact equality determines a strict map from the retained
local quotient on its entire completion. The end equation is a conclusion. -/
theorem sliceCompletion_equiv_unique (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter)
    {e : ℕ} (X : CompleteLiouvilleManifold e)
    (f g : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv X.manifold)
    (hf : (F.sliceCompletion L s).ambient.manifold.pullback X.manifold f X.primitive =
      (F.sliceCompletion L s).ambient.primitive)
    (hg : (F.sliceCompletion L s).ambient.manifold.pullback X.manifold g X.primitive =
      (F.sliceCompletion L s).ambient.primitive)
    (hc : ∀ x, f (original (F.native.patches s) x) = g (original (F.native.patches s) x)) :
    f = g := by
  apply (F.sliceCompletion L s).equiv_eq_of_scaled_primitive_on_compact X f g 1 1
  · simpa only [one_smul] using hf
  · simpa only [one_smul] using hg
  · intro z hz
    change z ∈ (compactDomain F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).carrier at hz
    rw [compactDomain_carrier] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hc x

/-- Canonical slice comparisons do not depend on their extension choices. -/
theorem SliceComparison.equiv_unique (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s v : Parameter) (hv : v ∈ c.val.baseSet)
    (a b : SliceComparison F L s v hv) : a.equiv = b.equiv :=
  F.sliceCompletion_equiv_unique L s (L.chartCompletion c v hv).ambient a.equiv b.equiv
    a.primitive b.primitive (fun x => (a.compact x).trans (b.compact x).symm)

/-- The canonical local overlap retains the actual original chart transition. -/
def overlapEquiv (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter)
    (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (F.sliceCompletion L s).ambient.manifold.SmoothEquiv
      (G.sliceCompletion L s).ambient.manifold :=
  ((F.baseSliceComparison L s hF).equiv.trans
    (L.completedChartTransition c d s ⟨F.base_subset hF, G.base_subset hG⟩).equiv).trans
      (G.baseSliceComparison L s hG).equiv.symm

/-- Pullback functoriality makes the actual conjugated overlap strict. -/
theorem overlapEquiv_primitive (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (F.sliceCompletion L s).ambient.manifold.pullback (G.sliceCompletion L s).ambient.manifold
      (F.overlapEquiv G L s hF hG) (G.sliceCompletion L s).ambient.primitive =
        (F.sliceCompletion L s).ambient.primitive := by
  let a := F.baseSliceComparison L s hF
  let b := G.baseSliceComparison L s hG
  let h := L.completedChartTransition c d s ⟨F.base_subset hF, G.base_subset hG⟩
  have hb : (L.chartCompletion d s (G.base_subset hG)).ambient.manifold.pullback
      (G.sliceCompletion L s).ambient.manifold b.equiv.symm
      (G.sliceCompletion L s).ambient.primitive =
        (L.chartCompletion d s (G.base_subset hG)).ambient.primitive := by
    rw [← b.primitive]
    exact (G.sliceCompletion L s).ambient.manifold.pullback_symm_pullback
      (L.chartCompletion d s (G.base_subset hG)).ambient.manifold b.equiv _
  change (F.sliceCompletion L s).ambient.manifold.pullback (G.sliceCompletion L s).ambient.manifold
    ((b.equiv.symm ∘ h.equiv) ∘ a.equiv) _ = _
  rw [(F.sliceCompletion L s).ambient.manifold.pullback_comp
    (L.chartCompletion c s (F.base_subset hF)).ambient.manifold (G.sliceCompletion L s).ambient.manifold
    (a.equiv.mdifferentiable (by simp))
    ((b.equiv.symm.mdifferentiable (by simp)).comp (h.equiv.mdifferentiable (by simp)))]
  rw [(L.chartCompletion c s (F.base_subset hF)).ambient.manifold.pullback_comp
    (L.chartCompletion d s (G.base_subset hG)).ambient.manifold (G.sliceCompletion L s).ambient.manifold
    (h.equiv.mdifferentiable (by simp)) (b.equiv.symm.mdifferentiable (by simp)),
    hb, h.primitive, a.primitive]

/-- On every original native point, the overlap is the actual compact
bundle coordinate change. -/
theorem overlapEquiv_compact (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) (x : M) :
    F.overlapEquiv G L s hF hG (original (F.native.patches s) x) =
      original (G.native.patches s) (c.val.coordChange d.val s x) := by
  change (G.baseSliceComparison L s hG).equiv.symm
    ((L.completedChartTransition c d s ⟨F.base_subset hF, G.base_subset hG⟩).equiv
      ((F.baseSliceComparison L s hF).equiv (original (F.native.patches s) x))) = _
  rw [(F.baseSliceComparison L s hF).compact,
    (L.completedChartTransition c d s ⟨F.base_subset hF, G.base_subset hG⟩).compact,
    (G.baseSliceComparison L s hG).compact_inverse]

/-- Any strict map with the actual original compact coordinate formula is
the canonical local overlap; no end compatibility is an extra input. -/
theorem overlapEquiv_unique (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    (f : (F.sliceCompletion L s).ambient.manifold.SmoothEquiv (G.sliceCompletion L s).ambient.manifold)
    (hp : (F.sliceCompletion L s).ambient.manifold.pullback (G.sliceCompletion L s).ambient.manifold
      f (G.sliceCompletion L s).ambient.primitive = (F.sliceCompletion L s).ambient.primitive)
    (hc : ∀ x, f (original (F.native.patches s) x) =
      original (G.native.patches s) (c.val.coordChange d.val s x)) :
    f = F.overlapEquiv G L s hF hG :=
  F.sliceCompletion_equiv_unique L s (G.sliceCompletion L s).ambient f _ hp
    (F.overlapEquiv_primitive G L s hF hG)
    (fun x => (hc x).trans (F.overlapEquiv_compact G L s hF hG x).symm)

/-- Reversing the original compact transition reverses the whole strict
completed overlap. The inverse equation is determined on the compact part. -/
theorem overlapEquiv_symm (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (F.overlapEquiv G L s hF hG).symm = G.overlapEquiv F L s hG hF := by
  apply G.overlapEquiv_unique F L s hG hF
  · rw [← F.overlapEquiv_primitive G L s hF hG]
    exact (F.sliceCompletion L s).ambient.manifold.pullback_symm_pullback
      (G.sliceCompletion L s).ambient.manifold (F.overlapEquiv G L s hF hG) _
  · intro x
    apply (F.overlapEquiv G L s hF hG).injective
    change (F.overlapEquiv G L s hF hG)
      ((F.overlapEquiv G L s hF hG).symm (original (G.native.patches s) x)) =
      (F.overlapEquiv G L s hF hG) (original (F.native.patches s) (d.val.coordChange c.val s x))
    rw [(F.overlapEquiv G L s hF hG).apply_symm_apply,
      F.overlapEquiv_compact G L s hF hG,
      d.val.coordChange_coordChange c.val d.val (G.base_subset hG) (F.base_subset hF),
      d.val.coordChange_same (G.base_subset hG)]
    rfl

/-- Strictness transports the very same completed flow for every real time. -/
theorem overlapEquiv_flow (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    (x : (F.sliceCompletion L s).ambient.manifold.Point) (r : ℝ) :
    F.overlapEquiv G L s hF hG ((F.sliceCompletion L s).ambient.completeFlow.flow r x) =
      (G.sliceCompletion L s).ambient.completeFlow.flow r (F.overlapEquiv G L s hF hG x) :=
  (F.sliceCompletion L s).ambient.map_flow (G.sliceCompletion L s).ambient
    (F.overlapEquiv G L s hF hG) (F.overlapEquiv_primitive G L s hF hG) x r

/-- The overlap boundary map is the actual restriction of the original
compact bundle coordinate change to its native boundary. -/
def overlapBoundary (F : LocalCompletionFamily P c t) (G : LocalCompletionFamily P d u)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base) :
    (IntrinsicBoundary.smoothManifold k M).SmoothEquiv (IntrinsicBoundary.smoothManifold k M) :=
  compatibleBoundaryTransitionDiffeomorph c.val d.val
    (compatibleTrivialization_of_mem c.property) (compatibleTrivialization_of_mem d.property)
    ⟨F.base_subset hF, G.base_subset hG⟩

@[simp]
theorem overlapBoundary_val (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (s : Parameter)
    (hF : s ∈ F.base) (hG : s ∈ G.base) (b : IntrinsicBoundary.Point k M) :
    (F.overlapBoundary G s hF hG b).val = c.val.coordChange d.val s b.val :=
  compatibleBoundaryTransitionDiffeomorph_val c.val d.val
    (compatibleTrivialization_of_mem c.property) (compatibleTrivialization_of_mem d.property)
    ⟨F.base_subset hF, G.base_subset hG⟩ b

/-- The actual completion's zero orbit retains every native boundary point. -/
theorem sliceCompletion_end_zero (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter) (b : IntrinsicBoundary.Point k M) :
    (F.sliceCompletion L s).endMap (b, 0) = original (F.native.patches s) b.val := by
  rw [(F.sliceCompletion L s).endMap_zero]
  exact compactDomain_boundaryInclusion F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
    (F.native.inverse s) (F.native.zero s) b

/-- Every real-radius boundary orbit has the same native boundary
coordinate change. This is forced by compact agreement and flow transport. -/
theorem overlapEquiv_end (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) :
    F.overlapEquiv G L s hF hG ((F.sliceCompletion L s).endMap (b, r)) =
      (G.sliceCompletion L s).endMap (F.overlapBoundary G s hF hG b, r) := by
  rw [(F.sliceCompletion L s).end_flow, (G.sliceCompletion L s).end_flow,
    F.overlapEquiv_flow G L s hF hG]
  congr 1
  change F.overlapEquiv G L s hF hG
    ((compactDomain F.native.width_pos (F.native.collar s)
      (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
      (F.native.inverse s) (F.native.zero s)).boundaryInclusion.map b) =
    (compactDomain G.native.width_pos (G.native.collar s)
      (G.native.embedding s) (G.native.smooth s) (G.native.boundary s)
      (G.native.inverse s) (G.native.zero s)).boundaryInclusion.map
        (F.overlapBoundary G s hF hG b)
  rw [compactDomain_boundaryInclusion, compactDomain_boundaryInclusion,
    F.overlapEquiv_compact G L s hF hG, overlapBoundary_val]

/-- On its whole attached cylinder, the retained completion orbit is the
actual signed cylinder insertion. This includes all outward radii. -/
theorem sliceCompletion_end_cylinder (F : LocalCompletionFamily P c t)
    (L : OriginalBundleLiouvilleLaws P) (s : Parameter)
    (b : IntrinsicBoundary.Point k M) (r : ℝ) (hr : r < F.native.width) :
    (F.sliceCompletion L s).endMap (b, -r) =
      cylinder (F.native.patches s) ⟨(r, b), hr, mem_univ _⟩ := by
  have hrad : -F.native.width < -r := neg_lt_neg hr
  have h := boundaryOrbitMap_eq_outwardEndMap F.native.width_pos (F.native.collar s)
    (F.native.embedding s) (F.native.smooth s) (F.native.boundary s)
    (F.native.inverse s) (F.native.zero s) (P.form c (F.reparam s))
    (F.source_smooth.slice s) (F.sliceLiouville L s) (F.native.nondegenerate s)
    (F.native.primitive_cylinder s) (F.sliceCompletion L s).ambient.completeFlow (b, -r) hrad
  exact h.trans (by simpa only [neg_neg] using
    outwardEndMap_eq_cylinder F.native.width_pos (F.native.collar s) (b, -r) hrad)

/-- On the common inward strip and every outward radius, the canonical
overlap is the literal signed-cylinder map induced by the original native
boundary transition. The two original collar widths are retained. -/
theorem overlapEquiv_cylinder (F : LocalCompletionFamily P c t)
    (G : LocalCompletionFamily P d u) (L : OriginalBundleLiouvilleLaws P)
    (s : Parameter) (hF : s ∈ F.base) (hG : s ∈ G.base)
    (b : IntrinsicBoundary.Point k M) (r : ℝ)
    (hrF : r < F.native.width) (hrG : r < G.native.width) :
    F.overlapEquiv G L s hF hG (cylinder (F.native.patches s) ⟨(r, b), hrF, mem_univ _⟩) =
      cylinder (G.native.patches s)
        ⟨(r, F.overlapBoundary G s hF hG b), hrG, mem_univ _⟩ := by
  rw [← F.sliceCompletion_end_cylinder L s b r hrF,
    F.overlapEquiv_end G L s hF hG,
    G.sliceCompletion_end_cylinder L s _ r hrG]

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
