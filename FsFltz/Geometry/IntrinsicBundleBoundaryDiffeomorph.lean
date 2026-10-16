import FsFltz.Geometry.IntrinsicBundleBoundaryTransport

/-!
# Native boundary diffeomorphisms from compatible bundle charts

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. The actual boundary-valued joint germs imply smoothness on each
native fibre. Both directions and the bundle transition identities produce
actual boundary diffeomorphisms, including bijective full derivatives.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A target-valued joint germ implies native smoothness of its original
time slice for any source model with corners. -/
theorem HasSmoothTargetFamilyOn.contMDiff_slice {d r : ℕ} {H F : Type*}
    [TopologicalSpace H] [TopologicalSpace F]
    {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F] [IsManifold I ∞ F]
    (N : SmoothManifold r) {S : Set Parameter} {v : Parameter → F → N.Point}
    (hv : HasSmoothTargetFamilyOn I N S v) (t : Parameter) (ht : t ∈ S) :
    ContMDiff I 𝓘(ℝ, Model r) ∞ (v t) := by
  intro x
  let c := chartAt H x
  have hx : x ∈ c.source := mem_chart_source _ _
  obtain ⟨U, hpU, β, hβ, heq⟩ := hv c (chart_mem_atlas _ _) t ht x hx
  let p : F → ℝ × Model d := fun y => (t.val, c.extend I y)
  have hc : ContMDiffOn I 𝓘(ℝ, Model d) ∞ (c.extend I) c.source :=
    c.contMDiffOn_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ x))
  have hp : ContMDiffOn I 𝓘(ℝ, ℝ × Model d) ∞ p c.source :=
    contMDiff_const.contMDiffOn.prodMk_space hc
  let O : TopologicalSpace.Opens F :=
    ⟨c.source ∩ p ⁻¹' U, hp.continuousOn.isOpen_inter_preimage c.open_source U.isOpen⟩
  let Q : O → U := fun y => ⟨p y.val, y.property.2⟩
  have hQ : ContMDiff I 𝓘(ℝ, ℝ × Model d) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff U Q).mp
    intro y
    exact (hp.contMDiffAt (c.open_source.mem_nhds y.property.1)).comp
      y contMDiff_subtype_val.contMDiffAt
  have hfun : β ∘ Q = fun y : O => v t y.val :=
    funext (fun y => heq t ht y.val y.property.1 y.property.2)
  have hvs : ContMDiff I 𝓘(ℝ, Model r) ∞ (fun y : O => v t y.val) := by
    rw [← hfun]
    exact hβ.comp hQ
  exact (contMDiffAt_subtype_iff (f := v t) (x := (⟨x, ⟨hx, hpU⟩⟩ : O))).mp hvs.contMDiffAt

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- The actual induced native boundary diffeomorphism on each chart
overlap. Its smoothness follows from the constructed joint boundary germs. -/
def compatibleBoundaryTransitionDiffeomorph (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    Diffeomorph 𝓘(ℝ, Model k) 𝓘(ℝ, Model k)
      (IntrinsicBoundary.Point k M) (IntrinsicBoundary.Point k M) ∞ where
  toFun := boundaryFamilyOn (e.baseSet ∩ e'.baseSet) (e.coordChange e')
    (compatibleTransition_boundary e e' he he') t
  invFun := boundaryFamilyOn (e'.baseSet ∩ e.baseSet) (e'.coordChange e)
    (compatibleTransition_boundary e' e he' he) t
  left_inv x := by
    apply Subtype.ext
    rw [boundaryFamilyOn_val _ (show t ∈ e'.baseSet ∩ e.baseSet from ⟨ht.2, ht.1⟩),
      boundaryFamilyOn_val _ ht, e.coordChange_coordChange e' e ht.1 ht.2,
      e.coordChange_same ht.1]
    rfl
  right_inv x := by
    apply Subtype.ext
    rw [boundaryFamilyOn_val _ ht,
      boundaryFamilyOn_val _ (show t ∈ e'.baseSet ∩ e.baseSet from ⟨ht.2, ht.1⟩),
      e'.coordChange_coordChange e e' ht.2 ht.1, e'.coordChange_same ht.2]
    rfl
  contMDiff_toFun := (compatibleTransition_boundary_germs e e' he he').contMDiff_slice
    (IntrinsicBoundary.smoothManifold k M) t ht
  contMDiff_invFun := (compatibleTransition_boundary_germs e' e he' he).contMDiff_slice
    (IntrinsicBoundary.smoothManifold k M) t ⟨ht.2, ht.1⟩

/-- Boundary transport is the literal restriction of the original ambient
bundle transition, on every native boundary point. -/
@[simp]
theorem compatibleBoundaryTransitionDiffeomorph_val (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : IntrinsicBoundary.Point k M) :
    (compatibleBoundaryTransitionDiffeomorph e e' he he' ht x).val =
      e.coordChange e' t x.val :=
  boundaryFamilyOn_val _ ht x

/-- The actual boundary transition differential is bijective on the full
boundary tangent space; immersion preservation requires no certificate. -/
theorem compatibleBoundaryTransitionDiffeomorph_bijective_mfderiv
    (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) (x : IntrinsicBoundary.Point k M) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k)
      (compatibleBoundaryTransitionDiffeomorph e e' he he' ht) x) :=
  ((compatibleBoundaryTransitionDiffeomorph e e' he he' ht).isInvertible_mfderiv (by simp)).bijective

end FsFltz.Geometry.IntrinsicSmoothBundle
