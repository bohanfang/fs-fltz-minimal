import FsFltz.Geometry.IntrinsicBundleDataTransport
import FsFltz.Geometry.IntrinsicZeroNativeRibbonFamily

/-!
# Native family interfaces for transported bundle data

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. Coordinate germs produced by bundle transport give the existing
native map and scalar family predicates. They retain the original interval
values. No real-time global family is part of the input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- Target-valued joint germs on the actual boundaryless source manifold,
restricted to the original parameter set. -/
def HasSmoothManifoldTargetFamilyOn {d r : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold r) (S : Set Parameter) (v : Parameter → M.Point → N.Point) : Prop :=
  ∀ t ∈ S, ∀ x : M.Point,
    ∃ U : TopologicalSpace.Opens (ℝ × M.Point), (t.val, x) ∈ U ∧
      ∃ β : U → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model r) ∞ β ∧
        ∀ s ∈ S, ∀ y : M.Point, ∀ h : (s.val, y) ∈ U,
          β ⟨(s.val, y), h⟩ = v s y

/-- On a boundaryless native source the coordinate target germs become
actual native product germs by precomposition with its source chart. -/
theorem HasSmoothTargetFamilyOn.native_manifold {d r : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold r) {S : Set Parameter}
    {v : Parameter → M.Point → N.Point}
    (hv : HasSmoothTargetFamilyOn 𝓘(ℝ, Model d) N S v) :
    HasSmoothManifoldTargetFamilyOn M N S v := by
  intro t ht x
  let a := chartAt (Model d) x
  have hx : x ∈ a.source := mem_chart_source _ _
  obtain ⟨U, hpU, β, hβ, heq⟩ := hv a (chart_mem_atlas _ _) t ht x hx
  let p : ℝ × M.Point → ℝ × Model d := fun z => (z.1, a.extend 𝓘(ℝ, Model d) z.2)
  have ha : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (a.extend 𝓘(ℝ, Model d)) a.source :=
    a.contMDiffOn_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ x))
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ p (univ ×ˢ a.source) :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (ha.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  let O : TopologicalSpace.Opens (ℝ × M.Point) :=
    ⟨(univ ×ˢ a.source) ∩ p ⁻¹' U,
      hp.continuousOn.isOpen_inter_preimage (isOpen_univ.prod a.open_source) U.isOpen⟩
  let Q : O → U := fun z => ⟨p z.val, z.property.2⟩
  have hQ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ Q := by
    apply (ContMDiff.subtypeVal_comp_iff U Q).mp
    intro z
    exact (hp.contMDiffAt ((isOpen_univ.prod a.open_source).mem_nhds z.property.1)).comp
      z contMDiff_subtype_val.contMDiffAt
  exact ⟨O, ⟨⟨mem_univ _, hx⟩, hpU⟩, β ∘ Q, hβ.comp hQ,
    fun s hs y hy => heq s hs y hy.1.2 hy.2⟩

/-- Coordinate scalar germs on a boundaryless source are exactly the
native scalar germs required by the existing positive-witness constructor. -/
theorem HasSmoothValueFamilyOn.native_scalar {d : ℕ} (M : SmoothManifold d)
    {v : Parameter → M.Point → ℝ}
    (hv : HasSmoothValueFamilyOn 𝓘(ℝ, Model d) univ v) :
    M.IsLocallyExtendibleIntervalScalarFamily v := by
  intro t x
  let a := chartAt (Model d) x
  have hx : x ∈ a.source := mem_chart_source _ _
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hv a (chart_mem_atlas _ _) t (mem_univ _) x hx
  let p : ℝ × M.Point → ℝ × Model d := fun z => (z.1, a.extend 𝓘(ℝ, Model d) z.2)
  have ha : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (a.extend 𝓘(ℝ, Model d)) a.source :=
    a.contMDiffOn_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ x))
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, ℝ × Model d) ∞ p (univ ×ˢ a.source) :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (ha.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  exact ⟨(univ ×ˢ a.source) ∩ p ⁻¹' U, β ∘ p,
    hp.continuousOn.isOpen_inter_preimage (isOpen_univ.prod a.open_source) hU,
    ⟨⟨mem_univ _, hx⟩, hpU⟩,
    hβ.contMDiffOn.comp (hp.mono inter_subset_left) (fun _ hz => hz.2),
    fun s y hy => heq s (mem_univ _) y hy.1.2 hy.2⟩

/-- The positive-dimensional native ribbon-map interface is obtained
directly from the transported actual-target germs. -/
theorem HasSmoothTargetFamilyOn.native_map {k r : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] (N : SmoothManifold r)
    {v : Parameter → M → N.Point}
    (hv : HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N univ v) :
    IntrinsicLiouville.IsLocallyExtendibleMapFamily (k := k) N v := by
  intro a ha t x hx
  obtain ⟨U, hpU, β, hβ, heq⟩ := hv a ha t (mem_univ _) x hx
  exact ⟨U, hpU, β, hβ, fun s y hy hsy => heq s (mem_univ _) y hy hsy⟩

/-- The zero-dimensional ribbon interface uses the same actual germs on
the original native source, with no positive-dimensional boundary model. -/
theorem HasSmoothTargetFamilyOn.native_zero_map {r : ℕ} {M : Type}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
    (N : SmoothManifold r) {v : Parameter → M → N.Point}
    (hv : HasSmoothTargetFamilyOn 𝓘(ℝ, Model 0) N univ v) :
    IntrinsicZeroLiouville.IsLocallyExtendibleRibbonMapFamily N v := by
  have h := hv.native_manifold (IntrinsicZeroLiouville.sourceManifold M) N
  intro t x
  obtain ⟨U, hpU, β, hβ, heq⟩ := h t (mem_univ _) x
  exact ⟨U, hpU, β, hβ, fun s y hsy => heq s (mem_univ _) y hsy⟩

end FsFltz.Geometry.IntrinsicSmoothBundle
