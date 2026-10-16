import FsFltz.Geometry.IntrinsicNativeMapFamily
import FsFltz.Geometry.IntrinsicBoundaryWitnessFamily

/-!
# Transport of joint native pair germs through fixed smooth maps

Source: `geoemtric-part-fsf.tex`, `def:pair`, 132–146, `def:chain`,
163–169, and `sec:lean`, 788–814. A fixed smooth boundary presentation
postcomposes the actual target-valued ribbon germs and precomposes the
actual scalar witness germs. Every prescribed interval value is retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

/-- Precomposition by a fixed smooth map preserves genuine joint scalar
germs across the parameter endpoints. -/
theorem IsLocallyExtendibleIntervalScalarFamily.comp_contMDiff {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (b : Parameter → N.Point → ℝ) (hb : N.IsLocallyExtendibleIntervalScalarFamily b)
    (f : M.Point → N.Point) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f) :
    M.IsLocallyExtendibleIntervalScalarFamily (fun t x => b t (f x)) := by
  intro t x
  obtain ⟨U, g, hU, hpU, hg, heq⟩ := hb t (f x)
  let p : ℝ × M.Point → ℝ × N.Point := fun p => (p.1, f p.2)
  have hp : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) ∞ p :=
    contMDiff_fst.prodMk (hf.comp contMDiff_snd)
  refine ⟨p ⁻¹' U, g ∘ p, hU.preimage hp.continuous, hpU,
    hg.comp hp.contMDiffOn (fun _ h => h), ?_⟩
  intro s y hy
  exact heq s (f y) hy

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k d e : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- Postcomposition by a fixed smooth map preserves every actual native
joint map germ, without choosing any new source extension. -/
theorem IsLocallyExtendibleMapFamily.comp_contMDiff
    (N : SmoothManifold d) (P : SmoothManifold e)
    (j : Parameter → M → N.Point) (hj : IsLocallyExtendibleMapFamily (k := k) N j)
    (f : N.Point → P.Point) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f) :
    IsLocallyExtendibleMapFamily (k := k) P (fun t x => f (j t x)) := by
  intro c hc t x hx
  obtain ⟨U, hpU, g, hg, heq⟩ := hj c hc t x hx
  exact ⟨U, hpU, f ∘ g, hf.comp hg,
    fun s y hy h => congrArg f (heq s y hy h)⟩


/-- Actual joint source map germs imply native smoothness of every required
slice, including at the spatial boundary. -/
theorem IsLocallyExtendibleMapFamily.contMDiff_slice
    [IsManifold (𝓡∂ (k + 1)) ∞ M]
    (N : SmoothManifold d) (j : Parameter → M → N.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) N j) (t : Parameter) :
    ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ (j t) := by
  intro x
  let c := chartAt (EuclideanHalfSpace (k + 1)) x
  have hx : x ∈ c.source := mem_chart_source _ _
  obtain ⟨U, hpU, g, hg, heq⟩ := hj c (chart_mem_atlas _ x) t x hx
  let p : M → ℝ × Model (k + 1) := fun y => (t.val, c.extend (𝓡∂ (k + 1)) y)
  have hc : ContMDiffOn (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (c.extend (𝓡∂ (k + 1))) c.source :=
    c.contMDiffOn_extend (IsManifold.subset_maximalAtlas (chart_mem_atlas _ x))
  have hp : ContMDiffOn (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ p c.source :=
    contMDiff_const.contMDiffOn.prodMk_space hc
  let O : TopologicalSpace.Opens M := ⟨c.source ∩ p ⁻¹' U,
    hp.continuousOn.isOpen_inter_preimage c.open_source U.isOpen⟩
  let a : O → U := fun y => ⟨p y.val, y.property.2⟩
  have ha : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ a := by
    apply (ContMDiff.subtypeVal_comp_iff U a).mp
    intro y
    exact (hp.contMDiffAt (c.open_source.mem_nhds y.property.1)).comp
      y contMDiff_subtype_val.contMDiffAt
  have hfun : g ∘ a = (fun y : O => j t y.val) :=
    funext (fun y => heq t y.val y.property.1 y.property.2)
  have hjs : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ (fun y : O => j t y.val) := by
    rw [← hfun]
    exact hg.comp ha
  exact (contMDiffAt_subtype_iff (f := j t)
    (x := (⟨x, ⟨hx, hpU⟩⟩ : O))).mp hjs.contMDiffAt

end FsFltz.Geometry.IntrinsicLiouville
