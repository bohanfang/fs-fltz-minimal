import FsFltz.Geometry.IntrinsicMapExtension

/-!
# Smooth target postcomposition of native map extension germs

Source: `geoemtric-part-fsf.tex`, the across-boundary smoothness conventions
and `def:pair`, lines 119–160, and `sec:lean`, lines 783–814. Native source
map germs remain actual open smooth extension germs under a smooth change of
boundaryless target. This applies in particular to a boundary diffeomorphism
derived from the same native ambient presentation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {d e : ℕ} (N : SmoothManifold d) (P : SmoothManifold e)

/-- Postcomposing with a smooth boundaryless target map preserves the original
native source's actual local open smooth extension germs. -/
theorem IsLocallyExtendibleMap.comp_contMDiff {f : M → N.Point}
    (hf : IsLocallyExtendibleMap (k := k) (F := Model d) f)
    (g : N.Point → P.Point)
    (hg : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ g) :
    IsLocallyExtendibleMap (k := k) (F := Model e) (g ∘ f) := by
  refine ⟨hg.continuous.comp hf.1, ?_⟩
  intro c hc x hx
  obtain ⟨β, U, hU, hxU, hβ, heq⟩ := hf.2 c hc x hx
  let a := chartAt (Model d) (f x)
  let b := chartAt (Model e) (g (f x))
  let q : Model d → Model e := b ∘ g ∘ a.symm
  let V : Set (Model d) := a.target ∩ (g ∘ a.symm) ⁻¹' b.source
  have hgaCont : ContinuousOn (g ∘ a.symm) a.target :=
    hg.continuous.comp_continuousOn a.symm.continuousOn
  have hV : IsOpen V :=
    hgaCont.isOpen_inter_preimage a.open_target b.open_source
  have hq : ContDiffOn ℝ ∞ q V := by
    have ha := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d))
      (x := f x) (n := ∞)).mono (inter_subset_left : V ⊆ a.target)
    have hga := hg.comp_contMDiffOn ha
    have hb := contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := g (f x)) (n := ∞)
    exact (hb.comp hga (fun z hz => hz.2)).contDiffOn
  have hzt : c.extend (𝓡∂ (k + 1)) x ∈ (c.extend (𝓡∂ (k + 1))).target :=
    (c.extend (𝓡∂ (k + 1))).map_source (by simpa only [c.extend_source] using hx)
  have hβx : β (c.extend (𝓡∂ (k + 1)) x) = a (f x) := by
    have h := heq.eq_of_nhdsWithin hzt
    rw [(c.extend (𝓡∂ (k + 1))).left_inv (by simpa only [c.extend_source] using hx)] at h
    exact h
  have hβV : β (c.extend (𝓡∂ (k + 1)) x) ∈ V := by
    rw [hβx]
    refine ⟨a.map_source (mem_chart_source _ _), ?_⟩
    change g (a.symm (a (f x))) ∈ b.source
    rw [a.left_inv (mem_chart_source _ _)]
    exact mem_chart_source _ _
  let U' := U ∩ β ⁻¹' V
  refine ⟨q ∘ β, U', hβ.continuousOn.isOpen_inter_preimage hU hV,
    ⟨hxU, hβV⟩, hq.comp (hβ.mono inter_subset_left) (fun z hz => hz.2), ?_⟩
  have ht : Tendsto (c.extend (𝓡∂ (k + 1))).symm
      (𝓝[(c.extend (𝓡∂ (k + 1))).target] (c.extend (𝓡∂ (k + 1)) x)) (𝓝 x) := by
    have ht₀ := (c.continuousAt_extend_symm (I := 𝓡∂ (k + 1)) hx).tendsto
    rw [(c.extend (𝓡∂ (k + 1))).left_inv (by simpa only [c.extend_source] using hx)] at ht₀
    exact ht₀.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in
      𝓝[(c.extend (𝓡∂ (k + 1))).target] (c.extend (𝓡∂ (k + 1)) x),
      f ((c.extend (𝓡∂ (k + 1))).symm z) ∈ a.source :=
    (hf.1.tendsto x |>.comp ht).eventually
      (a.open_source.mem_nhds (mem_chart_source _ _))
  filter_upwards [heq, hnear] with z hz hzs
  change b (g (a.symm (β z))) = b (g (f ((c.extend (𝓡∂ (k + 1))).symm z)))
  rw [hz, a.left_inv hzs]

end FsFltz.Geometry.IntrinsicLiouville
