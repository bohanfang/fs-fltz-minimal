import FsFltz.Geometry.TailoringOuterBoundaryHittingNeighborhood
import FsFltz.Geometry.SmoothHittingTimeUniqueness
import FsFltz.Geometry.ImmersionNeighborhood
import FsFltz.Geometry.TailoringAmbientRayPositivity

/-!
# Immersion of the actual outer flow projection on the full fiber

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775,
and the paragraph following `prop:band`, lines 1818–1840.
The inverse is constructed by a locally unique backward hit of the actual
full-fiber scalar level. No inverse or immersion is supplied as an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance outerHittingImmersionCharts :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance outerHittingImmersionSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- A positive scalar crossing has a smooth native local time with a
fixed open time interval of uniqueness. -/
theorem exists_native_local_unique_scalar_hitting_time
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    {f : LGSpace n → ℝ} (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ f)
    (p : ℝ × LGSpace n) (t b : ℝ) (hhit : f (G t p).2 = b)
    (hpos : 0 < deriv (fun s => f (G s p).2) t) :
    ∃ V : Set (ℝ × LGSpace n), IsOpen V ∧ p ∈ V ∧
      ∃ a c : ℝ, t ∈ Ioo a c ∧ ∃ σ : ℝ × LGSpace n → ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ σ V ∧
        σ p = t ∧ (∀ q ∈ V, σ q ∈ Ioo a c ∧ f (G (σ q) q).2 = b) ∧
        ∀ q ∈ V, ∀ s ∈ Ioo a c, f (G s q).2 = b → s = σ q := by
  obtain ⟨x, hx⟩ := lgCover_surjective n p.2
  let H : (ℝ × TangentCoordinates n) × ℝ → ℝ :=
    fun q => f (G q.2 (q.1.1, lgCover q.1.2)).2
  have hcoords : ContMDiff 𝓘(ℝ, (ℝ × TangentCoordinates n) × ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))) ∞
      (fun q : (ℝ × TangentCoordinates n) × ℝ => (q.2, (q.1.1, lgCover q.1.2))) :=
    contDiff_snd.contMDiff.prodMk (contDiff_fst.fst.contMDiff.prodMk
      ((contMDiff_lgCover n).comp contDiff_fst.snd.contMDiff))
  have hH : ContDiff ℝ ∞ H := (hf.comp (hG.comp hcoords).snd).contDiff
  have hg : Differentiable ℝ (fun s => f (G s p).2) :=
    (hf.comp (hG.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable
      (by simp)
  have he : (p.1, lgCover x) = p := Prod.ext rfl hx
  obtain ⟨U, hU, hxU, a, c, ht, σ₀, hσ₀, hσ₀x, hroot, hunique⟩ :=
    exists_smooth_hitting_time_neighborhood_unique (H := H) (p := (p.1, x))
      hH (by simpa only [H, he] using hhit)
      (by simpa only [H, he] using (hg t).hasDerivAt) hpos
  let l := isLocalDiffeomorph_lgCover n x
  let S : Set (ℝ × LGSpace n) := univ ×ˢ l.localInverse.source
  let ψ : ℝ × LGSpace n → ℝ × TangentCoordinates n :=
    fun q => (q.1, l.localInverse q.2)
  have hS : IsOpen S := isOpen_univ.prod l.localInverse.open_source
  have hψ₂ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, TangentCoordinates n) ∞ (fun q : ℝ × LGSpace n => l.localInverse q.2) S :=
    l.localInverse.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hq => hq.2)
  have hψ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × TangentCoordinates n) ∞ ψ S :=
    contMDiff_fst.contMDiffOn.prodMk_space hψ₂
  let V : Set (ℝ × LGSpace n) := S ∩ ψ ⁻¹' U
  let σ : ℝ × LGSpace n → ℝ := σ₀ ∘ ψ
  have hV : IsOpen V := hψ.continuousOn.isOpen_inter_preimage hS hU
  have hcenter : ψ p = (p.1, x) := by
    rw [← he]
    exact Prod.ext rfl (l.localInverse_left_inv l.localInverse_mem_target)
  have hpV : p ∈ V := by
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · rw [← hx]; exact l.localInverse_mem_source
    · change ψ p ∈ U; rw [hcenter]; exact hxU
  have hσM : ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, ℝ) ∞ σ₀ U :=
    contMDiffOn_iff_contDiffOn.mpr hσ₀
  refine ⟨V, hV, hpV, a, c, ht, σ,
    hσM.comp (hψ.mono inter_subset_left) (fun _ hq => hq.2),
    (congrArg σ₀ hcenter).trans hσ₀x, ?_, ?_⟩
  · intro q hq
    have hr := hroot (ψ q) hq.2
    simpa only [H, ψ, σ, Function.comp_apply, l.localInverse_right_inv hq.1.2] using hr
  · intro q hq s hs hqs
    apply hunique (ψ q) hq.2 s hs
    simpa only [H, ψ, l.localInverse_right_inv hq.1.2] using hqs

 /-- Backward scalar hits construct a local inverse to the graph projection
on a smoothly embedded full scalar level. This proves local injectivity
and immersion, without assuming either conclusion. -/
theorem exists_outer_projection_injective_immersion_neighborhood
    {d : ℕ} (M : SmoothManifold d) (j : M.SmoothEmbedding (lgManifold n))
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hfst : ∀ t p, (G t p).1 = p.1)
    {f : LGSpace n → ℝ} (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ f)
    (hlevel : ∀ x, f (j.map x) = 1)
    {W : Set (ℝ × M.Point)} (hW : IsOpen W) {τ : ℝ × M.Point → ℝ}
    (hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ τ W)
    (p : ℝ × M.Point) (hp : p ∈ W)
    (hpos : 0 < deriv (fun t => f (G t (p.1, j.map p.2)).2) 0) :
    ∃ U : Set (ℝ × M.Point), IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      InjOn (fun q => (q.1, (G (τ q) (q.1, j.map q.2)).2)) U ∧
      ∀ q ∈ U, Function.Injective
        (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          (fun r => (r.1, (G (τ r) (r.1, j.map r.2)).2)) q) := by
  let i : ℝ × M.Point → ℝ × LGSpace n := fun q => (q.1, j.map q.2)
  let proj : ℝ × M.Point → ℝ × LGSpace n := fun q => (q.1, (G (τ q) (i q)).2)
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ i :=
    contMDiff_fst.prodMk (j.map.contMDiff.comp contMDiff_snd)
  have hproj₂ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model (2 * n)) ∞ (fun q => (G (τ q) (i q)).2) W := by
    intro q hq
    exact (hG.comp_contMDiffOn (hτ.prodMk hi.contMDiffOn) q hq).snd
  have hproj : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ proj W :=
    contMDiff_fst.contMDiffOn.prodMk hproj₂
  have hback : G (-τ p) (proj p) = i p := by
    have hpair : proj p = G (τ p) (i p) :=
      Prod.ext (hfst (τ p) (i p)).symm rfl
    rw [hpair, ← G.map_add, neg_add_cancel, G.map_zero_apply]
  obtain ⟨V, hV, hpV, a, c, ht, σ, hσ, hσp, hroot, hunique⟩ :=
    exists_native_local_unique_scalar_hitting_time G hG hf (proj p) (-τ p) 1
      (by rw [hback]; exact hlevel p.2)
      (by rw [deriv_scalar_flow_eq_time_zero G hG hf, hback]; exact hpos)
  let R : ℝ × LGSpace n → ℝ × LGSpace n := fun q => (q.1, (G (σ q) q).2)
  have hR : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ R V := by
    apply contMDiff_fst.contMDiffOn.prodMk
    intro q hq
    exact (hG.comp_contMDiffOn (hσ.prodMk contMDiff_id.contMDiffOn) q hq).snd
  let U : Set (ℝ × M.Point) := (W ∩ proj ⁻¹' V) ∩ (fun q => -τ q) ⁻¹' Ioo a c
  have hU : IsOpen U :=
    (hτ.neg.mono inter_subset_left).continuousOn.isOpen_inter_preimage
      (hproj.continuousOn.isOpen_inter_preimage hW hV) isOpen_Ioo
  have hpU : p ∈ U := ⟨⟨hp, hpV⟩, ht⟩
  have hleft : EqOn (R ∘ proj) i U := by
    intro q hq
    have hbackq : G (-τ q) (proj q) = i q := by
      have hpair : proj q = G (τ q) (i q) :=
        Prod.ext (hfst (τ q) (i q)).symm rfl
      rw [hpair, ← G.map_add, neg_add_cancel, G.map_zero_apply]
    have he : -τ q = σ (proj q) :=
      hunique (proj q) hq.1.2 (-τ q) hq.2 (by rw [hbackq]; exact hlevel q.2)
    change (q.1, (G (σ (proj q)) (proj q)).2) = i q
    rw [← he, hbackq]
  refine ⟨U, hU, hpU, fun _ hq => hq.1.1, ?_, ?_⟩
  · intro q hq r hr he
    have hei : i q = i r := (hleft hq).symm.trans ((congrArg R he).trans (hleft hr))
    have hfirst : q.1 = r.1 := congrArg (fun z : ℝ × LGSpace n => z.1) hei
    exact Prod.ext hfirst (j.embedding.injective (congrArg Prod.snd hei))
  · intro q hq
    have hdi : Function.Injective
        (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) i q) :=
      (injective_mfderiv_parameterGraph_iff M (lgManifold n)
        (j := fun _ => j.map) (hi.contMDiffAt.snd.mdifferentiableAt (by simp))).mpr
        (j.immersion q.2)
    have heq : R ∘ proj =ᶠ[𝓝 q] i :=
      Filter.mem_of_superset (hU.mem_nhds hq) (fun r hr => hleft hr)
    have hder := mfderiv_comp (f := proj) (g := R) q
      ((hR.contMDiffAt (hV.mem_nhds hq.1.2)).mdifferentiableAt (by simp))
      ((hproj.contMDiffAt (hW.mem_nhds hq.1.1)).mdifferentiableAt (by simp))
    rw [heq.mfderiv_eq] at hder
    change mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) i q = _ at hder
    intro v w hvw
    apply hdi
    rw [hder]
    exact congrArg (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) R (proj q)) hvw

end FsFltz
