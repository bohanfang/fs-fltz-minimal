import FsFltz.Geometry.TailoringFiniteBandHittingSmooth

/-!
# A smooth transverse time with local uniqueness

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775,
and the immersion argument following `prop:band`, lines 1820–1840.
The fixed time interval makes the constructed local root usable as a
local inverse to a transverse flow projection.
-/

noncomputable section
open scoped ContDiff Topology
open Set

namespace FsFltz.Geometry
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Positive time transversality supplies one smooth local root, together
with a fixed time interval on which that root is the only root. -/
theorem exists_smooth_hitting_time_neighborhood_unique
    {H : E × ℝ → ℝ} {p : E} {t q b : ℝ}
    (hH : ContDiff ℝ ∞ H) (hhit : H (p, t) = b)
    (hder : HasDerivAt (fun s => H (p, s)) q t) (hq : 0 < q) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∃ a c : ℝ, t ∈ Ioo a c ∧
      ∃ τ : E → ℝ, ContDiffOn ℝ ∞ τ U ∧ τ p = t ∧
        (∀ x ∈ U, τ x ∈ Ioo a c ∧ H (x, τ x) = b) ∧
        ∀ x ∈ U, ∀ s ∈ Ioo a c, H (x, s) = b → s = τ x := by
  obtain ⟨U₀, hU₀, hp₀, τ, hτ, hτp, hhitτ⟩ :=
    exists_smooth_hitting_time_neighborhood hH hhit hder hq.ne'
  have hH' : ContDiff ℝ ∞
      (Function.uncurry (fun z : E × ℝ => fun s : ℝ => H (z.1, s))) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ ∞ (fun z : E × ℝ =>
      fderiv ℝ (fun s : ℝ => H (z.1, s)) z.2 (1 : ℝ)) :=
    hH'.fderiv_apply contDiff_snd contDiff_const (by simp)
  have ho : IsOpen {z : E × ℝ | 0 < deriv (fun s => H (z.1, s)) z.2} :=
    isOpen_lt continuous_const hd.continuous
  have hpt : (p, t) ∈ {z : E × ℝ | 0 < deriv (fun s => H (z.1, s)) z.2} := by
    change 0 < deriv (fun s => H (p, s)) t
    rw [hder.deriv]
    exact hq
  obtain ⟨V, J, hV, hJ, hpV, htJ, hVJ⟩ := isOpen_prod_iff.mp ho p t hpt
  obtain ⟨a, c, htac, hacJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds htJ)
  let U : Set E := (U₀ ∩ τ ⁻¹' Ioo a c) ∩ V
  have hU : IsOpen U :=
    (hτ.continuousOn.isOpen_inter_preimage hU₀ isOpen_Ioo).inter hV
  have hpU : p ∈ U := ⟨⟨hp₀, by simpa only [mem_preimage, hτp] using htac⟩, hpV⟩
  refine ⟨U, hU, hpU, a, c, htac, τ, hτ.mono (fun _ hx => hx.1.1), hτp,
    (fun x hx => ⟨hx.1.2, hhitτ x hx.1.1⟩), ?_⟩
  intro x hx s hs hxs
  have hmono : StrictMonoOn (fun r => H (x, r)) (Ioo a c) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a c)
      (hH.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun r hr => hVJ (a := (x, r)) ⟨hx.2, hacJ (interior_subset hr)⟩)
  exact hmono.injOn hs hx.1.2 (hxs.trans (hhitτ x hx.1.1).symm)

end FsFltz.Geometry
