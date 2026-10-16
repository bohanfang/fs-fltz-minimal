import FsFltz.Geometry.CompletionFamilyCollar
import FsFltz.Geometry.OriginalBundleCompletionMarkingFieldRegularity

/-!
# Actual completion maps from compact formulas and complete-flow germs

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`def:maslov`, lines 212–244; `geometric-part-fsf-proof.tex`,
`lem:markedfamily`, lines 975–1009. A compact presentation and the actual
complete flow determine smooth target-valued germs on the same completion.
The inward cutoff includes the seam; neither joint regularity of the
completed maps nor any off-interval flow law is an assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold IntrinsicSmoothBundle

/-- Smooth compact formulas and actual complete-flow germs give native
joint germs for the completed maps, including the seam and both parameter
endpoints. The cylindrical equality is required slightly inward of zero. -/
theorem hasSmoothManifoldTargetFamilyOn_of_compact_and_flow_germs
    {d e : ℕ} {D : LiouvilleDomain d} (C : Completion D) (N : SmoothManifold e)
    (f : Parameter → C.ambient.manifold.Point → N.Point)
    (g : ℝ → D.domain.extension.Point → N.Point)
    (b : D.domain.boundary.Point → N.Point)
    (φ : Parameter → ℝ → N.Point → N.Point)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × D.domain.extension.Point => g p.1 p.2))
    (hb : ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model e) ∞ b)
    (hφ : HasRealSmoothFlowGermsOn N univ φ)
    (δ : ℝ) (hδ : 0 < δ)
    (hcompact : ∀ t x, x ∈ D.domain.carrier → f t (C.inclusion.map x) = g t.val x)
    (hend : ∀ t x r, -δ < r → f t (C.endMap (x, r)) = φ t r (b x)) :
    HasSmoothManifoldTargetFamilyOn C.ambient.manifold N univ f := by
  intro t _ z
  by_cases hz : z ∈ C.inclusion.map '' interior D.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hz
    let l := C.inclusion_isLocalDiffeomorph x
    let S : Set C.ambient.manifold.Point :=
      {y | y ∈ l.localInverse.source ∧ l.localInverse y ∈ interior D.domain.carrier}
    have hS : IsOpen S := by
      apply isOpen_iff_mem_nhds.mpr
      intro y hy
      exact inter_mem (l.localInverse.open_source.mem_nhds hy.1)
        ((l.localInverse_contMDiffOn.contMDiffAt
          (l.localInverse.open_source.mem_nhds hy.1)).continuousAt.preimage_mem_nhds
            (isOpen_interior.mem_nhds hy.2))
    let U : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
      ⟨univ ×ˢ S, isOpen_univ.prod hS⟩
    let a : U → N.Point := fun p => g p.val.1 (l.localInverse p.val.2)
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
      intro p
      have hi := l.localInverse_contMDiffOn.contMDiffAt
        (l.localInverse.open_source.mem_nhds p.property.2.1)
      exact hg.contMDiffAt.comp p
        ((contMDiffAt_fst.comp p contMDiff_subtype_val.contMDiffAt).prodMk
          (hi.comp p (contMDiffAt_snd.comp p contMDiff_subtype_val.contMDiffAt)))
    refine ⟨U, ⟨mem_univ _, l.localInverse_mem_source, ?_⟩, a, ha, ?_⟩
    · rw [l.localInverse_left_inv l.localInverse_mem_target]
      exact hx
    · intro s _ y hy
      change g s.val (l.localInverse y) = f s y
      have he : C.inclusion.map (l.localInverse y) = y :=
        l.localInverse_right_inv hy.2.1
      simpa only [he] using (hcompact s _ (interior_subset hy.2.2)).symm
  · have hz' : z ∈ Set.range
        (fun p : D.domain.boundary.Point × Ici (0 : ℝ) => C.endMap (p.1, p.2)) := by
      rw [C.range_nonnegative_endMap]
      exact hz
    obtain ⟨⟨x, r⟩, rfl⟩ := hz'
    let q : D.domain.boundary.Point × ℝ := (x, r.val)
    let l := C.endMap_isLocalDiffeomorph q
    obtain ⟨V, hV, hpV, β, hβ, heq⟩ := hφ t (mem_univ _) r.val (b x)
    let H : ℝ × C.ambient.manifold.Point → ℝ × (ℝ × N.Point) :=
      fun p => (p.1, ((l.localInverse p.2).2, b (l.localInverse p.2).1))
    let S : Set (ℝ × C.ambient.manifold.Point) :=
      univ ×ˢ l.localInverse.source
    have hS : IsOpen S := isOpen_univ.prod l.localInverse.open_source
    have hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e))) ∞ H S := by
      have hi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × C.ambient.manifold.Point => l.localInverse p.2) S :=
        l.localInverse_contMDiffOn.comp contMDiff_snd.contMDiffOn
          (fun _ hp => hp.2)
      exact contMDiff_fst.contMDiffOn.prodMk
        ((contMDiff_snd.comp_contMDiffOn hi).prodMk
          (hb.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn hi)))
    let W : TopologicalSpace.Opens (ℝ × C.ambient.manifold.Point) :=
      ⟨S ∩ H ⁻¹' (V ∩ {p | -δ < p.2.1}),
        hH.continuousOn.isOpen_inter_preimage hS
          (hV.inter (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)))⟩
    let a : W → N.Point := fun p => β (H p.val)
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
      intro p
      exact (hβ.contMDiffAt (hV.mem_nhds p.property.2.1)).comp p
        ((hH.contMDiffAt (hS.mem_nhds p.property.1)).comp p
          contMDiff_subtype_val.contMDiffAt)
    have hinv : l.localInverse (C.endMap q) = q :=
      l.localInverse_left_inv l.localInverse_mem_target
    refine ⟨W, ?_, a, ha, ?_⟩
    · refine ⟨⟨mem_univ _, l.localInverse_mem_source⟩, ?_⟩
      change H (t.val, C.endMap q) ∈ V ∩ {p | -δ < p.2.1}
      simp only [H, hinv]
      exact ⟨hpV, by dsimp [q]; linarith [r.property]⟩
    · intro s _ y hy
      change β (s.val, ((l.localInverse y).2, b (l.localInverse y).1)) = f s y
      rw [heq s (mem_univ _) _ _ hy.2.1]
      have he : C.endMap (l.localInverse y) = y :=
        l.localInverse_right_inv hy.1.2
      simpa only [he] using
        (hend s (l.localInverse y).1 (l.localInverse y).2 hy.2.2).symm

end FsFltz.Geometry.Completion
