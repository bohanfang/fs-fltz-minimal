import FsFltz.Geometry.CompletionCollarRecovery
import FsFltz.Geometry.FamilyLiouvillePresentation
import FsFltz.Geometry.FamilyPullback

/-!
# Smooth completion presentations from varying compact Liouville primitives

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.

For pointwise supplied completions of a fixed compact domain, jointly smooth
primitives produce coherent compact and completion presentations. Their
transported completed primitives and fields are jointly smooth, including
extensions through the parameter endpoints. The actual compact collar and
its presentation isotopy are constructed from the primitives. Negative-radius
ODE uniqueness recovers each completion on that collar, deriving the common
completion gluing square. The varying-map pullback theorem supplies the
compact coefficient regularity used by the completed-family constructor.

Pointwise completion existence remains supplied input. This theorem imposes
no family regularity or collar compatibility on those completions and proves
none of the geometric target `thm:target` (lines 352–415).
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise supplied completions of a compact Liouville family have actual
coherent presentations whose transported completed primitives and fields are
jointly smooth. Only the compact primitive family is assumed smooth; the
compact collar, its isotopy, and the common completion square are outputs
of the foundation constructions. This does not assert pointwise completion
existence for the original extension presentation. -/
theorem exists_smooth_completionFamily_of_liouvilleFamily {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (C : ∀ t : Parameter, Completion (⟨D, L t⟩ : LiouvilleDomain d)) :
    ∃ h : ℝ → DomainPresentationEquiv D D,
      (∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv.symm p.2) ∧
      (∀ x, (h 0).extensionEquiv x = x) ∧
      ∃ p : ∀ t : Parameter,
          CompletionPresentationEquiv (C parameterZero) (C t) (h t.val),
        (C parameterZero).ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
          (C parameterZero).ambient.manifold.pullback (C t).ambient.manifold
            (p t).equiv (C t).ambient.primitive) ∧
        (C parameterZero).ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
          (C parameterZero).ambient.manifold.pullbackVectorField (C t).ambient.manifold
            (p t).equiv (C t).ambient.field) := by
  obtain ⟨δ, hδ, c, _hc, hzero, hside, hode, h, hboundary, hs, hsinv, h0, hcollar⟩ :=
    D.exists_liouvilleFamily_collarPresentation L hα
  have hnegative (t : Parameter) (x : D.boundary.Point) (r : ℝ)
      (hr : r ∈ Ioc (-δ) 0) :
      (C t).endMap (x, r) = (C t).inclusion.map (c (t.val, (x, r))) := by
    apply (C t).endMap_eq_inclusion_of_negative_collar (fun q => c (t.val, q)) hδ
      (hzero t.val)
    · intro y s hs
      exact (hside t y s ⟨hs.1, lt_of_le_of_lt hs.2 hδ⟩).mpr hs.2
    · intro y s hs
      exact hode t y s ⟨hs.1, lt_of_le_of_lt hs.2 hδ⟩ hs.2
    · exact hr
  have hsquare : ∀ (t : Parameter), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      ∀ x ∈ D.carrier, (C parameterZero).inclusion.map x = (C parameterZero).endMap q →
        (C t).inclusion.map ((h t.val).extensionEquiv x) =
          (C t).endMap ((h t.val).boundaryEquiv q.1, q.2) := by
    intro t q hq x hx he
    have hr : q.2 ≤ 0 := ((C parameterZero).endMap_mem_compact_iff q).mp ⟨x, hx, he⟩
    have hn : q.2 ∈ Ioc (-δ) 0 := ⟨hq.2.1, hr⟩
    have hsource : (C parameterZero).endMap q =
        (C parameterZero).inclusion.map (c (0, q)) :=
      hnegative parameterZero q.1 q.2 hn
    have hxq : x = c (0, q) :=
      (C parameterZero).inclusion.embedding.injective (he.trans hsource)
    rw [hxq, hcollar t.val t.property q hq, hboundary]
    exact (hnegative t q.1 q.2 hn).symm
  have hpull : D.extension.IsSmoothIntervalFormFamily (fun t : Parameter =>
      D.extension.pullback D.extension (h t.val).extensionEquiv (L t).primitive) :=
    D.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
      D.extension (fun t => (h t).extensionEquiv) hs (fun t => (L t).primitive) hα
  obtain ⟨p, hp, hz⟩ := (C parameterZero).exists_smooth_completionFamily_of_collar_presentations
    (fun t : Parameter => (⟨D, L t⟩ : LiouvilleDomain d)) C
    (fun t => h t.val) hpull δ hδ hsquare
  exact ⟨h, hboundary, hs, hsinv, h0, p, hp, hz⟩

end CompactDomain
end FsFltz.Geometry
