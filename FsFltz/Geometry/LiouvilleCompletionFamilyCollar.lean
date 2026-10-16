import FsFltz.Geometry.LiouvilleCompletionFamily

/-!
# Retaining the actual common collar of completion-family presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009.
This stronger internal producer retains the inward end formula constructed
by the existing compact collar and completion-family machinery. It imposes
no new regularity or presentation-compatibility input on the completions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.CompactDomain
open SmoothManifold

/-- The compact Liouville-family construction retains a common inward
collar on which its actual completed presentations are cylindrical. -/
theorem exists_smooth_completionFamily_with_inward_end_square {d : ℕ}
    (D : CompactDomain d) (L : Parameter → LiouvilleStructure D)
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
            (p t).equiv (C t).ambient.field) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ t x r, -δ < r →
          (p t).equiv ((C parameterZero).endMap (x, r)) = (C t).endMap (x, r) := by
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
        (C parameterZero).inclusion.map (c (0, q)) := hnegative parameterZero q.1 q.2 hn
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
  refine ⟨h, hboundary, hs, hsinv, h0, p, hp, hz, δ, hδ, ?_⟩
  intro t x r hr
  by_cases hnonneg : 0 ≤ r
  · have he := (p t).end_square x r hnonneg
    rw [hboundary] at he
    exact he
  · have hs := (p t).end_square_of_compact_collar
      (univ ×ˢ Ioo (-δ) δ) (hsquare t) (x, r)
      ⟨mem_univ _, hr, lt_trans (lt_of_not_ge hnonneg) hδ⟩
    rw [hboundary] at hs
    exact hs

end FsFltz.Geometry.CompactDomain
