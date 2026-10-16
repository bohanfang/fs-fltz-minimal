import FsFltz.Geometry.LiouvilleLocalSide
import FsFltz.Geometry.LiouvilleLocalCollar

/-!
# Uniform domain side of a constructed Liouville collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–158, and `sec:lean`,
lines 783–814. An injective two-sided boundary flow strip meets the boundary
only at time zero. On each connected positive or negative time interval,
the continuous orbit avoids the frontier, so membership in the compact
domain is constant. The pointwise outward-trajectory calculation determines
that constant. This propagates the local side identity to the whole common
collar strip without assuming uniform differential inequalities.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

private theorem mem_iff_of_avoid_frontier {X : Type*} [TopologicalSpace X]
    {C : Set X} (hC : IsClosed C) {γ : ℝ → X} (hγ : Continuous γ)
    {S : Set ℝ} (hS : IsPreconnected S)
    (havoid : ∀ t ∈ S, γ t ∉ frontier C) {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) :
    γ s ∈ C ↔ γ t ∈ C := by
  have hcover : S ⊆ (γ ⁻¹' interior C) ∪ (γ ⁻¹' Cᶜ) := by
    intro u hu
    by_cases hmem : γ u ∈ C
    · exact Or.inl ((mem_interior_iff_notMem_frontier hmem).mpr (havoid u hu))
    · exact Or.inr hmem
  have hdis : Disjoint (γ ⁻¹' interior C) (γ ⁻¹' Cᶜ) := by
    apply disjoint_left.mpr
    intro u hu hv
    exact hv (interior_subset hu)
  rcases IsPreconnected.subset_or_subset (isOpen_interior.preimage hγ)
    (hC.isOpen_compl.preimage hγ) hdis hcover hS with H | H
  · exact iff_of_true (interior_subset (H hs)) (interior_subset (H ht))
  · exact iff_of_false (H hs) (H ht)

namespace LiouvilleStructure

set_option backward.isDefEq.respectTransparency false in
/-- An injective boundary flow strip has its entire negative half inside
the domain and its entire positive half outside. The side at zero comes
from outwardness and the actual ODE, not from an assumed side certificate. -/
theorem flow_mem_carrier_iff_nonpos_of_collar_injective {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (F : Flow ℝ D.extension.Point) {δ : ℝ} (hδ : 0 < δ)
    (hode : ∀ x : D.boundary.Point,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun t => F t (D.boundaryInclusion.map x)) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (L.field (F 0 (D.boundaryInclusion.map x)))))
    (hinj : InjOn (fun p : D.boundary.Point × ℝ =>
      F p.2 (D.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ))
    (x : D.boundary.Point) {t : ℝ} (ht : t ∈ Ioo (-δ) δ) :
    F t (D.boundaryInclusion.map x) ∈ D.carrier ↔ t ≤ 0 := by
  let γ : ℝ → D.extension.Point := fun r => F r (D.boundaryInclusion.map x)
  have hγ : Continuous γ := F.continuous continuous_id continuous_const
  have hzero : γ 0 = D.boundaryInclusion.map x := F.map_zero_apply _
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have havoid : ∀ r ∈ Ioo (-δ) δ, r ≠ 0 → γ r ∉ frontier D.carrier := by
    intro r hr hne hfrontier
    have hmem : γ r ∈ range D.boundaryInclusion.map := by
      rwa [D.boundary_range]
    obtain ⟨y, hy⟩ := hmem
    have he : (x, r) = (y, (0 : ℝ)) :=
      hinj ⟨mem_univ _, hr⟩ ⟨mem_univ _, h0⟩
        (by simpa only [Flow.map_zero_apply] using hy.symm)
    exact hne (congrArg Prod.snd he)
  have hside := L.eventually_mem_carrier_iff_nonpos x hzero (hode x)
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff_ball.mp hside
  let a : ℝ := min δ ε / 2
  have ha : 0 < a := half_pos (lt_min hδ hε)
  have haδ : a < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hε)) (min_le_left _ _)
  have haε : a < ε := lt_of_lt_of_le (half_lt_self (lt_min hδ hε)) (min_le_right _ _)
  have hballneg : -a ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  have hballpos : a ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  rcases lt_trichotomy t 0 with hn | hz | hp
  · have hseed : γ (-a) ∈ D.carrier := (H _ hballneg).mpr (le_of_lt (neg_lt_zero.mpr ha))
    have hsame : γ t ∈ D.carrier ↔ γ (-a) ∈ D.carrier :=
      mem_iff_of_avoid_frontier D.compact.isClosed hγ isPreconnected_Ioo
        (fun r hr => havoid r ⟨hr.1, lt_trans hr.2 hδ⟩ (ne_of_lt hr.2))
        ⟨ht.1, hn⟩ ⟨neg_lt_neg haδ, neg_lt_zero.mpr ha⟩
    exact iff_of_true (hsame.mpr hseed) (le_of_lt hn)
  · subst t
    rw [Flow.map_zero_apply]
    exact iff_of_true (D.boundaryInclusion_mem_carrier x) le_rfl
  · have hseed : γ a ∉ D.carrier := fun hm => (not_le_of_gt ha) ((H _ hballpos).mp hm)
    have hsame : γ t ∈ D.carrier ↔ γ a ∈ D.carrier :=
      mem_iff_of_avoid_frontier D.compact.isClosed hγ isPreconnected_Ioo
        (fun r hr => havoid r ⟨lt_trans (neg_lt_zero.mpr hδ) hr.1, hr.2⟩
          (ne_of_gt hr.1)) ⟨hp, ht.2⟩ ⟨ha, haδ⟩
    exact iff_of_false (fun hm => hseed (hsame.mp hm)) (not_le_of_gt hp)

end LiouvilleStructure

namespace LiouvilleDomain

set_option backward.isDefEq.respectTransparency false in
/-- Construct the uniform Liouville flow collar together with its actual
domain-side identity on the same entire two-sided strip. Only the original
Liouville domain is supplied; no collar or side property is an input. -/
theorem exists_neighborhood_localCollar_with_side {d : ℕ} (D : LiouvilleDomain d) :
    ∃ (U : TopologicalSpace.Opens D.neighborhoodDomain.extension.Point) (δ : ℝ),
      D.neighborhoodDomain.carrier ⊆ (U : Set D.neighborhoodDomain.extension.Point) ∧
      0 < δ ∧ ∃ F : Flow ℝ D.neighborhoodDomain.extension.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.neighborhoodDomain.extension.Point => F p.1 p.2) ∧
      (∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field (F t x)))) ∧
      InjOn (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
        F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Model d) ∞ (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
          F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) ∧
      ∀ (x : D.neighborhoodDomain.boundary.Point) (t : ℝ), t ∈ Ioo (-δ) δ →
        (F t (D.neighborhoodDomain.boundaryInclusion.map x) ∈
          D.neighborhoodDomain.carrier ↔ t ≤ 0) := by
  obtain ⟨U, δ, hU, hδ, F, hF, hode, hinj, hdiff⟩ := D.exists_neighborhood_localCollar
  refine ⟨U, δ, hU, hδ, F, hF, hode, hinj, hdiff, ?_⟩
  intro x t ht
  apply D.neighborhoodStructure.flow_mem_carrier_iff_nonpos_of_collar_injective F hδ
    (fun y => hode _ (hU (D.neighborhoodDomain.boundaryInclusion_mem_carrier y)) 0
      ⟨neg_lt_zero.mpr hδ, hδ⟩) hinj x ht

end LiouvilleDomain
end FsFltz.Geometry
