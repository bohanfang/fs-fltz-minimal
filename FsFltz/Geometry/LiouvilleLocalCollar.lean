import FsFltz.Geometry.BoundaryNondegeneracy
import FsFltz.Geometry.LocalInverse
import FsFltz.Geometry.LiouvilleLocalFlow

/-!
# Local Liouville collar differential

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 805–814. This is the local inverse part of the Liouville collar
foundation: the boundary tangent hyperplane together with the outward field
span the ambient tangent space. The smooth boundary evolution therefore has
an invertible differential at time zero and a smooth local inverse.

The differential is derived from the initial-value and time-derivative
identities, rather than assumed invertible. Compactness of the boundary and
injectivity of its inclusion give an injective neighborhood of the zero-time
seam. Intersecting it with the open local-diffeomorphism locus and applying the
tube lemma gives one positive two-sided width. The constructed local flow in
the symplectic neighborhood supplies the evolution used by the final theorem.

No completion is an input. The exponential primitive identity and completion
gluing are separate obligations; this does not prove `thm:target`, lines
352–415. The auxiliary action is globally defined, but the original Liouville
ODE is asserted only on the constructed neighborhood and time interval.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace LiouvilleStructure

set_option backward.isDefEq.respectTransparency false in
/-- The actual differential of a smooth boundary evolution at time zero is
the boundary inclusion differential plus the time component times the field.
The two components are obtained by the manifold chain rule. -/
theorem boundaryFlow_mfderiv_zero {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D)
    (c : D.boundary.Point × ℝ → D.extension.Point)
    (x : D.boundary.Point)
    (hc : MDifferentiableAt ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) c (x, 0))
    (hzero : ∀ y, c (y, 0) = D.boundaryInclusion.map y)
    (htime : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
      L.field (D.boundaryInclusion.map x))
    (v : D.boundary.Tangent x) (s : ℝ) :
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d)) c (x, 0)
      (v, s) =
      mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d)) D.boundaryInclusion.map x v +
        s • L.field (D.boundaryInclusion.map x) := by
  change Model (d - 1) at v
  have hspace := mfderiv_comp_apply (f := fun y : D.boundary.Point => (y, (0 : ℝ)))
    (g := c) x hc (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v
  have hinit : (fun y : D.boundary.Point => c (y, (0 : ℝ))) =
      D.boundaryInclusion.map := funext hzero
  change mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d))
    (fun y => c (y, (0 : ℝ))) x v = _ at hspace
  rw [hinit] at hspace
  dsimp only [TangentSpace] at hspace
  erw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const,
    mfderiv_id, mfderiv_const] at hspace
  change mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d))
    D.boundaryInclusion.map x v =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) c (x, 0) (v, 0) at hspace
  have ht := mfderiv_comp_apply (f := fun t : ℝ => (x, t)) (g := c) 0 hc
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (1 : ℝ)
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) = _ at ht
  erw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id,
    mfderiv_const, mfderiv_id] at ht
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
    mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) c (x, 0) (0, (1 : ℝ)) at ht
  have hsplit : (v, s) = (v, (0 : ℝ)) + s • (0, (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_smul, ← hspace, ← ht, htime]

set_option backward.isDefEq.respectTransparency false in
/-- Outwardness makes the derived boundary-flow differential bijective.
The zero-dimensional case has no boundary point to which this applies. -/
theorem boundaryFlow_mfderiv_zero_bijective {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D)
    (c : D.boundary.Point × ℝ → D.extension.Point)
    (x : D.boundary.Point)
    (hc : MDifferentiableAt ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) c (x, 0))
    (hzero : ∀ y, c (y, 0) = D.boundaryInclusion.map y)
    (htime : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
      L.field (D.boundaryInclusion.map x)) :
    Function.Bijective
      (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, Model d)) c (x, 0)) := by
  let ρ := D.defining _ (D.boundaryInclusion_mem_frontier x)
  let A := (mfderiv (𝓘(ℝ, Model (d - 1))) (𝓘(ℝ, Model d))
    D.boundaryInclusion.map x).toLinearMap
  let p := (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, ℝ)) ρ.rho
    (D.boundaryInclusion.map x)).toLinearMap
  have hd : d ≠ 0 := by
    intro h
    subst d
    have : IsEmpty D.boundary.Point := D.zero_boundary rfl
    exact isEmptyElim x
  have hdim : Module.finrank ℝ (D.boundary.Tangent x) + 1 =
      Module.finrank ℝ (D.extension.Tangent (D.boundaryInclusion.map x)) := by
    change Module.finrank ℝ (Model (d - 1)) + 1 = Module.finrank ℝ (Model d)
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  have hbij := tangent_prod_span_bijective A p (L.field (D.boundaryInclusion.map x))
    (D.boundaryInclusion.immersion x) (D.boundaryInclusion_derivative_tangent x ρ)
    (ne_of_gt (L.outward _ (D.boundaryInclusion_mem_frontier x))) hdim
  have heq : (mfderiv ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) c (x, 0)).toLinearMap =
      A.coprod ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight
        (L.field (D.boundaryInclusion.map x))) := by
    ext q
    exact L.boundaryFlow_mfderiv_zero c x hc hzero htime q.1 q.2
  rw [← heq] at hbij
  exact hbij

set_option backward.isDefEq.respectTransparency false in
/-- A smooth boundary evolution has a native smooth local inverse near each
boundary point at zero time. Its derivative is proved invertible above. -/
theorem boundaryFlow_isLocalDiffeomorphAt_zero {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D)
    (c : D.boundary.Point × ℝ → D.extension.Point)
    {U : Set (D.boundary.Point × ℝ)} (hU : IsOpen U)
    (hc : ContMDiffOn ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) ∞ c U)
    (x : D.boundary.Point) (hx : (x, 0) ∈ U)
    (hzero : ∀ y, c (y, 0) = D.boundaryInclusion.map y)
    (htime : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
      L.field (D.boundaryInclusion.map x)) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) ∞ c (x, 0) := by
  have hbij := L.boundaryFlow_mfderiv_zero_bijective c x
    ((hc.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)) hzero htime
  have hprod : IsManifold ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) ∞
      (D.boundary.Point × ℝ) := inferInstance
  rw [← modelWithCornersSelf_prod] at hc hbij ⊢
  let : ChartedSpace (Model (d - 1) × ℝ) (D.boundary.Point × ℝ) :=
    prodChartedSpace (Model (d - 1)) D.boundary.Point ℝ ℝ
  have : IsManifold (𝓘(ℝ, Model (d - 1) × ℝ)) ∞ (D.boundary.Point × ℝ) := by
    rw [← modelWithCornersSelf_prod] at hprod
    exact hprod
  exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hU hc hx hbij

set_option backward.isDefEq.respectTransparency false in
/-- Compactness turns the proved local inverses along the zero-time seam
into one injective neighborhood and one common positive two-sided width. -/
theorem exists_uniform_boundaryFlow_collar {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D)
    (c : D.boundary.Point × ℝ → D.extension.Point)
    (hc : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) ∞ c)
    (hzero : ∀ y, c (y, 0) = D.boundaryInclusion.map y)
    (htime : ∀ x, mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
      L.field (D.boundaryInclusion.map x)) :
    ∃ (U : TopologicalSpace.Opens (D.boundary.Point × ℝ)) (δ : ℝ),
      0 < δ ∧ univ ×ˢ Ioo (-δ) δ ⊆ (U : Set (D.boundary.Point × ℝ)) ∧
      InjOn c U ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, Model d)) ∞ c U := by
  let K : Set (D.boundary.Point × ℝ) := univ ×ˢ ({0} : Set ℝ)
  have hb : IsCompact (univ : Set D.boundary.Point) := by
    rw [D.boundaryInclusion.embedding.isCompact_iff, image_univ, D.boundary_range]
    exact D.compact.of_isClosed_subset isClosed_frontier D.compact.isClosed.frontier_subset
  have hK : IsCompact K := hb.prod isCompact_singleton
  have hinj : InjOn c K := by
    rintro ⟨x, r⟩ ⟨_, hr⟩ ⟨y, s⟩ ⟨_, hs⟩ he
    have hr0 : r = 0 := hr
    have hs0 : s = 0 := hs
    subst r
    subst s
    rw [hzero, hzero] at he
    exact Prod.ext (D.boundaryInclusion.embedding.injective he) rfl
  have hloc (p : D.boundary.Point × ℝ) (hp : p ∈ K) :
      IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, Model d)) ∞ c p := by
    obtain ⟨x, r⟩ := p
    have hr : r = 0 := hp.2
    subst r
    exact L.boundaryFlow_isLocalDiffeomorphAt_zero c isOpen_univ hc.contMDiffOn
      x (mem_univ _) hzero (htime x)
  obtain ⟨V, hVo, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun p hp => (hloc p hp).contMDiffAt.continuousAt) (by
      intro p hp
      obtain ⟨e, he, heq⟩ := hloc p hp
      refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
      intro a ha b hb hab
      apply e.toPartialEquiv.injOn ha hb
      rw [← heq ha, ← heq hb]
      exact hab)
  let T : TopologicalSpace.Opens (D.boundary.Point × ℝ) :=
    { carrier := {p | IsLocalDiffeomorphAt
        ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, Model d)) ∞ c p}
      is_open' := by
        apply isOpen_iff_mem_nhds.mpr
        rintro p ⟨e, hp, he⟩
        apply mem_of_superset (e.open_source.mem_nhds hp)
        intro q hq
        exact ⟨e, hq, he⟩ }
  let U : TopologicalSpace.Opens (D.boundary.Point × ℝ) := ⟨V ∩ T, hVo.inter T.isOpen⟩
  have hKU : K ⊆ U := fun p hp => ⟨hKV hp, hloc p hp⟩
  obtain ⟨P, Q, _, hQ, hBP, hzeroQ, hPQ⟩ :=
    generalized_tube_lemma hb isCompact_singleton U.isOpen hKU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hQ.mem_nhds (hzeroQ (mem_singleton 0)))
  refine ⟨U, δ, hδ, ?_, hVi.mono inter_subset_left, fun p => p.property.2⟩
  rintro ⟨x, r⟩ ⟨_, hr⟩
  apply hPQ
  refine ⟨hBP (mem_univ x), hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hr

end LiouvilleStructure

namespace LiouvilleDomain

set_option backward.isDefEq.respectTransparency false in
/-- Construct an actual uniform local Liouville collar from the domain.
The action solves the Liouville ODE on a neighborhood of the compact domain,
and its boundary restriction is injective with smooth local inverses on a
single positive-width open cylinder. No flow or completion is an input. -/
theorem exists_neighborhood_localCollar {d : ℕ} (D : LiouvilleDomain d) :
    ∃ (U : TopologicalSpace.Opens D.neighborhoodDomain.extension.Point) (δ : ℝ),
      D.neighborhoodDomain.carrier ⊆ (U : Set D.neighborhoodDomain.extension.Point) ∧
      0 < δ ∧ ∃ F : Flow ℝ D.neighborhoodDomain.extension.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) (𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × D.neighborhoodDomain.extension.Point => F p.1 p.2) ∧
      (∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun s => F s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field (F t x)))) ∧
      InjOn (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
        F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, Model d)) ∞ (fun p : D.neighborhoodDomain.boundary.Point × ℝ =>
          F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) := by
  obtain ⟨U, δ₀, hU, hδ₀, F, hF, hode⟩ := D.exists_neighborhood_localFlow
  let c : D.neighborhoodDomain.boundary.Point × ℝ → D.neighborhoodDomain.extension.Point :=
    fun p => F p.2 (D.neighborhoodDomain.boundaryInclusion.map p.1)
  have hc : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, Model d)) ∞ c :=
    hF.comp (contMDiff_snd.prodMk
      (D.neighborhoodDomain.boundaryInclusion.map.contMDiff.comp contMDiff_fst))
  have hzero : ∀ y, c (y, 0) = D.neighborhoodDomain.boundaryInclusion.map y :=
    fun y => F.map_zero_apply _
  have htime (x : D.neighborhoodDomain.boundary.Point) :
      mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model d)) (fun t => c (x, t)) 0 (1 : ℝ) =
        D.neighborhoodStructure.field (D.neighborhoodDomain.boundaryInclusion.map x) := by
    have hd := hode _ (hU (D.neighborhoodDomain.boundaryInclusion_mem_carrier x)) 0
      (by exact ⟨neg_lt_zero.mpr hδ₀, hδ₀⟩)
    rw [hd.mfderiv]
    change (1 : ℝ) • D.neighborhoodStructure.field
      (F 0 (D.neighborhoodDomain.boundaryInclusion.map x)) = _
    rw [one_smul, Flow.map_zero_apply]
  obtain ⟨V, δ₁, hδ₁, hw, hinj, hdiff⟩ :=
    D.neighborhoodStructure.exists_uniform_boundaryFlow_collar c hc hzero htime
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hsub₀ : Ioo (-δ) δ ⊆ Ioo (-δ₀) δ₀ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsub₁ : univ ×ˢ Ioo (-δ) δ ⊆ (V : Set (D.neighborhoodDomain.boundary.Point × ℝ)) :=
    (prod_mono_right (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _))
      (min_le_right _ _))).trans hw
  exact ⟨U, δ, hU, hδ, F, hF, (fun x hx t ht => hode x hx t (hsub₀ ht)),
    hinj.mono hsub₁, (fun p => hdiff ⟨p.val, hsub₁ p.property⟩)⟩

end LiouvilleDomain
end FsFltz.Geometry
