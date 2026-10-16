import FsFltz.Geometry.FamilyLiouvilleLocalFlow
import FsFltz.Geometry.FamilyLiouvillePrimitive
import FsFltz.Geometry.LiouvilleLocalCollar
import FsFltz.Geometry.CompactCollarFamily
import FsFltz.Geometry.LiouvilleCollarSide

/-!
# A uniformly embedded local collar for varying Liouville primitives

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 783–814.
The boundary evolution comes from the constructed parameter-preserving local
flow. Outwardness proves its spatial differential invertible at the seam;
retaining the parameter gives jointly smooth local inverses. Compactness of
`[0,1] × ∂D` then gives one open parameter neighborhood and one positive
two-sided collar width on which that same map is an open embedding.

The original Liouville ODE is asserted only for interval parameters. No
Liouville geometry outside the interval, collars, or completions are supplied
as input. The domain-side and exponential primitive identities use the same
flow and collar. Completion gluing and the geometric target remain separate
obligations.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace CollarFlow

/-- The spatial action of a parameter-preserving flow at a fixed parameter.
Its action law is inherited from the same auxiliary flow. -/
def parameterSlice {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ (ℝ × X)) (hfst : ∀ s p, (F s p).1 = p.1) (t : ℝ) : Flow ℝ X where
  toFun := fun s x => (F s (t, x)).2
  cont' := continuous_snd.comp
    (F.continuous continuous_fst (continuous_const.prodMk continuous_snd))
  map_add' := by
    intro s u x
    have he : F u (t, x) = (t, (F u (t, x)).2) := Prod.ext (hfst _ _) rfl
    have hadd := congrArg Prod.snd (F.map_add s u (t, x))
    rw [he] at hadd
    exact hadd
  map_zero' := fun x => congrArg Prod.snd (F.map_zero_apply (t, x))

end CollarFlow
namespace CompactDomain

/-- Boundary evolution of the actual auxiliary family flow. -/
def boundaryFamilyFlow {d : ℕ} (D : CompactDomain d)
    (F : Flow ℝ (ℝ × D.extension.Point)) (p : ℝ × (D.boundary.Point × ℝ)) :
    D.extension.Point := (F p.2.2 (p.1, D.boundaryInclusion.map p.2.1)).2

/-- Retaining the original parameter makes the family collar one actual
map between product manifolds. -/
def boundaryFamilyFlowWithParameter {d : ℕ} (D : CompactDomain d)
    (F : Flow ℝ (ℝ × D.extension.Point)) (p : ℝ × (D.boundary.Point × ℝ)) :
    ℝ × D.extension.Point := (p.1, D.boundaryFamilyFlow F p)

set_option backward.isDefEq.respectTransparency false in
/-- A jointly smooth boundary evolution with its actual initial value and
Liouville time derivative has one uniformly embedded collar. The interval
geometric hypotheses suffice for an open parameter neighborhood of embeddings.
Seam differential invertibility is derived from outwardness. -/
theorem exists_uniform_boundaryFamily_collar {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
    (hc : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞ c)
    (hzero : ∀ t x, c (t, (x, 0)) = D.boundaryInclusion.map x)
    (htime : ∀ (t : Parameter) (x : D.boundary.Point),
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun r => c (t.val, (x, r))) 0 (1 : ℝ) =
        (L t).field (D.boundaryInclusion.map x)) :
    ∃ (J : TopologicalSpace.Opens ℝ) (δ : ℝ),
      parameterInterval ⊆ (J : Set ℝ) ∧ 0 < δ ∧
      InjOn (fun p : ℝ × (D.boundary.Point × ℝ) => (p.1, c p))
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (D.boundary.Point × ℝ) => (p.1, c p))
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      Topology.IsOpenEmbedding
        (fun p : {p : ℝ × (D.boundary.Point × ℝ) //
            p ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)} => (p.val.1, c p.val)) := by
  let f : ℝ × (D.boundary.Point × ℝ) → ℝ × D.extension.Point :=
    fun p => (p.1, c p)
  let K : Set (ℝ × (D.boundary.Point × ℝ)) :=
    parameterInterval ×ˢ (univ ×ˢ ({0} : Set ℝ))
  have hK : IsCompact K := isCompact_Icc.prod (D.isCompact_boundary.prod isCompact_singleton)
  have hloc : ∀ p ∈ K, IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ f p := by
    rintro ⟨t, x, r⟩ hp
    have hr : r = 0 := hp.2.2
    subst r
    let t' : Parameter := ⟨t, hp.1⟩
    have hs : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Model d) ∞ (fun q => c (t, q)) :=
      hc.comp (contMDiff_const.prodMk contMDiff_id)
    have hbij := (L t').boundaryFlow_mfderiv_zero_bijective (fun q => c (t, q)) x
      (hs.mdifferentiableAt (by simp)) (hzero t) (htime t' x)
    have hpB : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (D.boundary.Point × ℝ) := inferInstance
    let : ChartedSpace (Model (d - 1) × ℝ) (D.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.boundary.Point ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hpB hc hbij ⊢
    exact isLocalDiffeomorphAt_retainingParameter isOpen_univ hc.contMDiffOn
      (mem_univ _) hbij
  have hinj : InjOn f K := by
    rintro ⟨t, x, r⟩ hp ⟨u, y, s⟩ hq he
    have hr : r = 0 := hp.2.2
    have hs : s = 0 := hq.2.2
    subst r
    subst s
    have ht : t = u := congrArg Prod.fst he
    have hx := congrArg Prod.snd he
    change c (t, (x, 0)) = c (u, (y, 0)) at hx
    rw [hzero, hzero] at hx
    exact Prod.ext ht (Prod.ext (D.boundaryInclusion.embedding.injective hx) rfl)
  obtain ⟨V, hV, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun p hp => (hloc p hp).contMDiffAt.continuousAt) (by
      intro p hp
      obtain ⟨e, he, heq⟩ := hloc p hp
      refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
      intro a ha b hb hab
      exact e.toPartialEquiv.injOn ha hb ((heq ha).symm.trans (hab.trans (heq hb))))
  let T : TopologicalSpace.Opens (ℝ × (D.boundary.Point × ℝ)) :=
    { carrier := {p | IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ f p}
      is_open' := by
        apply isOpen_iff_mem_nhds.mpr
        rintro p ⟨e, hp, he⟩
        exact mem_of_superset (e.open_source.mem_nhds hp) (fun q hq => ⟨e, hq, he⟩) }
  let W : TopologicalSpace.Opens (ℝ × (D.boundary.Point × ℝ)) :=
    ⟨V ∩ T, hV.inter T.isOpen⟩
  have hKW : K ⊆ W := fun p hp => ⟨hKV hp, hloc p hp⟩
  obtain ⟨A, B, hA, hB, hIA, hKB, hAB⟩ := generalized_tube_lemma
    isCompact_Icc (D.isCompact_boundary.prod isCompact_singleton) W.isOpen hKW
  obtain ⟨P, Q, _, hQ, hBP, hzeroQ, hPQ⟩ := generalized_tube_lemma
    D.isCompact_boundary isCompact_singleton hB hKB
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hQ.mem_nhds (hzeroQ (mem_singleton 0)))
  let J : TopologicalSpace.Opens ℝ := ⟨A, hA⟩
  let C : TopologicalSpace.Opens (ℝ × (D.boundary.Point × ℝ)) :=
    ⟨(J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ), J.isOpen.prod (isOpen_univ.prod isOpen_Ioo)⟩
  have hCW : (C : Set (ℝ × (D.boundary.Point × ℝ))) ⊆ W := by
    rintro ⟨t, x, r⟩ hp
    apply hAB
    refine ⟨hp.1, hPQ ⟨hBP (mem_univ x), hball ?_⟩⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hp.2.2
  have hd : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ f C := fun p => (hCW p.property).2
  have hi : InjOn f C := hVi.mono (hCW.trans inter_subset_left)
  have hl : IsLocalHomeomorph (fun p : C => f p.val) := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact hd.isLocalHomeomorphOn.comp C.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn
      (fun p _ => p.property)
  exact ⟨J, δ, hIA, hδ, hi, hd,
    hl.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp hi)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Varying smooth primitives on a fixed compact domain produce a single
uniformly embedded local boundary collar, with jointly smooth local inverses,
the exact domain-side law, and the exponential primitive identity including
the radial differential. Every conclusion uses the same constructed
parameter-preserving flow. No collar or completion is an input. -/
theorem exists_liouvilleFamily_localCollar_invariant {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ (U : TopologicalSpace.Opens (ℝ × D.extension.Point))
      (J : TopologicalSpace.Opens ℝ) (δ : ℝ) (F : Flow ℝ (ℝ × D.extension.Point)),
      parameterInterval ×ˢ D.carrier ⊆ (U : Set (ℝ × D.extension.Point)) ∧
      parameterInterval ⊆ (J : Set ℝ) ∧ 0 < δ ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => F p.1 p.2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      (∀ (t : Parameter) s x,
        x ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood ↔
          (F s (t.val, x)).2 ∈ (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood) ∧
      (∀ (t : Parameter) (x : D.extension.Point), (t.val, x) ∈ U →
        ∀ r ∈ Ioo (-δ) δ,
          D.extension.Nondegenerate
            (D.extension.exteriorDerivative ((L t).primitive)) (F r (t.val, x)).2 ∧
          D.extension.LiouvilleEquation ((L t).primitive) (F r (t.val, x)).2
            (D.extension.liouvilleVector ((L t).primitive) (F r (t.val, x)).2) ∧
          HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
            (fun u => (F u (t.val, x)).2) r
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (D.extension.liouvilleVector ((L t).primitive) (F r (t.val, x)).2))) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
        (D.boundaryFamilyFlow F) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (D.boundaryFamilyFlowWithParameter F) ∧
      (∀ t x, D.boundaryFamilyFlow F (t, (x, 0)) = D.boundaryInclusion.map x) ∧
      InjOn (D.boundaryFamilyFlowWithParameter F)
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (D.boundaryFamilyFlowWithParameter F)
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      Topology.IsOpenEmbedding
        (fun p : {p : ℝ × (D.boundary.Point × ℝ) //
            p ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)} =>
          D.boundaryFamilyFlowWithParameter F p.val) ∧
      (∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
        (D.boundaryFamilyFlow F (t.val, (x, r)) ∈ D.carrier ↔ r ≤ 0)) ∧
      ∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
        ∀ (v : Model (d - 1)) (s : ℝ),
          evalOne ((L t).primitive) (D.boundaryFamilyFlow F (t.val, (x, r)))
            (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
              (fun q : D.boundary.Point × ℝ => D.boundaryFamilyFlow F (t.val, q))
              (x, r) (v, s)) =
            Real.exp r * evalOne (D.boundaryForm ((L t).primitive)) x v := by
  obtain ⟨U, δ₀, hU, hδ₀, F, hF, hFspatial, hfst, hinvariant, hlocal⟩ :=
    D.exists_liouvilleFamily_localFlow_invariant L halpha
  have hc : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
      (D.boundaryFamilyFlow F) :=
    hFspatial.comp ((contMDiff_snd.comp contMDiff_snd).prodMk
      (contMDiff_fst.prodMk
        (D.boundaryInclusion.map.contMDiff.comp (contMDiff_fst.comp contMDiff_snd))))
  have hzero : ∀ t x, D.boundaryFamilyFlow F (t, (x, 0)) =
      D.boundaryInclusion.map x := fun t x => congrArg Prod.snd (F.map_zero_apply _)
  have htime (t : Parameter) (x : D.boundary.Point) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun r => D.boundaryFamilyFlow F (t.val, (x, r))) 0 (1 : ℝ) =
        (L t).field (D.boundaryInclusion.map x) := by
    have hd := (hlocal t _ (hU ⟨t.property, D.boundaryInclusion_mem_carrier x⟩) 0
      (show (0 : ℝ) ∈ Ioo (-δ₀) δ₀ from ⟨neg_lt_zero.mpr hδ₀, hδ₀⟩)).2.2
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun r => (F r (t.val, D.boundaryInclusion.map x)).2) 0 (1 : ℝ) = _
    rw [hd.mfderiv]
    change (1 : ℝ) • D.extension.liouvilleVector ((L t).primitive)
      (F 0 (t.val, D.boundaryInclusion.map x)).2 = _
    rw [Flow.map_zero_apply, one_smul]
    exact ((L t).field_eq_liouvilleVector _ (D.boundaryInclusion_mem_carrier x)).symm
  obtain ⟨J, δ₁, hJ, hδ₁, hinj, hdiff, _⟩ :=
    D.exists_uniform_boundaryFamily_collar L (D.boundaryFamilyFlow F) hc hzero htime
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hsub₀ : Ioo (-δ) δ ⊆ Ioo (-δ₀) δ₀ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsub₁ : (J : Set ℝ) ×ˢ ((univ : Set D.boundary.Point) ×ˢ Ioo (-δ) δ) ⊆
      (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ₁) δ₁) :=
    prod_mono_right (prod_mono_right
      (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)))
  have hi : InjOn (D.boundaryFamilyFlowWithParameter F)
      ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) := hinj.mono hsub₁
  have hd : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (D.boundaryFamilyFlowWithParameter F) ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) :=
    fun p => hdiff ⟨p.val, hsub₁ p.property⟩
  refine ⟨U, J, δ, F, hU, hJ, hδ, hF, hfst, hinvariant,
    (fun t x hx r hr => hlocal t x hx r (hsub₀ hr)), hc,
    contMDiff_fst.prodMk hc, hzero, hi, hd, ?_, ?_, ?_⟩
  · let C : TopologicalSpace.Opens (ℝ × (D.boundary.Point × ℝ)) :=
      ⟨(J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ), J.isOpen.prod (isOpen_univ.prod isOpen_Ioo)⟩
    have hl : IsLocalHomeomorph (fun p : C => D.boundaryFamilyFlowWithParameter F p.val) := by
      rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
      exact hd.isLocalHomeomorphOn.comp C.isOpenEmbedding'.isLocalHomeomorph.isLocalHomeomorphOn
        (fun p _ => p.property)
    exact hl.isOpenEmbedding_of_injective (Set.injOn_iff_injective.mp hi)
  · intro t x r hr
    let G := CollarFlow.parameterSlice F hfst t.val
    have hode (y : D.boundary.Point) :
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
          (fun s => G s (D.boundaryInclusion.map y)) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight ((L t).field (G 0 (D.boundaryInclusion.map y)))) := by
      have h := (hlocal t _ (hU ⟨t.property, D.boundaryInclusion_mem_carrier y⟩) 0
        (show (0 : ℝ) ∈ Ioo (-δ₀) δ₀ from ⟨neg_lt_zero.mpr hδ₀, hδ₀⟩)).2.2
      change HasMFDerivAt _ _ (fun s => (F s (t.val, D.boundaryInclusion.map y)).2) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((L t).field (F 0 (t.val, D.boundaryInclusion.map y)).2))
      rw [F.map_zero_apply] at h ⊢
      rw [(L t).field_eq_liouvilleVector _ (D.boundaryInclusion_mem_carrier y)]
      exact h
    have hgi : InjOn (fun p : D.boundary.Point × ℝ =>
        G p.2 (D.boundaryInclusion.map p.1)) (univ ×ˢ Ioo (-δ) δ) := by
      intro p hp q hq he
      have hh : (t.val, p) = (t.val, q) := @hi (t.val, p)
        ⟨hJ t.property, hp⟩ (t.val, q) ⟨hJ t.property, hq⟩ (Prod.ext rfl he)
      exact congrArg Prod.snd hh
    exact (L t).flow_mem_carrier_iff_nonpos_of_collar_injective G hδ hode hgi x hr
  · intro t x r hr v s
    exact D.localBoundaryFamilyFlow_primitive L F hF hδ
      (fun a y u hu => (hlocal a _
        (hU ⟨a.property, D.boundaryInclusion_mem_carrier y⟩) u (hsub₀ hu)).2.1)
      (fun a y u hu => (hlocal a _
        (hU ⟨a.property, D.boundaryInclusion_mem_carrier y⟩) u (hsub₀ hu)).2.2)
      t x hr v s

/-- The original local collar interface, retaining its exact public contract. -/
theorem exists_liouvilleFamily_localCollar {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ (U : TopologicalSpace.Opens (ℝ × D.extension.Point))
      (J : TopologicalSpace.Opens ℝ) (δ : ℝ) (F : Flow ℝ (ℝ × D.extension.Point)),
      parameterInterval ×ˢ D.carrier ⊆ (U : Set (ℝ × D.extension.Point)) ∧
      parameterInterval ⊆ (J : Set ℝ) ∧ 0 < δ ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (ℝ × D.extension.Point) => F p.1 p.2) ∧
      (∀ s p, (F s p).1 = p.1) ∧
      (∀ (t : Parameter) (x : D.extension.Point), (t.val, x) ∈ U →
        ∀ r ∈ Ioo (-δ) δ,
          D.extension.Nondegenerate
            (D.extension.exteriorDerivative ((L t).primitive)) (F r (t.val, x)).2 ∧
          D.extension.LiouvilleEquation ((L t).primitive) (F r (t.val, x)).2
            (D.extension.liouvilleVector ((L t).primitive) (F r (t.val, x)).2) ∧
          HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
            (fun u => (F u (t.val, x)).2) r
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (D.extension.liouvilleVector ((L t).primitive) (F r (t.val, x)).2))) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞
        (D.boundaryFamilyFlow F) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (D.boundaryFamilyFlowWithParameter F) ∧
      (∀ t x, D.boundaryFamilyFlow F (t, (x, 0)) = D.boundaryInclusion.map x) ∧
      InjOn (D.boundaryFamilyFlowWithParameter F)
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (D.boundaryFamilyFlowWithParameter F)
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)) ∧
      Topology.IsOpenEmbedding
        (fun p : {p : ℝ × (D.boundary.Point × ℝ) //
            p ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ) δ)} =>
          D.boundaryFamilyFlowWithParameter F p.val) ∧
      (∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
        (D.boundaryFamilyFlow F (t.val, (x, r)) ∈ D.carrier ↔ r ≤ 0)) ∧
      ∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
        ∀ (v : Model (d - 1)) (s : ℝ),
          evalOne ((L t).primitive) (D.boundaryFamilyFlow F (t.val, (x, r)))
            (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d)
              (fun q : D.boundary.Point × ℝ => D.boundaryFamilyFlow F (t.val, q))
              (x, r) (v, s)) =
            Real.exp r * evalOne (D.boundaryForm ((L t).primitive)) x v := by
  obtain ⟨U, J, δ, F, hU, hJ, hδ, hF, hfst, _, hlocal, hc, hcp,
      hzero, hinj, hdiff, hemb, hside, hprimitive⟩ :=
    D.exists_liouvilleFamily_localCollar_invariant L halpha
  exact ⟨U, J, δ, F, hU, hJ, hδ, hF, hfst, hlocal, hc, hcp,
    hzero, hinj, hdiff, hemb, hside, hprimitive⟩

end CompactDomain
end FsFltz.Geometry
