import FsFltz.Geometry.FamilyLiouvilleCollar
import FsFltz.Geometry.CollarFamilyEvolution

/-!
# Compact presentations for varying Liouville collars

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The parameter itself is the isotopy time of the constructed family collar.
Its Eulerian velocity is cut off near the compact boundary seam and then
integrated. The resulting presentations fix the boundary, preserve the
compact carrier, and identify one common two-sided collar. No completion,
collar, or flow is assumed in the varying-primitive existence theorem.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CollarFamilyExtension.EmbeddedIsotopy

variable {B F M Q HM HQ : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HM] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ B HM} {J : ModelWithCorners ℝ F HQ}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold J ∞ Q]
  {f : ℝ × M → Q} (A : CollarFamilyExtension.EmbeddedIsotopy
    (I := I) (J := J) f)

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] [IsManifold J ∞ Q] in
/-- A point stationary throughout an embedded isotopy has zero Eulerian
velocity, including outside the actual open target. Only times occurring
in the isotopy source must contain its stationary representative. -/
theorem velocity_eq_zero_of_stationary (q : M) (y : Q)
    (hstationary : ∀ s, f (s, q) = y)
    (hsource : ∀ p ∈ A.source, (p.1, q) ∈ A.source) (s : ℝ) :
    A.velocity (s, y) = 0 := by
  by_cases hp : (s, y) ∈ A.target
  · let z : A.target := ⟨(s, y), hp⟩
    have hs : (A.coordinates z).1 = s := congrArg Prod.fst (A.apply_coordinates z)
    have hq : (s, q) ∈ A.source := by
      simpa only [hs] using hsource _ (A.coordinates_mem z)
    rw [← hstationary s, A.velocity_apply (s, q) hq]
    have hd := A.smooth.contMDiffAt (A.source.isOpen.mem_nhds hq)
    have hm := mfderiv_comp (f := fun u : ℝ => (u, q)) (g := f) s
      (hd.mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    change mfderiv 𝓘(ℝ, ℝ) J (fun u : ℝ => f (u, q)) s = _ at hm
    have he : (fun u : ℝ => f (u, q)) = fun _ => y := funext hstationary
    rw [he, mfderiv_const, mfderiv_prod_left] at hm
    exact (congrArg (fun L => L (1 : ℝ)) hm).symm
  · simp only [velocity, dite_eq_right hp]

end CollarFamilyExtension.EmbeddedIsotopy

namespace CompactDomain

set_option backward.isDefEq.respectTransparency false in
/-- An actual jointly embedded boundary collar family admits a smooth
boundary-fixed evolution carrying its initial collar to every interval
collar. The all-real evolution comes from a supported auxiliary field;
the prescribed collar identity is required only on `[0,1]`. -/
theorem exists_boundaryCollar_globalSmoothEvolution {d : ℕ} (D : CompactDomain d)
    (c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point)
    (hc : ContMDiff ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞ c)
    (hzero : ∀ t x, c (t, (x, 0)) = D.boundaryInclusion.map x)
    (J : TopologicalSpace.Opens ℝ) (hJ : parameterInterval ⊆ (J : Set ℝ))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (he : Topology.IsOpenEmbedding
      (fun p : {p : ℝ × (D.boundary.Point × ℝ) //
          p ∈ (J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ₀) δ₀)} => (p.val.1, c p.val)))
    (hd : IsLocalDiffeomorphOn ((𝓘(ℝ, ℝ)).prod
        ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ (fun p => (p.1, c p))
        ((J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ₀) δ₀))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧
      ∃ H : ℝ → ℝ → D.extension.SmoothEquiv D.extension,
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
          𝓘(ℝ, Model d) ∞
          (fun p : ℝ × (ℝ × D.extension.Point) => H p.1 p.2.1 p.2.2) ∧
        (∀ s x, H s s x = x) ∧
        (∀ s t u x, H t u (H s t x) = H s u x) ∧
        (∀ s t, (H s t).symm = H t s) ∧
        (∀ s t (x : D.boundary.Point),
          H s t (D.boundaryInclusion.map x) = D.boundaryInclusion.map x) ∧
        (∀ s t x, H s t x ∈ D.carrier ↔ x ∈ D.carrier) ∧
        ∀ t ∈ parameterInterval, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
          H 0 t (c (0, q)) = c (t, q) := by
  let W : TopologicalSpace.Opens (ℝ × (D.boundary.Point × ℝ)) :=
    ⟨(J : Set ℝ) ×ˢ (univ ×ˢ Ioo (-δ₀) δ₀),
      J.isOpen.prod (isOpen_univ.prod isOpen_Ioo)⟩
  let A : CollarFamilyExtension.EmbeddedIsotopy
      (I := (𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, Model d)) c :=
    { source := W
      smooth := hc.contMDiffOn
      embedding := he
      localDiffeomorph := hd }
  have hvelocity : ∀ t (x : D.boundary.Point),
      A.velocity (t, D.boundaryInclusion.map x) = 0 := by
    intro t x
    exact A.velocity_eq_zero_of_stationary (x, 0) (D.boundaryInclusion.map x)
      (fun s => hzero s x)
      (fun p hp => ⟨hp.1, mem_univ _, neg_lt_zero.mpr hδ₀, hδ₀⟩) t
  let K₀ : Set (ℝ × D.extension.Point) :=
    parameterInterval ×ˢ (D.boundaryInclusion.map '' univ)
  have hK₀ : IsCompact K₀ := isCompact_Icc.prod
    (D.isCompact_boundary.image D.boundaryInclusion.map.contMDiff.continuous)
  have hK₀A : K₀ ⊆ A.target := by
    rintro ⟨t, y⟩ ⟨ht, x, _, rfl⟩
    refine ⟨⟨(t, (x, 0)), hJ ht, mem_univ _, neg_lt_zero.mpr hδ₀, hδ₀⟩, ?_⟩
    exact Prod.ext rfl (hzero t x)
  let : LocallyCompactSpace (ModelProd ℝ (Model d)) := by
    change LocallyCompactSpace (ℝ × Model d)
    infer_instance
  obtain ⟨χ, V, hχ, hKV, hχone, hχcompact, hχsupp⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) hK₀ A.target.isOpen hK₀A
  let U : Set (ℝ × (D.boundary.Point × ℝ)) :=
    (A.source : Set (ℝ × (D.boundary.Point × ℝ))) ∩
      (fun p => (p.1, c p)) ⁻¹' V
  have hU : IsOpen U := A.source.isOpen.inter
    ((contMDiff_fst.prodMk hc).continuous.isOpen_preimage _ V.isOpen)
  have hseam : parameterInterval ×ˢ (univ ×ˢ ({0} : Set ℝ)) ⊆ U := by
    rintro ⟨t, x, r⟩ ⟨ht, _, hr⟩
    have hr0 : r = 0 := hr
    subst r
    refine ⟨⟨hJ ht, mem_univ _, neg_lt_zero.mpr hδ₀, hδ₀⟩, ?_⟩
    change (t, c (t, (x, 0))) ∈ V
    rw [hzero]
    exact hKV ⟨ht, x, mem_univ _, rfl⟩
  obtain ⟨ε, hε, δ₁, hδ₁, hwidth⟩ :=
    CollarExtension.exists_uniform_time_width D.isCompact_boundary hU hseam
  let Z := fun t x => A.supportedVelocity χ (t, x)
  have hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × D.extension.Point => (⟨p.2, Z p.1 p.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) D.extension.Point)) :=
    A.contMDiff_supportedVelocity χ hχ hχsupp
  have hZzero : ∀ p ∉ tsupport χ, Z p.1 p.2 = 0 := by
    intro p hp
    simp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity,
      image_eq_zero_of_notMem_tsupport hp, zero_smul]
  have hZboundary : ∀ t (x : D.boundary.Point),
      Z t (D.boundaryInclusion.map x) = 0 := by
    intro t x
    simp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity,
      hvelocity, smul_zero]
  obtain ⟨Φ, hself, hΦ, hcomp, hinv, _, _⟩ :=
    CollarFlow.exists_global_evolution hZ hχcompact hZzero
  have hΦsmooth := CollarFlow.contMDiff_joint_of_hasMFDerivAt hZ Φ hself hΦ
  have hboundary : ∀ s t (x : D.boundary.Point),
      Φ s t (D.boundaryInclusion.map x) = D.boundaryInclusion.map x := by
    intro s t x
    have hcst : ∀ u, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun _ : ℝ => D.boundaryInclusion.map x) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (D.boundaryInclusion.map x))) := by
      intro u
      rw [hZboundary, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const _ _
    exact congrFun (CollarFlow.eq_of_hasMFDerivAt hZ (hΦ s _) hcst (hself s _)) t
  have hcarrier : ∀ s t x, Φ s t x ∈ D.carrier ↔ x ∈ D.carrier := by
    intro s t x
    exact D.mem_carrier_iff_of_continuous_evolution Φ
      (fun s x => hΦsmooth.continuous.comp
        (continuous_const.prodMk (continuous_id.prodMk continuous_const)))
      hself hinv hboundary s t x
  have hm : ∀ s t, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (Φ s t) := by
    intro s t
    exact hΦsmooth.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  let H := fun s t => (show D.extension.SmoothEquiv D.extension from
    { toFun := Φ s t
      invFun := Φ t s
      left_inv := hinv s t
      right_inv := hinv t s
      contMDiff_toFun := hm s t
      contMDiff_invFun := hm t s })
  let δ := min δ₀ δ₁
  refine ⟨δ, lt_min hδ₀ hδ₁, min_le_left _ _, H,
    hΦsmooth, hself, hcomp, ?_, hboundary, hcarrier, ?_⟩
  · intro s t
    ext x
    rfl
  · intro t ht q hq
    have hq₁ : q ∈ univ ×ˢ Ioo (-δ₁) δ₁ :=
      prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _))
        (min_le_right _ _)) hq
    have hode : ∀ u ∈ Ioo (-ε) (1 + ε),
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => c (s, q)) u
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (c (u, q)))) := by
      intro u hu
      have hp : (u, q) ∈ U := hwidth ⟨hu, hq₁⟩
      have hz : Z u (c (u, q)) = A.velocity (u, c (u, q)) := by
        dsimp only [Z, CollarFamilyExtension.EmbeddedIsotopy.supportedVelocity]
        rw [hχone _ hp.2, one_smul]
      rw [hz]
      exact A.hasMFDerivAt_apply u q hp.1
    have hinit : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    exact CollarFlow.eqOn_of_hasMFDerivAt hZ hinit
      (fun u _ => hΦ 0 (c (0, q)) u) hode (hself 0 _)
      (show t ∈ Ioo (-ε) (1 + ε) by constructor <;> linarith [ht.1, ht.2])

set_option backward.isDefEq.respectTransparency false in
/-- Smooth varying Liouville primitives on a fixed compact domain produce
actual common compact presentations. The same generated collar is used in
the radial ODE, domain-side law, and presentation square. The original
Liouville ODE is needed only on its negative collar inside the compact
domain, where the supplied field equals the canonical Liouville vector.
No completion or collar compatibility is a hypothesis. -/
theorem exists_liouvilleFamily_collarPresentation {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (hα : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ c : ℝ × (D.boundary.Point × ℝ) → D.extension.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))) 𝓘(ℝ, Model d) ∞ c ∧
        (∀ t x, c (t, (x, 0)) = D.boundaryInclusion.map x) ∧
        (∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
          (c (t.val, (x, r)) ∈ D.carrier ↔ r ≤ 0)) ∧
        (∀ (t : Parameter) (x : D.boundary.Point) (r : ℝ), r ∈ Ioo (-δ) δ →
          r ≤ 0 → HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
            (fun u => c (t.val, (x, u))) r
            ((1 : ℝ →L[ℝ] ℝ).smulRight ((L t).field (c (t.val, (x, r)))))) ∧
        ∃ h : ℝ → DomainPresentationEquiv D D,
          (∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞) ∧
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
            (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2) ∧
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
            (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv.symm p.2) ∧
          (∀ x, (h 0).extensionEquiv x = x) ∧
          ∀ t ∈ parameterInterval, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
            (h t).extensionEquiv (c (0, q)) = c (t, q) := by
  obtain ⟨U, J, δ₀, F, hU, hJ, hδ₀, hF, hfst, hlocal, hc, hcp,
      hzero, hinj, hdiff, hemb, hside, hprimitive⟩ :=
    D.exists_liouvilleFamily_localCollar L hα
  obtain ⟨δ, hδ, hδle, H, hH, hself, hcomp, hinv, hboundary, hcarrier, hcollar⟩ :=
    D.exists_boundaryCollar_globalSmoothEvolution (D.boundaryFamilyFlow F) hc hzero
      J hJ δ₀ hδ₀ hemb hdiff
  let h : ℝ → DomainPresentationEquiv D D := fun t =>
    { extensionEquiv := H 0 t
      carrier := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (hcarrier 0 t x).mpr hx
        · intro hy
          refine ⟨(H 0 t).symm y, ?_, (H 0 t).apply_symm_apply y⟩
          rw [hinv]
          exact (hcarrier t 0 y).mpr hy
      boundaryEquiv := Diffeomorph.refl _ _ ∞
      boundary_square := hboundary 0 t }
  have hsub : Ioo (-δ) δ ⊆ Ioo (-δ₀) δ₀ :=
    Ioo_subset_Ioo (neg_le_neg hδle) hδle
  refine ⟨δ, hδ, D.boundaryFamilyFlow F, hc, hzero,
    (fun t x r hr => hside t x r (hsub hr)), ?_, h,
    (fun _ => rfl), ?_, ?_, hself 0, hcollar⟩
  · intro t x r hr hnonpos
    have hx : D.boundaryFamilyFlow F (t.val, (x, r)) ∈ D.carrier :=
      (hside t x r (hsub hr)).mpr hnonpos
    have hode := (hlocal t (D.boundaryInclusion.map x)
      (hU ⟨t.property, D.boundaryInclusion_mem_carrier x⟩) r (hsub hr)).2.2
    change HasMFDerivAt _ _ (fun u => D.boundaryFamilyFlow F (t.val, (x, u))) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (D.extension.liouvilleVector ((L t).primitive)
          (D.boundaryFamilyFlow F (t.val, (x, r))))) at hode
    rw [← (L t).field_eq_liouvilleVector _ hx] at hode
    exact hode
  · exact hH.comp (contMDiff_const.prodMk (contMDiff_fst.prodMk contMDiff_snd))
  · change ContMDiff _ _ ∞
      (fun p : ℝ × D.extension.Point => (H 0 p.1).symm p.2)
    simp_rw [hinv]
    exact hH.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd))

end CompactDomain
end FsFltz.Geometry
