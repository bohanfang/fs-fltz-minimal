import FsFltz.Geometry.CollarFamilyExtension

/-!
# Smooth relative correction for fixed-completion families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The supported collar field on family parameter
times compact extension is integrated using the proved smooth evolution.
Its zero family component makes that parameter constant along every solution.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : ℝ → DomainPresentationEquiv D.domain E.domain)

set_option backward.isDefEq.respectTransparency false in
/-- Integrating one jointly supported velocity produces a jointly smooth
family of correction diffeomorphisms with the original parameter frozen.
The boundary is fixed, compact carriers are preserved, and the full
smaller collar follows the actual normalization interpolation. -/
theorem exists_familyCollar_globalSmoothEvolution
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ H : ℝ → ℝ → ℝ → E.domain.extension.SmoothEquiv E.domain.extension,
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))) 𝓘(ℝ, Model d) ∞
          (fun p : ℝ × (ℝ × (ℝ × E.domain.extension.Point)) => H p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
        (∀ s t x, H s s t x = x) ∧
        (∀ s u v t x, H u v t (H s u t x) = H s v t x) ∧
        (∀ s u t, (H s u t).symm = H u s t) ∧
        (∀ s u t (y : E.domain.boundary.Point),
          H s u t (E.domain.boundaryInclusion.map y) = E.domain.boundaryInclusion.map y) ∧
        (∀ s u t x, H s u t x ∈ E.domain.carrier ↔ x ∈ E.domain.carrier) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ univ ×ˢ Ioo (-δ) δ, ∀ s ∈ Icc (0 : ℝ) 1,
          H 0 s t (C.compactPresentationInterpolation C' (h t) (0, q)) =
            C.compactPresentationInterpolation C' (h t) (s, q) := by
  obtain ⟨ε, hε, δ, hδ, Z, K, hZ, hK, hzero, hparam, hboundary, hode⟩ :=
    C.exists_compactlySupported_familyCollarVelocity C' h hh
  have hM : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ (ℝ × E.domain.extension.Point) := inferInstance
  let : ChartedSpace (ℝ × Model d) (ℝ × E.domain.extension.Point) :=
    prodChartedSpace ℝ ℝ (Model d) E.domain.extension.Point
  rw [← modelWithCornersSelf_prod] at hM
  let : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × E.domain.extension.Point) := hM
  simp_rw +instances [← modelWithCornersSelf_prod] at hZ hparam hboundary hode
  obtain ⟨Φ, hself, hΦ, hcomp, hinv, _, _⟩ :=
    CollarFlow.exists_global_evolution (F := ℝ × Model d) hZ hK hzero
  have hΦsmooth := CollarFlow.contMDiff_joint_of_hasMFDerivAt (F := ℝ × Model d) hZ Φ hself hΦ
  have hfst : ∀ s u (p : ℝ × E.domain.extension.Point), (Φ s u p).1 = p.1 := by
    intro s u p
    have hd : ∀ v : ℝ, HasDerivAt (fun a => (Φ s a p).1) (0 : ℝ) v := by
      intro v
      have hm := (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model d)) (Φ s v p)).comp v (hΦ s p v)
      have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt
      apply hh.congr_deriv
      change (1 : ℝ) • (Z v (Φ s v p)).1 = 0
      rw [hparam, smul_zero]
    have he : (fun a => (Φ s a p).1) = fun _ => p.1 := by
      apply ODE_solution_unique_univ (t₀ := s) (v := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
        (s := fun _ => univ) (K := 0) (fun _ => (LipschitzWith.const 0).lipschitzOnWith)
      · exact fun v => ⟨hd v, mem_univ _⟩
      · exact fun v => ⟨hasDerivAt_const v _, mem_univ _⟩
      · exact congrArg Prod.fst (hself s p)
    exact congrFun he u
  let ψ := fun s u t x => (Φ s u (t, x)).2
  have hψself : ∀ s t x, ψ s s t x = x := fun s t x => congrArg Prod.snd (hself s (t, x))
  have hψcomp : ∀ s u v t x, ψ u v t (ψ s u t x) = ψ s v t x := by
    intro s u v t x
    have he := congrArg Prod.snd (hcomp s u v (t, x))
    have hf : Φ s u (t, x) = (t, ψ s u t x) := Prod.ext (hfst s u (t, x)) rfl
    rw [hf] at he
    exact he
  have hψinv : ∀ s u t x, ψ u s t (ψ s u t x) = x := by
    intro s u t x
    rw [hψcomp, hψself]
  have hψsmooth : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × (ℝ × (ℝ × E.domain.extension.Point)) => ψ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (Prod.snd : ℝ × E.domain.extension.Point → E.domain.extension.Point) := contMDiff_snd
    rw [← modelWithCornersSelf_prod] at hs
    have hf := hs.comp hΦsmooth
    rw [modelWithCornersSelf_prod (E := ℝ) (F := Model d)] at hf
    exact hf
  have hψboundary : ∀ s u t (y : E.domain.boundary.Point),
      ψ s u t (E.domain.boundaryInclusion.map y) = E.domain.boundaryInclusion.map y := by
    intro s u t y
    have hc : ∀ v, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × Model d)
        (fun _ : ℝ => (t, E.domain.boundaryInclusion.map y)) v
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z v (t, E.domain.boundaryInclusion.map y))) := by
      intro v
      rw [hboundary, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const _ _
    have he := CollarFlow.eq_of_hasMFDerivAt (F := ℝ × Model d) hZ (hΦ s (t, E.domain.boundaryInclusion.map y)) hc
      (hself s (t, E.domain.boundaryInclusion.map y))
    exact congrArg Prod.snd (congrFun he u)
  have hψcarrier : ∀ s u t x, ψ s u t x ∈ E.domain.carrier ↔ x ∈ E.domain.carrier := by
    intro s u t x
    exact E.domain.mem_carrier_iff_of_continuous_evolution (fun s u => ψ s u t)
      (fun s x => (hψsmooth.continuous.comp
        (continuous_const.prodMk (continuous_id.prodMk
          (continuous_const.prodMk continuous_const)))))
      (fun s x => hψself s t x) (fun s u x => hψinv s u t x)
      (fun s u y => hψboundary s u t y) s u x
  have hm : ∀ s u t, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (ψ s u t) := by
    intro s u t
    exact hψsmooth.comp (contMDiff_const.prodMk (contMDiff_const.prodMk
      (contMDiff_const.prodMk contMDiff_id)))
  let H := fun s u t => (show E.domain.extension.SmoothEquiv E.domain.extension from
    { toFun := ψ s u t
      invFun := ψ u s t
      left_inv := hψinv s u t
      right_inv := hψinv u s t
      contMDiff_toFun := hm s u t
      contMDiff_invFun := hm u s t })
  refine ⟨δ, hδ, H, hψsmooth, hψself, hψcomp, ?_, hψboundary, hψcarrier, ?_⟩
  · intro s u t
    ext x
    rfl
  · intro t ht q hq s hs
    have hs₀ : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have hc := CollarFlow.eqOn_of_hasMFDerivAt (F := ℝ × Model d) hZ hs₀
      (fun u _ => hΦ 0 (C.familyCompactInterpolation C' h (0, (t, q))) u)
      (fun u hu => hode u hu t ht q hq) (hself 0 _)
    have he := congrArg Prod.snd (hc (show s ∈ Ioo (-ε) (1 + ε) by constructor <;> linarith [hs.1, hs.2]))
    exact he

set_option backward.isDefEq.respectTransparency false in
/-- Joint smoothness of a family of diffeomorphisms also gives joint
smoothness of their inverses; retaining the parameter makes the inverse
function theorem apply to the actual family map. -/
theorem contMDiff_domainPresentationFamily_inverse
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × E.domain.extension.Point => (h p.1).extensionEquiv.symm p.2) := by
  let f : ℝ × D.domain.extension.Point → ℝ × E.domain.extension.Point :=
    fun p => (p.1, (h p.1).extensionEquiv p.2)
  have hf : IsLocalDiffeomorph ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ f := by
    rintro ⟨t, x⟩
    exact isLocalDiffeomorphAt_retainingParameter isOpen_univ hh.contMDiffOn (mem_univ _)
      (((h t).extensionEquiv.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv
        (by simp)).bijective
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨t, x⟩ ⟨u, y⟩ he
      have ht : t = u := congrArg Prod.fst he
      subst u
      exact Prod.ext rfl ((h t).extensionEquiv.injective (congrArg Prod.snd he))
    · rintro ⟨t, y⟩
      exact ⟨(t, (h t).extensionEquiv.symm y), Prod.ext rfl ((h t).extensionEquiv.apply_symm_apply y)⟩
  let e := hf.diffeomorphOfBijective hbij
  have he : (fun p : ℝ × E.domain.extension.Point =>
      (p.1, (h p.1).extensionEquiv.symm p.2)) = e.symm := by
    funext p
    apply e.injective
    change f (p.1, (h p.1).extensionEquiv.symm p.2) = e (e.symm p)
    exact (show f (p.1, (h p.1).extensionEquiv.symm p.2) = p from
      Prod.ext rfl ((h p.1).extensionEquiv.apply_symm_apply p.2)).trans
        (e.apply_symm_apply p).symm
  exact contMDiff_snd.comp (he ▸ e.symm.contMDiff)

set_option backward.isDefEq.respectTransparency false in
/-- A raw jointly smooth family between fixed supplied compact domains and
fixed supplied completions admits a coherent smooth collar correction.
The same positive radius works for every parameter in `[0,1]`; no collar
compatibility is imposed on the raw family. Its boundary maps are retained,
and both the corrected extension maps and their inverses are jointly smooth.
The general case of varying domains or completions is not asserted. -/
theorem exists_collarAdapted_domainPresentationFamily
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ h' : ℝ → DomainPresentationEquiv D.domain E.domain,
      (∀ t, (h' t).boundaryEquiv = (h t).boundaryEquiv) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.domain.extension.Point => (h' p.1).extensionEquiv p.2) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × E.domain.extension.Point => (h' p.1).extensionEquiv.symm p.2) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
        ∀ x ∈ D.domain.carrier, C.inclusion.map x = C.endMap q →
          C'.inclusion.map ((h' t).extensionEquiv x) =
            C'.endMap ((h' t).boundaryEquiv q.1, q.2) := by
  obtain ⟨δ₀, hδ₀, H, hs, hself, hcomp, hinv, hboundary, hcarrier, hcollar⟩ :=
    C.exists_familyCollar_globalSmoothEvolution C' h hh
  let g := fun t => (h t).extensionEquiv.trans (H 1 0 t)
  have hg : ∀ t, g t '' D.domain.carrier = E.domain.carrier := by
    intro t
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcarrier 1 0 t _).mpr (((h t).mem_carrier_iff x).mpr hx)
    · intro hy
      refine ⟨(g t).symm y, ?_, (g t).apply_symm_apply y⟩
      apply ((h t).mem_carrier_iff _).mp
      change (h t).extensionEquiv ((h t).extensionEquiv.symm ((H 1 0 t).symm y)) ∈ E.domain.carrier
      rw [(h t).extensionEquiv.apply_symm_apply]
      rw [hinv]
      exact (hcarrier 0 1 t y).mpr hy
  let h' : ℝ → DomainPresentationEquiv D.domain E.domain := fun t =>
    { extensionEquiv := g t
      carrier := hg t
      boundaryEquiv := (h t).boundaryEquiv
      boundary_square := by
        intro x
        change H 1 0 t ((h t).extensionEquiv (D.domain.boundaryInclusion.map x)) = _
        rw [(h t).boundary_square]
        exact hboundary 1 0 t ((h t).boundaryEquiv x) }
  have hh' : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h' p.1).extensionEquiv p.2) :=
    hs.comp (contMDiff_const.prodMk (contMDiff_const.prodMk
      (contMDiff_fst.prodMk hh)))
  let U := C.familyCompactInterpolationDomain C' h hh
  let f : ℝ × ((Parameter × D.domain.boundary.Point) × ℝ) →
      ℝ × (ℝ × (D.domain.boundary.Point × ℝ)) :=
    fun p => (p.1, (p.2.1.1.val, (p.2.1.2, p.2.2)))
  have hf : Continuous f := by fun_prop
  have hseam : Icc (0 : ℝ) 1 ×ˢ
      ((univ : Set (Parameter × D.domain.boundary.Point)) ×ˢ ({0} : Set ℝ)) ⊆ f ⁻¹' U := by
    rintro ⟨s, ⟨t, x⟩, r⟩ ⟨hs, _, hr⟩
    have hr0 : r = 0 := hr
    subst r
    exact C.mem_familyCompactInterpolationDomain_boundary C' h hh s t.val x
  obtain ⟨ε, hε, δ₁, hδ₁, hwidth⟩ := CollarExtension.exists_uniform_time_width
    (by simpa only [univ_prod_univ] using
      (isCompact_univ : IsCompact (univ : Set Parameter)).prod D.domain.isCompact_boundary)
    (U.isOpen.preimage hf) hseam
  let δ := min δ₀ δ₁
  refine ⟨h', fun _ => rfl, hh', contMDiff_domainPresentationFamily_inverse h' hh',
    δ, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht q hq x hx he
  have hq₀ : q ∈ univ ×ˢ Ioo (-δ₀) δ₀ :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _))
      (min_le_left _ _)) hq
  have hq₁ : q ∈ univ ×ˢ Ioo (-δ₁) δ₁ :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _))
      (min_le_right _ _)) hq
  have hdom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (s, (t, q)) ∈ U := by
    apply hwidth (a := (s, ((⟨t, ht⟩, q.1), q.2)))
    exact ⟨⟨by have := hs.1; linarith, by have := hs.2; linarith⟩,
      mem_univ ((⟨t, ht⟩ : Parameter), q.1), hq₁.2⟩
  have hdom₀ := hdom 0 ⟨le_rfl, zero_le_one⟩
  have hdom₁ := hdom 1 ⟨zero_le_one, le_rfl⟩
  have hc := congrArg (H 1 0 t) (hcollar t ht q hq₀ 1 ⟨zero_le_one, le_rfl⟩)
  rw [hcomp, C.compactPresentationInterpolation_one C' (h t) q hdom₁] at hc
  rw [hself, C.compactPresentationInterpolation_zero] at hc
  have htgt : ((h t).boundaryEquiv q.1, q.2) ∈ C'.presentationCollarSourceDomain := by
    have hm := hdom₀.2
    change C.presentationCollarInterpolation C' (h t) (0, q) ∈ C'.presentationCollarSourceDomain at hm
    rwa [C.presentationCollarInterpolation_zero] at hm
  have hsrc : q ∈ C.presentationCollarSourceDomain := ⟨x, he⟩
  have hpoint : C.presentationCollarPoint q = x :=
    C.inclusion.embedding.injective ((C.inclusionMap_presentationCollarPoint q hsrc).trans he.symm)
  change C'.inclusion.map (H 1 0 t ((h t).extensionEquiv x)) = _
  rw [← hpoint, ← hc, C'.inclusionMap_presentationCollarPoint _ htgt]

end FsFltz.Geometry.Completion
