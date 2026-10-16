import FsFltz.Geometry.FamilyLiouvillePresentation
import FsFltz.Geometry.CompletionLocalization

/-!
# Common flow collars and their compact presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and `sec:lean`,
lines 788–814. One invariant parameter-preserving family flow supplies
actual collars in each primitive's symplectic neighborhood. The compact
presentation is constructed using those same collar maps. No completion
or comparison chain is supplied or asserted here.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
set_option backward.isDefEq.respectTransparency false

private theorem spatial_mfderiv_bijective
    {M N B E HM HN : Type}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HM] [TopologicalSpace HN]
    {I : ModelWithCorners ℝ B HM} {J : ModelWithCorners ℝ E HN}
    [TopologicalSpace M] [ChartedSpace HM M]
    [TopologicalSpace N] [ChartedSpace HN N]
    (f : ℝ × M → N) (t : ℝ) (x : M)
    (hf : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod I) J f (t, x))
    (hb : Function.Bijective (mfderiv ((𝓘(ℝ, ℝ)).prod I)
      ((𝓘(ℝ, ℝ)).prod J) (fun p => (p.1, f p)) (t, x))) :
    Function.Bijective (mfderiv I J (fun y => f (t, y)) x) := by
  let A := mfderiv ((𝓘(ℝ, ℝ)).prod I) J f (t, x)
  have he (v : B) : A (0, v) = mfderiv I J (fun y => f (t, y)) x v := by
    have hm := mfderiv_comp (f := fun y : M => (t, y)) (g := f) x hf
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at hm
    exact (congrArg (fun K => K v) hm).symm
  rw [mfderiv_prodMk mdifferentiableAt_fst hf, mfderiv_fst] at hb
  constructor
  · intro v w h
    have hp : ((0 : ℝ), v) = (0, w) := @hb.1 (0, v) (0, w) (Prod.ext rfl (by
      change A (0, v) = A (0, w)
      rw [he, he, h]))
    exact congrArg Prod.snd hp
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := hb.2 (0, z)
    have ha : a = 0 := congrArg Prod.fst hab
    subst a
    exact ⟨b, (he b).symm.trans (congrArg Prod.snd hab)⟩

namespace LiouvilleDomain

/-- On the open nondegeneracy locus, restriction has the same canonical
contraction field in the native model tangent fibers. -/
theorem neighborhood_field_eq_canonical {d : ℕ} (D : LiouvilleDomain d)
    (x : D.neighborhoodDomain.extension.Point) :
    D.neighborhoodStructure.field x =
      D.domain.extension.liouvilleVector D.liouville.primitive x.val := by
  apply (D.domain.extension.liouvilleVector_eq D.liouville.primitive x.val x.property ?_).symm
  intro v
  have hc := D.neighborhood_contraction x v
  unfold evalTwo evalOne at hc ⊢
  erw [D.domain.extension.exteriorDerivative_restrict D.symplecticNeighborhood
    D.liouville.primitive D.liouville.smooth_primitive x] at hc
  rw [D.neighborhood_primitive] at hc
  exact hc

end LiouvilleDomain

namespace CompactDomain

/-- Smooth interval primitives produce actual collars of one common width,
and a jointly smooth compact presentation carrying the initial collar to
each interval collar. Every collar uses the same generated family flow. -/
theorem exists_liouvilleFamily_flowCollarPresentation {d : ℕ} (D : CompactDomain d)
    (L : Parameter → LiouvilleStructure D)
    (halpha : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d),
        (∀ t, (A t).width = δ) ∧
        ∃ h : ℝ → DomainPresentationEquiv D D,
          (∀ t, (h t).boundaryEquiv = Diffeomorph.refl _ _ ∞) ∧
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
            (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv p.2) ∧
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
            (fun p : ℝ × D.extension.Point => (h p.1).extensionEquiv.symm p.2) ∧
          (∀ x, (h 0).extensionEquiv x = x) ∧
          ∀ (t : Parameter) q, q ∈ univ ×ˢ Ioo (-δ) δ →
            (h t.val).extensionEquiv ((A parameterZero).map q).val = ((A t).map q).val := by
  obtain ⟨U, J, δ₀, F, hU, hJ, hδ₀, hF, hfst, hinvariant,
      hlocal, hc, _, hzero, hinj, hdiff, hemb, hside, _⟩ :=
    D.exists_liouvilleFamily_localCollar_invariant L halpha
  obtain ⟨δ, hδ, hδle, H, hH, hself, _, hinv, hboundary, hcarrier, hcollar⟩ :=
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
  let G (t : Parameter) : Flow ℝ (⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.extension.Point :=
    (CollarFlow.parameterSlice F hfst t.val).restrict
      (fun s x hx => (hinvariant t s x).mp hx)
  have hG (t : Parameter) : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model d) ∞
      (fun p : ℝ × (⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.extension.Point =>
        G t p.1 p.2) := by
    apply (ContMDiff.subtypeVal_comp_iff
      (⟨D, L t⟩ : LiouvilleDomain d).symplecticNeighborhood _).mp
    exact (contMDiff_snd.comp hF).comp
      (contMDiff_fst.prodMk (contMDiff_const.prodMk
        (contMDiff_subtype_val.comp contMDiff_snd)))
  have hode (t : Parameter) (x : D.boundary.Point) (r : ℝ)
      (hr : r ∈ Ioo (-δ) δ) :
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun s => G t s ((⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.boundaryInclusion.map x)) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          ((⟨D, L t⟩ : LiouvilleDomain d).neighborhoodStructure.field
            (G t r ((⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.boundaryInclusion.map x)))) := by
    let Dt : LiouvilleDomain d := ⟨D, L t⟩
    let γ := fun s => G t s (Dt.neighborhoodDomain.boundaryInclusion.map x)
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ r :=
      ((hG t).comp (contMDiff_id.prodMk contMDiff_const) r).mdifferentiableAt (by simp)
    have hd := (hlocal t (D.boundaryInclusion.map x)
      (hU ⟨t.property, D.boundaryInclusion_mem_carrier x⟩) r (hsub hr)).2.2
    have hm := mfderiv_comp (f := γ)
      (g := (Subtype.val : Dt.symplecticNeighborhood → D.extension.Point)) r
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)) hγ
    erw [D.extension.mfderiv_restrict_val Dt.symplecticNeighborhood (γ r)] at hm
    simp only [ContinuousLinearMap.id_comp] at hm
    apply hγ.hasMFDerivAt.congr_mfderiv
    rw [← hm]
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
      (fun s => (F s (t.val, D.boundaryInclusion.map x)).2) r = _
    rw [hd.mfderiv]
    rw [Dt.neighborhood_field_eq_canonical]
    rfl
  have hGi (t : Parameter) : InjOn
      (fun p : D.boundary.Point × ℝ =>
        G t p.2 ((⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.boundaryInclusion.map p.1))
      (univ ×ˢ Ioo (-δ) δ) := by
    intro p hp q hq he
    have he' := congrArg Subtype.val he
    have hpair : (t.val, p) = (t.val, q) := @hinj (t.val, p)
      ⟨hJ t.property, hp.1, hsub hp.2⟩ (t.val, q) ⟨hJ t.property, hq.1, hsub hq.2⟩
      (Prod.ext rfl he')
    exact congrArg Prod.snd hpair
  have hGd (t : Parameter) : IsLocalDiffeomorphOn
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model d) ∞
      (fun p : D.boundary.Point × ℝ =>
        G t p.2 ((⟨D, L t⟩ : LiouvilleDomain d).neighborhoodDomain.boundaryInclusion.map p.1))
      (univ ×ˢ Ioo (-δ) δ) := by
    intro p
    let Dt : LiouvilleDomain d := ⟨D, L t⟩
    let g : D.boundary.Point × ℝ → Dt.neighborhoodDomain.extension.Point :=
      fun q => G t q.2 (Dt.neighborhoodDomain.boundaryInclusion.map q.1)
    have hg : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Model d) ∞ g :=
      (hG t).comp (contMDiff_snd.prodMk
        (Dt.neighborhoodDomain.boundaryInclusion.map.contMDiff.comp contMDiff_fst))
    have hdtotal := hdiff ⟨(t.val, p.val), hJ t.property, p.property.1, hsub p.property.2⟩
    have hb := spatial_mfderiv_bijective (D.boundaryFamilyFlow F) t.val p.val
      (hc.mdifferentiableAt (by simp))
      (hdtotal.mfderivToContinuousLinearEquiv (by simp)).bijective
    have hm := mfderiv_comp (f := g)
      (g := (Subtype.val : Dt.symplecticNeighborhood → D.extension.Point)) p.val
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))
    erw [D.extension.mfderiv_restrict_val Dt.symplecticNeighborhood (g p.val)] at hm
    simp only [ContinuousLinearMap.id_comp] at hm
    change Function.Bijective (mfderiv _ _ (Subtype.val ∘ g) p.val) at hb
    rw [hm] at hb
    have hprod : IsManifold ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
        (D.boundary.Point × ℝ) := inferInstance
    let : ChartedSpace (Model (d - 1) × ℝ) (D.boundary.Point × ℝ) :=
      prodChartedSpace (Model (d - 1)) D.boundary.Point ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hg hb hprod ⊢
    exact isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
      isOpen_univ hg.contMDiffOn (mem_univ _) hb
  let A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain d) :=
    fun t =>
      { width := δ
        positive_width := hδ
        flow := G t
        smooth_action := hG t
        solves := hode t
        injective := hGi t
        localDiffeomorph := hGd t
        side := fun x r hr => hside t x r (hsub hr)
        primitive := fun x r hr v s =>
          (⟨D, L t⟩ : LiouvilleDomain d).localBoundaryFlow_primitive
            (G t) (hG t) hδ (hode t) x hr v s |>.trans (by
              rw [(⟨D, L t⟩ : LiouvilleDomain d).neighborhood_boundaryForm]) }
  refine ⟨δ, hδ, A, fun _ => rfl, h, fun _ => rfl, ?_, ?_, hself 0, ?_⟩
  · exact hH.comp (contMDiff_const.prodMk (contMDiff_fst.prodMk contMDiff_snd))
  · change ContMDiff _ _ ∞ (fun p : ℝ × D.extension.Point => (H 0 p.1).symm p.2)
    simp_rw [hinv]
    exact hH.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd))
  · intro t q hq
    exact hcollar t.val t.property q hq

end CompactDomain
end FsFltz.Geometry
