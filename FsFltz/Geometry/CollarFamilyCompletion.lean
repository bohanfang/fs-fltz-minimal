import FsFltz.Geometry.CollarFamilyEvolution

/-!
# Completed families from raw fixed-completion presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. The supplied completions are fixed. A raw
jointly smooth compact presentation family is corrected on one common
collar and fed into the existing completed-family construction. Joint
primitive regularity is derived from the corrected maps by the chain rule;
neither that regularity nor the common geometric collar square is an input.
Varying-domain and varying-completion production remains a separate problem.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a fixed smooth one-form through a jointly smooth map family
has jointly smooth coefficients, including open extensions across both
parameter endpoints. The spatial derivative is the restriction of the
actual joint derivative to the vertical tangent directions. -/
theorem isSmoothFormFamily_pullback_one_of_contMDiff
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × M.Point => f p.1 p.2))
    (α : N.Form 1) (hα : N.IsSmoothForm α) :
    M.IsSmoothFormFamily (fun t => M.pullback N (f t) α) := by
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨_, hy⟩
  let c := chartAt (Model d) a
  let b := chartAt (Model e) (f t (c.symm y))
  let W : Set (ℝ × Model d) := univ ×ˢ c.target
  let k : ℝ × Model d → N.Point := fun p => f p.1 (c.symm p.2)
  have hk : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ k W :=
    hf.comp_contMDiffOn (contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).comp
        contMDiffOn_snd (fun _ hp => hp.2)))
  let S : Set (ℝ × Model d) := W ∩ k ⁻¹' b.source
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) b.open_source
  have hpS : (t, y) ∈ S := ⟨⟨mem_univ _, hy⟩, mem_chart_source _ _⟩
  let g : ℝ × Model d → Model e := fun p => b (k p)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := f t (c.symm y))).comp
      (hk.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  have hcoeff : ContDiffOn ℝ ∞ (fun p => N.formInChart (f t (c.symm y)) α (g p)) S :=
    (hα _).comp hg (fun _ hp => b.map_source hp.2)
  let B : ℝ × Model d → Model d →L[ℝ] Model e :=
    fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ (Model d))
  have hB : ContDiffOn ℝ ∞ B S :=
    (hg.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_comp contDiffOn_const
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model e) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn hcoeff).clm_comp hB)
  have hforms : ContDiffOn ℝ ∞ (fun p =>
      (N.formInChart (f t (c.symm y)) α (g p)).compContinuousLinearMap (B p)) S := by
    convert hs using 1
    ext p vs
    change (N.formInChart (f t (c.symm y)) α (g p)) (fun i => B p (vs i)) =
      (N.formInChart (f t (c.symm y)) α (g p)) (fun _ => B p (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
  refine ⟨S, hS, hpS, hforms.congr ?_⟩
  intro p hp
  have hd := (hg.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun z : Model d => (p.1, z))
      (ContinuousLinearMap.inr ℝ ℝ (Model d)) p.2 := hasFDerivAt_prodMk_right p.1 p.2
  have hsp : fderiv ℝ (fun z => g (p.1, z)) p.2 = B p := by
    exact (hd.hasFDerivAt.comp p.2 hc).fderiv
  rw [← hsp]
  exact M.formInChart_pullback N α a (f t (c.symm y)) p.2 hp.1.2 hp.2
    ((hf.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp))

end SmoothManifold

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : ℝ → DomainPresentationEquiv D.domain E.domain)

set_option backward.isDefEq.respectTransparency false in
/-- For fixed supplied completions, a raw jointly smooth compact
presentation family produces corrected compact presentations and actual
completion presentations with jointly smooth transported primitives and
Liouville fields. The correction retains the raw boundary maps and has
jointly smooth maps and inverses. The common collar square is constructed
by `exists_collarAdapted_domainPresentationFamily` and consumed by the
existing completed-family theorem; it is not a hypothesis of this result. -/
theorem exists_smooth_completionFamily_of_domainPresentationFamily
    (hh : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × D.domain.extension.Point => (h p.1).extensionEquiv p.2)) :
    ∃ h' : ℝ → DomainPresentationEquiv D.domain E.domain,
      (∀ t, (h' t).boundaryEquiv = (h t).boundaryEquiv) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.domain.extension.Point => (h' p.1).extensionEquiv p.2) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × E.domain.extension.Point => (h' p.1).extensionEquiv.symm p.2) ∧
      ∃ p : ∀ t : Parameter, CompletionPresentationEquiv C C' (h' t.val),
        C.ambient.manifold.IsSmoothIntervalFormFamily (fun t =>
          C.ambient.manifold.pullback C'.ambient.manifold (p t).equiv C'.ambient.primitive) ∧
        C.ambient.manifold.IsSmoothIntervalVectorFieldFamily (fun t =>
          C.ambient.manifold.pullbackVectorField C'.ambient.manifold (p t).equiv C'.ambient.field) := by
  obtain ⟨h', hb, hs, hsinv, δ, hδ, hcollar⟩ :=
    C.exists_collarAdapted_domainPresentationFamily C' h hh
  have hα : D.domain.extension.IsSmoothIntervalFormFamily (fun t : Parameter =>
      D.domain.extension.pullback E.domain.extension (h' t.val).extensionEquiv E.liouville.primitive) := by
    refine ⟨fun t => D.domain.extension.pullback E.domain.extension (h' t).extensionEquiv
      E.liouville.primitive, ?_, fun _ => rfl⟩
    exact D.domain.extension.isSmoothFormFamily_pullback_one_of_contMDiff E.domain.extension
      (fun t => (h' t).extensionEquiv) hs E.liouville.primitive E.liouville.smooth_primitive
  obtain ⟨p, hp, hZ⟩ := C.exists_smooth_completionFamily_of_collar_presentations
    (fun _ => E) (fun _ => C') (fun t => h' t.val) hα δ hδ
    (fun t => hcollar t.val t.property)
  exact ⟨h', hb, hs, hsinv, p, hp, hZ⟩

end Completion
end FsFltz.Geometry
