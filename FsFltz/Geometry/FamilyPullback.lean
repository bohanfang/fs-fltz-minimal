import FsFltz.Geometry.CompletionFamily

/-!
# Pullback of simultaneous smooth map and one-form families

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. Joint regularity of transported primitives follows
from joint regularity of both the maps and the target primitives. The proof
retains genuine open extensions across parameter endpoints and does not
require a uniform time margin on noncompact manifolds.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- Simultaneously varying maps and one-forms have a jointly smooth pullback
family, with actual open extensions across the closed parameter interval.
The spatial derivative is the vertical restriction of the joint derivative. -/
theorem isSmoothFormFamily_pullback_one_of_isSmoothMapFamily
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : M.IsSmoothMapFamily N f)
    (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α) :
    M.IsSmoothFormFamily (fun t => M.pullback N (f t) (α t)) := by
  obtain ⟨R, hR, hRcover, hfR⟩ := hf
  intro a
  apply smoothNearInterval_of_local
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  let c := chartAt (Model d) a
  let b := chartAt (Model e) (f t (c.symm y))
  let q₀ : ℝ × Model d → ℝ × M.Point := fun p => (p.1, c.symm p.2)
  have hq₀ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ q₀ (univ ×ˢ c.target) :=
    contMDiffOn_fst.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).comp
        contMDiffOn_snd (fun _ hp => hp.2))
  let W : Set (ℝ × Model d) := (univ ×ˢ c.target) ∩ q₀ ⁻¹' R
  have hW : IsOpen W := hq₀.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) hR
  let k : ℝ × Model d → N.Point := fun p => f p.1 (c.symm p.2)
  have hk : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ k W :=
    hfR.comp (hq₀.mono inter_subset_left) inter_subset_right
  let S : Set (ℝ × Model d) := W ∩ k ⁻¹' b.source
  have hS : IsOpen S := hk.continuousOn.isOpen_inter_preimage
    hW b.open_source
  have hpS : (t, y) ∈ S :=
    ⟨⟨⟨mem_univ _, hy⟩, hRcover ⟨ht, mem_univ _⟩⟩, mem_chart_source _ _⟩
  let g : ℝ × Model d → Model e := fun p => b (k p)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ g S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := f t (c.symm y))).comp
      (hk.mono inter_subset_left) inter_subset_right
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  obtain ⟨A, hA, hAcover, hcoeffA⟩ := hα (f t (c.symm y))
  let q : ℝ × Model d → ℝ × Model e := fun p => (p.1, g p)
  have hq : ContDiffOn ℝ ∞ q S := contDiffOn_fst.prodMk hg
  let U := S ∩ q ⁻¹' A
  have hU : IsOpen U := hq.continuousOn.isOpen_inter_preimage hS hA
  have hpU : (t, y) ∈ U :=
    ⟨hpS, hAcover ⟨ht, b.map_source (mem_chart_source _ _)⟩⟩
  have hcoeff : ContDiffOn ℝ ∞
      (fun p => N.formInChart (f t (c.symm y)) (α p.1) (g p)) U :=
    hcoeffA.comp (hq.mono inter_subset_left) inter_subset_right
  let B : ℝ × Model d → Model d →L[ℝ] Model e :=
    fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ (Model d))
  have hB : ContDiffOn ℝ ∞ B U :=
    ((hg.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_comp contDiffOn_const).mono
      inter_subset_left
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model e) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eF.symm.contDiff.comp_contDiffOn hcoeff).clm_comp hB)
  have hforms : ContDiffOn ℝ ∞ (fun p =>
      (N.formInChart (f t (c.symm y)) (α p.1) (g p)).compContinuousLinearMap (B p)) U := by
    convert hs using 1
    ext p vs
    change (N.formInChart (f t (c.symm y)) (α p.1) (g p)) (fun i => B p (vs i)) =
      (N.formInChart (f t (c.symm y)) (α p.1) (g p)) (fun _ => B p (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
  refine ⟨U, hU, hpU, hforms.congr ?_⟩
  intro p hp
  have hd := (hg.contDiffAt (hS.mem_nhds hp.1)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun z : Model d => (p.1, z))
      (ContinuousLinearMap.inr ℝ ℝ (Model d)) p.2 := hasFDerivAt_prodMk_right p.1 p.2
  have hsp : fderiv ℝ (fun z => g (p.1, z)) p.2 = B p := by
    exact (hd.hasFDerivAt.comp p.2 hc).fderiv
  rw [← hsp]
  exact M.formInChart_pullback N (α p.1) a (f t (c.symm y)) p.2
    hp.1.1.1.2 hp.1.2
    (((hfR.contMDiffAt (hR.mem_nhds hp.1.1.2)).comp (c.symm p.2)
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))

/-- A globally jointly smooth map family is a special case of the open
extension formulation for simultaneous map and one-form pullback. -/
theorem isSmoothFormFamily_pullback_one_of_contMDiff_family
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × M.Point => f p.1 p.2))
    (α : ℝ → N.Form 1) (hα : N.IsSmoothFormFamily α) :
    M.IsSmoothFormFamily (fun t => M.pullback N (f t) (α t)) :=
  M.isSmoothFormFamily_pullback_one_of_isSmoothMapFamily N f
    ⟨univ, isOpen_univ, subset_univ _, hf.contMDiffOn⟩ α hα

/-- Pullback of interval map and one-form families is an interval one-form
family. Their chosen real extensions retain both endpoint extensions. -/
theorem isSmoothIntervalFormFamily_pullback_one
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : Parameter → M.Point → N.Point) (hf : M.IsSmoothIntervalMapFamily N f)
    (α : Parameter → N.Form 1) (hα : N.IsSmoothIntervalFormFamily α) :
    M.IsSmoothIntervalFormFamily (fun t => M.pullback N (f t) (α t)) := by
  obtain ⟨f', hf', hfeq⟩ := hf
  obtain ⟨α', hα', hαeq⟩ := hα
  refine ⟨fun t => M.pullback N (f' t) (α' t),
    M.isSmoothFormFamily_pullback_one_of_isSmoothMapFamily N f' hf' α' hα', ?_⟩
  intro t
  dsimp only
  rw [hfeq t, hαeq t]

/-- A real jointly smooth map family can transport an interval-indexed
one-form family without requiring the target forms outside the interval. -/
theorem isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : ℝ → M.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × M.Point => f p.1 p.2))
    (α : Parameter → N.Form 1) (hα : N.IsSmoothIntervalFormFamily α) :
    M.IsSmoothIntervalFormFamily (fun t : Parameter => M.pullback N (f t.val) (α t)) := by
  obtain ⟨α', hα', hαeq⟩ := hα
  refine ⟨fun t => M.pullback N (f t) (α' t),
    M.isSmoothFormFamily_pullback_one_of_contMDiff_family N f hf α' hα', ?_⟩
  intro t
  dsimp only
  rw [hαeq t]

end FsFltz.Geometry.SmoothManifold
