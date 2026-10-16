import FsFltz.Geometry.RankTwoPrimitiveFamily
import FsFltz.Geometry.PotentialAmbientRoundedMotion

/-!
# Joint primitives on the prescribed holomorphic path

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and assembly, lines 2148–2158. Both the potential and polynomial vary at
the same parameter. The consumer is the actual transported compact pair.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.SmoothManifold

/-- Jointly smooth complex maps have jointly smooth actual plane pullbacks. -/
theorem isSmoothFormFamily_planePullbackForm {d : ℕ} (M : SmoothManifold d)
    (f : ℝ → M.Point → ℂ)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × M.Point => f p.1 p.2)) :
    M.IsSmoothFormFamily (fun t => M.planePullbackForm (f t)) := by
  intro a
  let c := chartAt (Model d) a
  let S := (univ : Set ℝ) ×ˢ c.target
  let g : ℝ × Model d → ℂ := fun p => f p.1 (c.symm p.2)
  have hS : IsOpen S := isOpen_univ.prod c.open_target
  have hgm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℂ) ∞ g S :=
    (hf.contMDiffOn (s := univ)).comp
      (contMDiffOn_fst.prodMk
        ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).comp
          contMDiffOn_snd (fun _ hp => hp.2))) (fun _ _ => mem_univ _)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgm
  have hg : ContDiffOn ℝ ∞ g S := hgm.contDiffOn
  let B : ℝ × Model d → Model d →L[ℝ] ℂ :=
    fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ (Model d))
  have hB : ContDiffOn ℝ ∞ B S :=
    (hg.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_comp contDiffOn_const
  let eC := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have hs := eE.contDiff.comp_contDiffOn
    ((eC.symm.contDiff.comp_contDiffOn (contDiff_planeLambda.comp_contDiffOn hg)).clm_comp hB)
  have hforms : ContDiffOn ℝ ∞
      (fun p => (planeLambda (g p)).compContinuousLinearMap (B p)) S := by
    convert hs using 1
    ext p vs
    change planeLambda (g p) (fun i => B p (vs i)) =
      planeLambda (g p) (fun _ => B p (vs 0))
    congr 1
    funext i
    rw [Fin.eq_zero i]
  refine ⟨S, hS, prod_mono (subset_univ _) Subset.rfl, hforms.congr ?_⟩
  intro p hp
  have hd := (hg.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun z : Model d => (p.1, z))
      (ContinuousLinearMap.inr ℝ ℝ (Model d)) p.2 := hasFDerivAt_prodMk_right p.1 p.2
  have hsp : fderiv ℝ (fun z => g (p.1, z)) p.2 = B p := by
    exact (hd.hasFDerivAt.comp p.2 hc).fderiv
  rw [← hsp]
  exact M.formInChart_planePullbackForm
    (hf.comp (contMDiff_const.prodMk contMDiff_id)) a p.2 hp.2

end FsFltz.Geometry.SmoothManifold

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The actual potential primitive is affine under affine interpolation. -/
theorem lambdaPotentialForm_potentialPath {φ₀ φ : RealSpace n → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    lambdaPotentialForm (potentialPath φ₀ φ t) =
      (1 - t) • lambdaPotentialForm φ₀ + t • lambdaPotentialForm φ := by
  have hg (u : RealSpace n) : coordinateGradient (potentialPath φ₀ φ t) u =
      (1 - t) • coordinateGradient φ₀ u + t • coordinateGradient φ u := by
    funext j
    have hd := (((hφ₀.differentiable (by simp) u).hasFDerivAt.const_mul (1-t)).add
      ((hφ.differentiable (by simp) u).hasFDerivAt.const_mul t)).fderiv
    change (fderiv ℝ (fun x => (1-t)*φ₀ x + t*φ x) u) (Pi.single j 1) = _
    exact congrArg (fun L : RealSpace n →L[ℝ] ℝ => L (Pi.single j 1)) hd
  funext y
  change LGSpace n at y
  ext vs
  simp [lambdaPotentialForm, covectorForm, hg, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]


/-- Joint regularity of the actual potential primitive, including real
extensions across both interval endpoints. -/
theorem isSmoothFormFamily_lambdaPotentialForm_potentialPath
    {φ₀ φ : RealSpace n → ℝ} (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) :
    (lgManifold n).IsSmoothFormFamily
      (fun t => lambdaPotentialForm (potentialPath φ₀ φ t)) := by
  intro a
  let c := chartAt (Model (2 * n)) a
  have hs (η : (lgManifold n).Form 1) (hη : (lgManifold n).IsSmoothForm η) :
      ContDiffOn ℝ ∞ (fun p : ℝ × Model (2 * n) =>
        (lgManifold n).formInChart a η p.2) (univ ×ˢ c.target) :=
    (hη a).comp contDiffOn_snd (fun _ hp => hp.2)
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  have h := (((contDiffOn_const (c := (1 : ℝ))).sub contDiffOn_fst).smul
    (hs _ (isSmoothForm_lambdaPotentialForm hφ₀))).add
    (contDiffOn_fst.smul (hs _ (isSmoothForm_lambdaPotentialForm hφ)))
  apply h.congr
  intro p _
  simp only [lambdaPotentialForm_potentialPath hφ₀ hφ,
    SmoothManifold.formInChart_add, SmoothManifold.formInChart_smul]
  rfl

/-- The prescribed simultaneous coefficient/potential path has a jointly
smooth actual rank-two primitive for every fixed real coefficient. -/
theorem isSmoothFormFamily_coefficientPath_potentialPath_primitive
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : ℝ) :
    (lgManifold n).IsSmoothFormFamily (fun t =>
      (lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
        (W (I.alongCoefficientPath t)) K) := by
  have hpot := isSmoothFormFamily_lambdaPotentialForm_potentialPath
    (contDiff_realSquaredNorm.div_const 2) hφ
  have hplane := (lgManifold n).isSmoothFormFamily_planePullbackForm
    (fun t => W (I.alongCoefficientPath t)) (contMDiff_coefficientPath_W_native_joint I)
  intro a
  obtain ⟨U, hU, hUc, hUf⟩ := hpot a
  obtain ⟨V, hV, hVc, hVf⟩ := hplane a
  refine ⟨U ∩ V, hU.inter hV, subset_inter hUc hVc, ?_⟩
  have h := (hUf.mono inter_subset_left).add
    ((hVf.mono inter_subset_right).const_smul K)
  apply h.congr
  intro p _
  simp only [SmoothManifold.rankTwoPrimitive, SmoothManifold.formInChart_add,
    SmoothManifold.formInChart_smul]
  rfl

end FsFltz
