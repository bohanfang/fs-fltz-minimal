import FsFltz.Geometry.FamilyPullback
import FsFltz.Geometry.RankTwoLiouville

/-!
# Smooth affine rank-two primitive families

Source: `geometric-part-fsf-proof.tex`, `eq:fs`, lines 1096–1102,
`lem:markedfamily`, lines 975–1009, and the completed family in
`lem:grading`, lines 1994–2001. The plane pullback is quadratic in an
affine map parameter. This supplies actual ambient primitive families
for the tailoring compact domains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- The plane primitive pulled back along an affine map is a quadratic
polynomial of actual one-forms. -/
theorem planePullbackForm_add_smul {f g : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ g) (s : ℝ) :
    M.planePullbackForm (f + s • g) = M.planePullbackForm f +
      s • (M.planePullbackForm (f + g) - M.planePullbackForm f - M.planePullbackForm g) +
      s ^ 2 • M.planePullbackForm g := by
  have hd (x : M.Point) : complexDifferential M (f + s • g) x =
      complexDifferential M f x + s • complexDifferential M g x :=
    ((hf.mdifferentiable (by simp) x).hasMFDerivAt.add
      ((hg.mdifferentiable (by simp) x).hasMFDerivAt.const_smul s)).mfderiv
  have ha (x : M.Point) : complexDifferential M (f + g) x =
      complexDifferential M f x + complexDifferential M g x :=
    ((hf.mdifferentiable (by simp) x).hasMFDerivAt.add
      (hg.mdifferentiable (by simp) x).hasMFDerivAt).mfderiv
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  change evalOne (M.planePullbackForm (f + s • g)) x (v 0) = _
  simp only [evalOne, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, planePullbackForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, planeLambda_apply,
    Function.comp_apply, hd, ha, add_apply, smul_apply,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- Affine complex maps and a fixed smooth primitive give an actual smooth
rank-two family, with an extension for all real parameters. -/
theorem isSmoothFormFamily_rankTwoPrimitive_affine {f g : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ g)
    {α : M.Form 1} (hα : M.IsSmoothForm α) (K : ℝ) :
    M.IsSmoothFormFamily (fun s => M.rankTwoPrimitive α (f + s • g) K) := by
  intro a
  let c := chartAt (Model d) a
  refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
    prod_mono (subset_univ _) Subset.rfl, ?_⟩
  have hs (η : M.Form 1) (hη : M.IsSmoothForm η) :
      ContDiffOn ℝ ∞ (fun p : ℝ × Model d => M.formInChart a η p.2)
        (univ ×ˢ c.target) := (hη a).comp contDiffOn_snd (fun _ hp => hp.2)
  have h0 := hs _ (M.isSmoothForm_planePullbackForm hf)
  have h1 := hs _ (M.isSmoothForm_planePullbackForm hg)
  have h01 := hs _ (M.isSmoothForm_planePullbackForm (hf.add hg))
  have hh := (hs α hα).add
    ((h0.add (contDiffOn_fst.smul ((h01.sub h0).sub h1))).add
      ((contDiffOn_fst.pow 2).smul h1) |>.const_smul K)
  apply hh.congr
  intro p _
  simp only [rankTwoPrimitive, M.planePullbackForm_add_smul hf hg,
    formInChart_add, formInChart_sub, formInChart_smul]
  rfl

end FsFltz.Geometry.SmoothManifold
