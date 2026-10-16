import FsFltz.Geometry.IntrinsicNativeFamilyEndpointComparison

/-!
# Joint comparison of the original finite ribbon family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 127–128 and 159–160,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–814 and 825–830.
The native finite ribbon is its whole completion. The compact coherence
square of the same pair deformation identifies its reference comparison
with one fixed completion diffeomorphism composed with the actual native
relabeling. Both directions therefore extend smoothly in the real parameter.
No independently chosen pair family or comparison regularity is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.PairDeformation
open IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Model 0) M]
  [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- The reference comparison uses the actual ribbon completion presentation
of the given deformation. -/
def nativeZeroRibbonReferenceEquiv (Q : PairDeformation 1)
    (e : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞)
    (t : Parameter) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      M Q.source.ribbonCompletion.ambient.manifold.Point ∞ :=
  (endpointCompletionDiffeomorph (Q.pair t).ribbonDomain
    (Q.pair t).ribbonCompletion (e t)).trans
      (Q.ribbonCompletionPresentation t).equiv.symm

/-- The same compact square determines every reference completion point. -/
theorem nativeZeroRibbonReferenceEquiv_eq (Q : PairDeformation 1)
    (e : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    (t : Parameter) (x : M) :
    Q.nativeZeroRibbonReferenceEquiv e t x =
      endpointCompletionDiffeomorph Q.source.ribbonDomain Q.source.ribbonCompletion
        (e parameterZero) (R t.val x) := by
  apply (Q.ribbonCompletionPresentation t).equiv.injective
  change (Q.ribbonCompletionPresentation t).equiv
      ((Q.ribbonCompletionPresentation t).equiv.symm
        ((Q.pair t).ribbonCompletion.inclusion.map (e t x).val)) = _
  rw [(Q.ribbonCompletionPresentation t).equiv.apply_symm_apply]
  change _ = (Q.ribbonCompletionPresentation t).equiv
    (Q.source.ribbonCompletion.inclusion.map (e parameterZero (R t.val x)).val)
  exact ((Q.ribbonCompletionPresentation t).compact_square _
    (e parameterZero (R t.val x)).property).trans
      (congrArg (Q.pair t).ribbonCompletion.inclusion.map (hsquare t x)) |>.symm

/-- The original finite ribbon product and its same-Q reference completion
are related by a parameter-preserving diffeomorphism. Its maps have genuine
all-real smooth extensions, including both closed-interval endpoints. -/
theorem exists_nativeZeroRibbonTotalComparison (Q : PairDeformation 1)
    (e : ∀ t, letI := (Q.pair t).ribbonDomain.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M (Q.pair t).ribbonDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) R)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val) :
    ∃ F : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
        (ℝ × M) (ℝ × Q.source.ribbonCompletion.ambient.manifold.Point) ∞,
      (∀ z, (F z).1 = z.1) ∧ (∀ z, (F.symm z).1 = z.1) ∧
      (∀ (t : Parameter) x, F (t.val, x) =
        (t.val, Q.nativeZeroRibbonReferenceEquiv e t x)) ∧
      (∀ (t : Parameter) y, F.symm (t.val, y) =
        (t.val, (Q.nativeZeroRibbonReferenceEquiv e t).symm y)) := by
  let a := endpointCompletionDiffeomorph Q.source.ribbonDomain
    Q.source.ribbonCompletion (e parameterZero)
  let F : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model 0))
      (ℝ × M) (ℝ × Q.source.ribbonCompletion.ambient.manifold.Point) ∞ :=
    { toFun := fun z => (z.1, a (R z.1 z.2))
      invFun := fun z => (z.1, (R z.1).symm (a.symm z.2))
      left_inv := by intro z; simp only [a.symm_apply_apply, Diffeomorph.symm_apply_apply]
      right_inv := by intro z; simp only [Diffeomorph.apply_symm_apply, a.apply_symm_apply]
      contMDiff_toFun := contMDiff_fst.prodMk (a.contMDiff.comp hR.1)
      contMDiff_invFun := contMDiff_fst.prodMk (hR.2.comp
        (contMDiff_fst.prodMk (a.symm.contMDiff.comp contMDiff_snd))) }
  refine ⟨F, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro t x
    exact congrArg (Prod.mk t.val) (Q.nativeZeroRibbonReferenceEquiv_eq e R hsquare t x).symm
  · intro t y
    apply F.injective
    change F (F.symm (t.val, y)) = F (t.val, (Q.nativeZeroRibbonReferenceEquiv e t).symm y)
    rw [F.apply_symm_apply]
    change (t.val, y) = (t.val, a (R t.val ((Q.nativeZeroRibbonReferenceEquiv e t).symm y)))
    rw [← Q.nativeZeroRibbonReferenceEquiv_eq e R hsquare,
      (Q.nativeZeroRibbonReferenceEquiv e t).apply_symm_apply]

end FsFltz.Geometry.PairDeformation
