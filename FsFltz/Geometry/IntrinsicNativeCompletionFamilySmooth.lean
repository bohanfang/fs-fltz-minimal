import FsFltz.Geometry.IntrinsicNativeCompletionFamilySeam
import FsFltz.Geometry.IntrinsicCompletionFamilyMap

/-!
# Smoothness of the natural map on the original family atlas

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169;
and `sec:lean`, lines 788–793 and 805–814. Native compact coherence gives
the smooth formula on the interior of the original total completion.
The real cylinder extension gives a smooth formula across the seam and
on the whole outward end. The actual mixed germs give smoothness on the
remaining inward cylinder, with the original collar width unchanged.

The conclusion concerns the same prescribed quotient map. A smooth inverse
and transport of vertical primitives are separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The exact native and full-cylinder formulas force joint smoothness of
the same map on the original total atlas. There is no reconstructed collar,
no reduction of its width and no assumed completion-map smoothness. -/
theorem contMDiff_ambientNativeTotalMap
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
    (hzero : ∀ t x, C t (0, x) = x.val)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hmix : HasRealMixedGerms (δ := δ) C)
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
    (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
    (hqnative : ∀ t x,
      q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
    (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      q (totalCylinder (fun t p => C t p.val) (t, p)) =
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ q := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let f₀ : M → (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point :=
    fun x => (Q.pair parameterZero).ambientCompletion.inclusion.map (e parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ f₀ :=
    (Q.pair parameterZero).ambientCompletion.inclusion.map.contMDiff.comp
      ((Q.pair parameterZero).ambientDomain.domain.contMDiff_subtype_val.comp (e parameterZero).contMDiff)
  have hnative : ContMDiff (familyModel (k + 1)) (𝓡∂ (k + 1)) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => R p.1.val p.2.val) :=
    hR.1.comp (contMDiff_subtypeVal_Icc.prodMap IntrinsicInterior.contMDiff_val)
  have hi : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (q ∘ totalInterior c) := by
    convert hf₀.comp hnative using 1
    funext p
    exact (hqnative p.1 p.2.val).trans
      (Q.ambientNativeReferenceMap_eq_compact e R hsquareA p.1 p.2.val)
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquareB C hode hzero
  have hinput : ContMDiff (familyModel (k + 1))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
        (p.1.val, (p.2.val.2, -p.2.val.1))) :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val δ).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val δ).comp contMDiff_snd)).neg)
  have hstrip : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (q ∘ totalCylinder c) {p | p.2.val.1 < -a} := by
    apply (hβ.comp hinput).contMDiffOn.congr
    intro p hp'
    exact (hqend p.1 p.2).trans (heβ p.1 p.2.val.2 (-p.2.val.1)
      (by change p.2.val.1 < -a at hp'; linarith)).symm
  exact contMDiff_totalFamily_of_end_strip hδ C hboundary hzero hjoint hmix q
    (neg_pos.mpr ha) hi hstrip

end FsFltz.Geometry.PairDeformation
