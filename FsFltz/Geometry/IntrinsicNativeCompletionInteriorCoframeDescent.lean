import FsFltz.Geometry.IntrinsicNativeCompletionInteriorInverse
import FsFltz.Geometry.CoordinateCoframePullback

/-!
# Actual coframes and canonical squares through the original interior inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244,
`g:chain`, lines 407–413, and `sec:lean`, lines 788–814.
The same native relabeling inverse and reference inclusion inverse transport
source-local coframes through their actual spatial differential. The induced
complex structures and complete squared tensors retain their literal
spatial pullback equations and every nearby interval coefficient value.
Compatibility with the completed symplectic forms and agreement between
source local representatives remain separate obligations.
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
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

include hdim hR in
/-- Source-local coframes and scalar coordinates produce actual smooth
complex and nonzero squared canonical tensor extensions on the reference
completion. Every coframe uses the spatial derivative of the retained
original inverse, and every interval scalar is composed with that same
inverse. Nonvanishing off the interval is obtained by shrinking around the
one supplied nonzero coefficient; no geometric law there is assumed. -/
theorem exists_ambientNativeTotalEquiv_symm_interiorCoframeExtension
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ)
    (t : Parameter) (u : IntrinsicInterior.Point k M)
    (V : Set (ℝ × Model (k + 1))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model (k + 1)) u u) ∈ V)
    (L : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] TangentCoordinates n)
    (hL : ContDiffOn ℝ ∞ L V) (hLinv : ∀ z ∈ V, (L z).IsInvertible)
    (a : ℝ × (Model (k + 1)) → ℂ) (ha : ContDiffOn ℝ ∞ a V)
    (hane : a (t.val, chartAt (Model (k + 1)) u u) ≠ 0)
    (haeq : ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      (s.val, chartAt (Model (k + 1)) u w) ∈ V →
        a (s.val, chartAt (Model (k + 1)) u w) =
          f (totalInterior (fun t p => C t p.val) (s, w))) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (k + 1)) ∞ g U ∧
        g (t.val, Q.ambientNativeReferenceMap e t u.val) = u ∧
        (∀ z ∈ U, g z ∈ (chartAt (Model (k + 1)) u).source) ∧
        (∀ (s : Parameter) y, (s.val, y) ∈ U →
          (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
            totalInterior (fun t p => C t p.val) (s, g (s.val, y))) ∧
        let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
          chartAt (Model (k + 1)) u (g z)
        let B := pullbackCoordinateVerticalCoframe Q.source.ambientManifold φ L
        let a' := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point => a (z.1, φ z)
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
          (fun z => coframeComplexStructure (B z)) U ∧
        IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold
          (fun z => a' z • coframeSquaredGenerator (B z)) U ∧
        (∀ z ∈ U, IsSquaredCanonicalTensor (coframeComplexStructure (B z))
          (a' z • coframeSquaredGenerator (B z))) ∧
        (∀ z ∈ U, a' z • coframeSquaredGenerator (B z) ≠ 0) ∧
        (∀ z ∈ U, coframeComplexStructure (B z) =
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) (fun y => φ (z.1, y)) z.2).inverse.comp
            (((L (z.1, φ z)).inverse.comp ((coordinateComplexStructure n).comp (L (z.1, φ z)))).comp
              (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) (fun y => φ (z.1, y)) z.2))) ∧
        (∀ z ∈ U, a' z • coframeSquaredGenerator (B z) =
          (a' z • (coordinateSquaredVolumeTensor n).compContinuousLinearMap
            (fun _ => L (z.1, φ z))).compContinuousLinearMap
              (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
                (fun y => φ (z.1, y)) z.2)) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          a' (s.val, y) = f
            ((Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y)) := by
  let u' := IntrinsicInterior.restrictDiffeomorph (R t.val) u
  obtain ⟨U₀, hU₀, hpU₀, g, hg, hgpval, hginv, heq⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_realInteriorGerm_verticalDerivative
      hdim e b R hR hsquareA hδ C q hqnative hqend t u'
  have hcenter : Q.ambientNativeInteriorReferenceMap (e parameterZero) u' =
      Q.ambientNativeReferenceMap e t u.val := by
    rw [Q.ambientNativeReferenceMap_eq_compact e R hsquareA]
    rfl
  rw [hcenter] at hpU₀ hgpval
  have hgp : g (t.val, Q.ambientNativeReferenceMap e t u.val) = u := by
    apply Subtype.ext
    exact hgpval.trans ((R t.val).symm_apply_apply u.val)
  let N := Q.source.ambientManifold
  let c := chartAt (Model (k + 1)) u
  let S := U₀ ∩ g ⁻¹' c.source
  have hS : IsOpen S := hg.continuousOn.isOpen_inter_preimage hU₀ c.open_source
  have hpS : (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ S := by
    refine ⟨hpU₀, ?_⟩
    change g (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ c.source
    rw [hgp]
    exact mem_chart_source _ _
  let φ := fun z : ℝ × N.Point => c (g z)
  have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ φ S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := u)).comp
      (hg.mono inter_subset_left) inter_subset_right
  let G := fun z : ℝ × N.Point => (z.1, φ z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × (Model (k + 1))) ∞ G S :=
    contMDiffOn_fst.prodMk_space hφ
  let V' := V ∩ a ⁻¹' ({0}ᶜ : Set ℂ)
  have hV' : IsOpen V' := ha.continuousOn.isOpen_inter_preimage hV
    isClosed_singleton.isOpen_compl
  let U := S ∩ G ⁻¹' V'
  have hU : IsOpen U := hG.continuousOn.isOpen_inter_preimage hS hV'
  have hpU : (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ U := by
    refine ⟨hpS, ?_⟩
    change (t.val, c (g _)) ∈ V'
    rw [hgp]
    exact ⟨hpV, hane⟩
  let B := pullbackCoordinateVerticalCoframe N φ L
  have hB : IsSmoothVerticalCoframeOn N B U := by
    intro u
    exact (isSmoothVerticalCoframeOn_coordinatePullback N φ hS hφ hV L hL u).mono
      (fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1⟩)
  have hBinv : ∀ z ∈ U, (B z).IsInvertible := by
    intro z hz
    have hgz : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
        (fun y => g (z.1, y)) z.2 :=
      (((hg.contMDiffAt (hU₀.mem_nhds hz.1.1)).comp z.2
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
    have hcz := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u)
    have hcinv : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) c (g z)).IsInvertible := by
      apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hcz.symm_comp_deriv hz.1.2)
      have h := hcz.comp_symm_deriv (c.map_source hz.1.2)
      rwa [c.left_inv hz.1.2] at h
    have hgi := hginv z hz.1.1
    dsimp only [B, pullbackCoordinateVerticalCoframe]
    change ((L (G z)).comp
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) (c ∘ fun y => g (z.1, y)) z.2)).IsInvertible
    rw [mfderiv_comp z.2 (hcz.mdifferentiableAt hz.1.2) hgz]
    exact (hLinv _ hz.2.1).comp (hcinv.comp hgi)
  let a' := a ∘ G
  have ha' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℂ) ∞ a' U :=
    ha.contMDiffOn.comp (hG.mono inter_subset_left) (fun z hz => hz.2.1)
  have hcanonical : ∀ z ∈ U, IsSquaredCanonicalTensor (coframeComplexStructure (B z))
      (a' z • coframeSquaredGenerator (B z)) := by
    intro z hz
    exact (squaredCanonicalSubmodule _).smul_mem _
      (coframeSquaredGenerator_canonical _ _ (coframeComplexStructure_intertwines _ (hBinv z hz)))
  refine ⟨U, hU, hpU, g, hg.mono (fun z hz => hz.1.1), hgp,
    (fun z hz => hz.1.2), (fun s y hy => heq s y hy.1.1), hB, hBinv,
    hB.complexEndomorphism hBinv, hB.squaredGenerator.smul hU ha', hcanonical, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact smul_ne_zero hz.2.2 (coframeSquaredGenerator_ne_zero _ (hBinv z hz))
  · intro z hz
    exact coframeComplexStructure_coordinateComp _ (hLinv _ hz.2.1) _
  · intro z _
    exact smul_coframeSquaredGenerator_coordinateComp _ _ _
  · intro s y hy
    rw [heq s y hy.1.1]
    exact haeq s (g (s.val, y)) hy.1.2 hy.2.1

end FsFltz.Geometry.PairDeformation
