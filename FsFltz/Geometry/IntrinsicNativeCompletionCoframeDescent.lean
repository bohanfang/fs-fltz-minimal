import FsFltz.Geometry.IntrinsicNativeCompletionCoefficientDescent
import FsFltz.Geometry.CoordinateCoframePullback

/-!
# Actual coframe and canonical-square transport by the original end inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244,
`g:chain`, lines 407–413, and `sec:lean`, lines 788–814.
The native boundary–radial chart has its original product tangent model.
Local real coframes and scalar coordinates transport through the retained
inverse of the original completed comparison. Smoothness of its actual
spatial derivative, inversion, and determinant square produce local complex
and squared canonical tensor extensions. No target grading or smoothness
of a replacement completed family is assumed.
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
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
    (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

include hdim α hp hc hb hsquareB hzero hode in
/-- Source-local coframes and scalar coordinates produce actual smooth
complex and nonzero squared canonical tensor extensions on the reference
completion. Every coframe uses the spatial derivative of the retained
original inverse, and every interval scalar is composed with that same
inverse. Nonvanishing off the interval is obtained by shrinking around the
one supplied nonzero coefficient; no geometric law there is assumed. -/
theorem exists_ambientNativeTotalEquiv_symm_endCoframeExtension
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → ℂ)
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r)
    (V : Set (ℝ × (Model k × ℝ))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ∈ V)
    (L : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n)
    (hL : ContDiffOn ℝ ∞ L V) (hLinv : ∀ z ∈ V, (L z).IsInvertible)
    (a : ℝ × (Model k × ℝ) → ℂ) (ha : ContDiffOn ℝ ∞ a V)
    (hane : a (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ≠ 0)
    (haeq : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      (p.val.2, -p.val.1) ∈ (chartAt (Model k × ℝ) (x, r)).source →
      (s.val, chartAt (Model k × ℝ) (x, r) (p.val.2, -p.val.1)) ∈ V →
        a (s.val, chartAt (Model k × ℝ) (x, r) (p.val.2, -p.val.1)) =
          f (totalCylinder (fun t p => C t p.val) (s, p))) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U ∧
        g (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) = (x, r) ∧
        (∀ z ∈ U, g z ∈ (chartAt (Model k × ℝ) (x, r)).source) ∧
        (∀ (s : Parameter) y, (s.val, y) ∈ U →
          ∃ p : Band δ (IntrinsicBoundary.Point k M),
            p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
            (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
              totalCylinder (fun t p => C t p.val) (s, p)) ∧
        let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
          chartAt (Model k × ℝ) (x, r) (g z)
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
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ) (fun y => φ (z.1, y)) z.2).inverse.comp
            (((L (z.1, φ z)).inverse.comp ((coordinateComplexStructure n).comp (L (z.1, φ z)))).comp
              (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ) (fun y => φ (z.1, y)) z.2))) ∧
        (∀ z ∈ U, a' z • coframeSquaredGenerator (B z) =
          (a' z • (coordinateSquaredVolumeTensor n).compContinuousLinearMap
            (fun _ => L (z.1, φ z))).compContinuousLinearMap
              (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
                (fun y => φ (z.1, y)) z.2)) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          a' (s.val, y) = f
            ((Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y)) := by
  obtain ⟨U₀, hU₀, hpU₀, g, hg, hgp, hginv, _, heq⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_realEndGerm_verticalDerivative
      hdim α e hp hc b hb hsquareB R hsquareA hδ C hzero hode q hqnative hqend t x r hr
  let N := Q.source.ambientManifold
  let c := chartAt (Model k × ℝ) (x, r)
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model k × ℝ) ∞ g U₀ := by
    rwa [modelWithCornersSelf_prod]
  let S := U₀ ∩ g ⁻¹' c.source
  have hS : IsOpen S := hg.continuousOn.isOpen_inter_preimage hU₀ c.open_source
  have hpS : (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ S := by
    refine ⟨hpU₀, ?_⟩
    change g (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ c.source
    rw [hgp]
    exact mem_chart_source _ _
  let φ := fun z : ℝ × N.Point => c (g z)
  have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model k × ℝ) ∞ φ S :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := (x, r))).comp
      (hgm.mono inter_subset_left) inter_subset_right
  let G := fun z : ℝ × N.Point => (z.1, φ z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ G S :=
    contMDiffOn_fst.prodMk_space hφ
  let V' := V ∩ a ⁻¹' ({0}ᶜ : Set ℂ)
  have hV' : IsOpen V' := ha.continuousOn.isOpen_inter_preimage hV
    isClosed_singleton.isOpen_compl
  let U := S ∩ G ⁻¹' V'
  have hU : IsOpen U := hG.continuousOn.isOpen_inter_preimage hS hV'
  have hpU : (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U := by
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
    have hgz : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
        (fun y => g (z.1, y)) z.2 :=
      (((hgm.contMDiffAt (hU₀.mem_nhds hz.1.1)).comp z.2
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
    have hcz := (mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) (x, r))
    have hcinv : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) c (g z)).IsInvertible := by
      apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hcz.symm_comp_deriv hz.1.2)
      have h := hcz.comp_symm_deriv (c.map_source hz.1.2)
      rwa [c.left_inv hz.1.2] at h
    have hgi : (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
        (fun y => g (z.1, y)) z.2).IsInvertible := by
      rw [modelWithCornersSelf_prod]
      exact hginv z hz.1.1
    dsimp only [B, pullbackCoordinateVerticalCoframe]
    change ((L (G z)).comp
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ) (c ∘ fun y => g (z.1, y)) z.2)).IsInvertible
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
    obtain ⟨p, hp, hpeq⟩ := heq s y hy.1.1
    rw [hpeq]
    have hp' : (p.val.2, -p.val.1) = g (s.val, y) := by
      rw [hp]
      simp only [neg_neg]
    dsimp only [a', Function.comp_apply, G, φ]
    rw [← hp']
    exact haeq s p (hp'.symm ▸ hy.1.2) (hp'.symm ▸ hy.2.1)

end FsFltz.Geometry.PairDeformation
