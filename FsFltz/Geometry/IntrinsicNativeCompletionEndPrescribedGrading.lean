import FsFltz.Geometry.IntrinsicNativeCompletionCoframeDescent
import FsFltz.Geometry.CoordinateCanonicalTensor

/-!
# Prescribed canonical tensors through the original end inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
An arbitrary original boundary–radial coordinate tensor supplies its
computed inverse-coframe coefficient. The retained native inverse transports
its full canonical square and original complex field. Source canonicality
and intertwining are needed only on the parameter interval.
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
/-- The actual original end inverse transports an arbitrary prescribed
source-coordinate complex field and canonical tensor. Its scalar is computed
from that tensor; the complete tensor pullback and the complex conjugation
are conclusions. Real extensions of the source tensor and coframe may be
noncanonical outside the parameter interval. -/
theorem exists_ambientNativeTotalEquiv_symm_endPrescribedGradingExtension
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r)
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (V : Set (ℝ × (Model k × ℝ))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ∈ V)
    (L : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n)
    (hL : ContDiffOn ℝ ∞ L V) (hLinv : ∀ z ∈ V, (L z).IsInvertible)
    (K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ))
    (hLK : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      ∀ v, L (s.val, w) (K (s.val, w) v) = coordinateComplexStructure n (L (s.val, w) v))
    (T : (ℝ × (Model k × ℝ)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => (Model k × ℝ)) ℂ)
    (hT : ContDiffOn ℝ ∞ T V)
    (hcanonical : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      IsSquaredCanonicalTensor
        (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
        ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)))
    (hne : T (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ≠ 0) :
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
        let a' := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
          coordinateSquaredCoframeCoefficient (L (z.1, φ z)) (T (z.1, φ z))
        (∀ z ∈ U, (z.1, φ z) ∈ V) ∧
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
          (fun z => coframeComplexStructure (B z)) U ∧
        IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold
          (fun z => a' z • coframeSquaredGenerator (B z)) U ∧
        (∀ z ∈ U, IsSquaredCanonicalTensor (coframeComplexStructure (B z))
          (a' z • coframeSquaredGenerator (B z))) ∧
        (∀ z ∈ U, a' z • coframeSquaredGenerator (B z) ≠ 0) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          coframeComplexStructure (B (s.val, y)) =
            (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
              (fun y => φ (s.val, y)) y).inverse.comp
              ((K (s.val, φ (s.val, y))).comp
                (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
                  (fun y => φ (s.val, y)) y)) ∧
          a' (s.val, y) • coframeSquaredGenerator (B (s.val, y)) =
            (T (s.val, φ (s.val, y))).compContinuousLinearMap
              (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
                (fun y => φ (s.val, y)) y) := by
  let a := fun z => coordinateSquaredCoframeCoefficient (L z) (T z)
  have ha : ContDiffOn ℝ ∞ a V :=
    contDiffOn_coordinateSquaredCoframeCoefficient hL hLinv hT
  have hane : a (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ≠ 0 :=
    coordinateSquaredCoframeCoefficient_ne_zero P _ (hLinv _ hpV) _
      (hLK t _ hpV) _ (hcanonical t _ hpV) hne
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  have hi : Function.Injective (totalCylinder c) := by
    intro p p' h
    have ht : p.1 = p'.1 := congrArg (parameter c) h
    obtain ⟨s, p⟩ := p
    obtain ⟨s', p'⟩ := p'
    dsimp only at ht
    subst s'
    have hq := congrArg q h
    rw [hqend, hqend] at hq
    unfold CompletionPresentationEquiv.prescribedEndMap at hq
    have hc' := (Q.pair s).ambientCompletion.endMap_injective
      ((Q.ambientCompletionPresentation s).equiv.symm.injective hq)
    have hb' := (Q.ambientPresentation s).boundaryEquiv.injective (congrArg Prod.fst hc')
    have hx := (b parameterZero).injective hb'
    have hr' := neg_injective (congrArg Prod.snd hc')
    exact Prod.ext rfl (Subtype.ext (Prod.ext hr' hx))
  let f := Function.extend (totalCylinder c)
    (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
      a (p.1.val, chartAt (Model k × ℝ) (x, r) (p.2.val.2, -p.2.val.1))) (fun _ => 0)
  have haeq : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      (p.val.2, -p.val.1) ∈ (chartAt (Model k × ℝ) (x, r)).source →
      (s.val, chartAt (Model k × ℝ) (x, r) (p.val.2, -p.val.1)) ∈ V →
      a (s.val, chartAt (Model k × ℝ) (x, r) (p.val.2, -p.val.1)) =
        f (totalCylinder c (s, p)) := by
    intro s p _ _
    exact (hi.extend_apply
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
        a (p.1.val, chartAt (Model k × ℝ) (x, r) (p.2.val.2, -p.2.val.1)))
      (fun _ => 0) (s, p)).symm
  obtain ⟨U₀, hU₀, hpU₀, g, hg, hgp, hgchart, heq,
    hB, hBinv, hJ, hSq, hcan, hnz, _, hTensorPull, _⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_endCoframeExtension
      hdim α e hp hc b hb hsquareB R hsquareA hδ C hzero hode q hqnative hqend f t x r hr V hV hpV L hL hLinv
      a ha hane haeq
  let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
    chartAt (Model k × ℝ) (x, r) (g z)
  have hgm := hg
  rw [← modelWithCornersSelf_prod] at hgm
  have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, (Model k × ℝ)) ∞ φ U₀ :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := (x, r))).comp hgm hgchart
  let G := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point => (z.1, φ z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ G U₀ := contMDiffOn_fst.prodMk_space hφ
  let U := U₀ ∩ G ⁻¹' V
  have hU : IsOpen U := hG.continuousOn.isOpen_inter_preimage hU₀ hV
  have hpU : (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U := by
    refine ⟨hpU₀, ?_⟩
    change (t.val, chartAt (Model k × ℝ) (x, r) (g _)) ∈ V
    rwa [hgp]
  refine ⟨U, hU, hpU, g, hg.mono inter_subset_left, hgp,
    (fun z hz => hgchart z hz.1), (fun s y hy => heq s y hy.1),
    (fun z hz => hz.2), (fun u => (hB u).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
    (fun z hz => hBinv z hz.1),
    (fun u => (hJ u).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
    (fun u => (hSq u).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
    (fun z hz => hcan z hz.1), (fun z hz => hnz z hz.1), ?_⟩
  intro s y hy
  refine ⟨coframeComplexStructure_coordinateComp_eq _ (hLinv _ hy.2) _ _
    (hLK s _ hy.2), ?_⟩
  have hrec := coordinateSquaredCoframe_reconstruction P _ (hLinv _ hy.2) _
    (hLK s _ hy.2) _ (hcanonical s _ hy.2)
  exact (hTensorPull (s.val, y) hy.1).trans
    (congrArg (fun S => S.compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
        (fun y => φ (s.val, y)) y)) hrec.symm)

end FsFltz.Geometry.PairDeformation
