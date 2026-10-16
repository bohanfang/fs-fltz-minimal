import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCoframeDescent
import FsFltz.Geometry.CoordinateCanonicalTensor

/-!
# Prescribed canonical tensors through the original interior inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
The original source coordinate tensor supplies its computed inverse-coframe
coefficient. The retained native inverse transports the complete prescribed
complex field and canonical square. No descended generator formula is an
input, and no off-interval canonicality or compatibility is required.
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
/-- The actual original interior inverse transports an arbitrary prescribed
source-coordinate complex field and canonical tensor. Its scalar is computed
from that tensor; the complete tensor pullback and the complex conjugation
are conclusions. Real extensions of the source tensor and coframe may be
noncanonical outside the parameter interval. -/
theorem exists_ambientNativeTotalEquiv_symm_interiorPrescribedGradingExtension
    (t : Parameter) (u : IntrinsicInterior.Point k M)
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (V : Set (ℝ × Model (k + 1))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model (k + 1)) u u) ∈ V)
    (L : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] TangentCoordinates n)
    (hL : ContDiffOn ℝ ∞ L V) (hLinv : ∀ z ∈ V, (L z).IsInvertible)
    (K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1))
    (hLK : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      ∀ v, L (s.val, w) (K (s.val, w) v) = coordinateComplexStructure n (L (s.val, w) v))
    (T : (ℝ × Model (k + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (hT : ContDiffOn ℝ ∞ T V)
    (hcanonical : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      IsSquaredCanonicalTensor
        (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
        ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)))
    (hne : T (t.val, chartAt (Model (k + 1)) u u) ≠ 0) :
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
            (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
              (fun y => φ (s.val, y)) y).inverse.comp
              ((K (s.val, φ (s.val, y))).comp
                (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
                  (fun y => φ (s.val, y)) y)) ∧
          a' (s.val, y) • coframeSquaredGenerator (B (s.val, y)) =
            (T (s.val, φ (s.val, y))).compContinuousLinearMap
              (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
                (fun y => φ (s.val, y)) y) := by
  let a := fun z => coordinateSquaredCoframeCoefficient (L z) (T z)
  have ha : ContDiffOn ℝ ∞ a V :=
    contDiffOn_coordinateSquaredCoframeCoefficient hL hLinv hT
  have hane : a (t.val, chartAt (Model (k + 1)) u u) ≠ 0 :=
    coordinateSquaredCoframeCoefficient_ne_zero P _ (hLinv _ hpV) _
      (hLK t _ hpV) _ (hcanonical t _ hpV) hne
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  have hi : Function.Injective (totalInterior c) := by
    intro p p' h
    have hh := original_injective (totalCollar c) h
    exact Prod.ext (congrArg (fun z : Parameter × M => z.1) hh)
      (Subtype.ext (congrArg (fun z : Parameter × M => z.2) hh))
  let f := Function.extend (totalInterior c)
    (fun p : Parameter × IntrinsicInterior.Point k M =>
      a (p.1.val, chartAt (Model (k + 1)) u p.2)) (fun _ => 0)
  have haeq : ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      (s.val, chartAt (Model (k + 1)) u w) ∈ V →
      a (s.val, chartAt (Model (k + 1)) u w) = f (totalInterior c (s, w)) := by
    intro s w _ _
    exact (hi.extend_apply
      (fun p : Parameter × IntrinsicInterior.Point k M =>
        a (p.1.val, chartAt (Model (k + 1)) u p.2)) (fun _ => 0) (s, w)).symm
  obtain ⟨U₀, hU₀, hpU₀, g, hg, hgp, hgchart, heq,
    hB, hBinv, hJ, hSq, hcan, hnz, _, hTensorPull, _⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_interiorCoframeExtension
      hdim e b R hR hsquareA hδ C q hqnative hqend f t u V hV hpV L hL hLinv
      a ha hane haeq
  let φ := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
    chartAt (Model (k + 1)) u (g z)
  have hφ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ φ U₀ :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := u)).comp hg hgchart
  let G := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point => (z.1, φ z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, ℝ × Model (k + 1)) ∞ G U₀ := contMDiffOn_fst.prodMk_space hφ
  let U := U₀ ∩ G ⁻¹' V
  have hU : IsOpen U := hG.continuousOn.isOpen_inter_preimage hU₀ hV
  have hpU : (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ U := by
    refine ⟨hpU₀, ?_⟩
    change (t.val, chartAt (Model (k + 1)) u (g _)) ∈ V
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
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
        (fun y => φ (s.val, y)) y)) hrec.symm)

end FsFltz.Geometry.PairDeformation
