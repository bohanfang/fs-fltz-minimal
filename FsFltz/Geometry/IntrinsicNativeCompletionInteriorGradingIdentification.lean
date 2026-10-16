import FsFltz.Geometry.IntrinsicNativeCompletionInteriorGradingDerivative
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorPrescribedGrading
import FsFltz.Geometry.CoordinateComplexCoframe

/-!
# The prescribed original slice grading in the retained interior inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
Source coordinate representatives are compared with the prescribed original
native slice data through the actual interior inclusion and chart tangent
maps. The produced real inverse has that exact slice differential on the
interval. Consequently the coframe extension is the prescribed original
slice pullback, including the complete canonical-square tensor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- A source coordinate change cancels from the actual complex pullback.
The spatial map may have a different tangent model. -/
theorem conjugatedComplexStructure_coordinateCancel {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : F →L[ℝ] G) (hH : H.IsInvertible) (D : E →L[ℝ] F) (J : F →L[ℝ] F) :
    (H.comp D).inverse.comp
      ((H.comp (J.comp H.inverse)).comp (H.comp D)) = D.inverse.comp (J.comp D) := by
  rw [hH.inverse_comp_of_left]
  ext v
  simp only [ContinuousLinearMap.comp_apply, hH.inverse_apply_self]

/-- The same source coordinate change cancels from the entire tensor
pullback, including every tangent slot. -/
theorem squaredTensor_coordinateCancel {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : F →L[ℝ] G) (hH : H.IsInvertible) (D : E →L[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ) :
    (T.compContinuousLinearMap (fun _ => H.inverse)).compContinuousLinearMap
      (fun _ => H.comp D) = T.compContinuousLinearMap (fun _ => D) := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, hH.inverse_apply_self]

end FsFltz.Geometry

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
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
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
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Original native fields represented in the retained interior chart
pull back to the coframe extension through the original slice inverse.
Both matching equations are derived from source coordinate expressions and
the proved differential of the actual native inverse. -/
theorem ambientNativeSliceDiffeomorph_symm_interiorCoframe_matches
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ g U)
    (heq : ∀ (s : Parameter) y, (s.val, y) ∈ U →
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
        totalInterior (fun t p => C t p.val) (s, g (s.val, y)))
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val, y) ∈ U) (u : IntrinsicInterior.Point k M)
    (hchart : g (s.val, y) ∈ (chartAt (Model (k + 1)) u).source)
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (L : Model (k + 1) →L[ℝ] TangentCoordinates n) (hL : L.IsInvertible)
    (Jnative : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      Model (k + 1) →L[ℝ] Model (k + 1))
    (Tnative : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (K : Model (k + 1) →L[ℝ] Model (k + 1))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (hLK : ∀ v, L (K v) = coordinateComplexStructure n (L v))
    (hcan : IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp (K.comp P.toContinuousLinearMap))
      (T.compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    let w := g (s.val, y)
    let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
    let H := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (chartAt (Model (k + 1)) u) w).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y
    let A := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => chartAt (Model (k + 1)) u (g (s.val, z))) y
    K = H.comp ((Jnative (j w)).comp H.inverse) →
    T = (Tnative (j w)).compContinuousLinearMap (fun _ => H.inverse) →
    coframeComplexStructure (L.comp A) =
      D.inverse.comp ((Jnative
        ((Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
          hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)).comp D) ∧
    coordinateSquaredCoframeCoefficient L T • coframeSquaredGenerator (L.comp A) =
      (Tnative
        ((Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
          hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)).compContinuousLinearMap
        (fun _ => D) := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  dsimp only
  intro hK hT
  let w := g (s.val, y)
  let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
  let H : Model (k + 1) →L[ℝ] Model (k + 1) :=
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (chartAt (Model (k + 1)) u) w).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
  have hci : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (chartAt (Model (k + 1)) u) w).IsInvertible := by
    have hc := mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hc.symm_comp_deriv hchart)
    have h := hc.comp_symm_deriv ((chartAt (Model (k + 1)) u).map_source hchart)
    rwa [(chartAt (Model (k + 1)) u).left_inv hchart] at h
  have hHi : H.IsInvertible := hci.comp
    (isInvertible_mfderiv_completionInterior hδ (C s) (hemb s) (hC s)
      (hboundary s) (hinv s) (hzero s) w).inverse
  have hA := Q.ambientNativeSliceDiffeomorph_symm_interiorChart_mfderiv hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    U hU g hg heq s y hy u hchart
  have hpoint := Q.ambientNativeSliceDiffeomorph_symm_eq_interior_of_total hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    s y w (heq s y hy)
  rw [hpoint]
  refine ⟨?_, ?_⟩
  · rw [coframeComplexStructure_coordinateComp_eq L hL _ K hLK, hA, hK]
    simpa only [H, j, w, ContinuousLinearMap.comp_assoc] using
      conjugatedComplexStructure_coordinateCancel (E := Model (2 * n)) H hHi
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
          (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
            hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)
        (Jnative (j w))
  · have hrec := coordinateSquaredCoframe_reconstruction P L hL K hLK T hcan
    rw [smul_coframeSquaredGenerator_coordinateComp, ← hrec, hA, hT]
    simpa only [H, j, w, ContinuousLinearMap.comp_assoc] using
      squaredTensor_coordinateCancel (E := Model (2 * n)) H hHi
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
          (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
            hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)
        (Tnative (j w))

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- An arbitrary original native grading with genuine smooth source
coordinate extensions produces local grading extensions on the reference
completion. The source coframe is constructed from the prescribed complex
field; the scalar is extracted from the prescribed tensor. The same retained
inverse supplies both regularity and the exact original slice matching. -/
theorem exists_ambientNativeSlice_interiorPrescribedGradingExtension
    (t : Parameter) (u : IntrinsicInterior.Point k M)
    (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (V : Set (ℝ × Model (k + 1))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model (k + 1)) u u) ∈ V)
    (K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1))
    (hK : ContDiffOn ℝ ∞ K V)
    (hsq : ∀ (s : Parameter) w, (s.val, w) ∈ V → ∀ v, K (s.val, w) (K (s.val, w) v) = -v)
    (T : (ℝ × Model (k + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (hT : ContDiffOn ℝ ∞ T V)
    (hcanonical : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      IsSquaredCanonicalTensor
        (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
        ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)))
    (hne : T (t.val, chartAt (Model (k + 1)) u u) ≠ 0)
    (Jnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      Model (k + 1) →L[ℝ] Model (k + 1))
    (Tnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (hKnative : ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      (s.val, chartAt (Model (k + 1)) u w) ∈ V →
      letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
      let H := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        (chartAt (Model (k + 1)) u) w).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
      K (s.val, chartAt (Model (k + 1)) u w) = H.comp ((Jnative s (j w)).comp H.inverse))
    (hTnative : ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) u).source →
      (s.val, chartAt (Model (k + 1)) u w) ∈ V →
      letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
      let H := (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        (chartAt (Model (k + 1)) u) w).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j w).inverse
      T (s.val, chartAt (Model (k + 1)) u w) =
        (Tnative s (j w)).compContinuousLinearMap (fun _ => H.inverse)) :
    ∃ U : Set (ℝ × Q.source.ambientManifold.Point),
      IsOpen U ∧ (t.val, Q.ambientNativeReferenceMap e t u.val) ∈ U ∧
      ∃ B : (ℝ × Q.source.ambientManifold.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
          (fun z => coframeComplexStructure (B z)) U ∧
        ∃ S : ℝ × Q.source.ambientManifold.Point → SquaredCanonicalTensor n,
          IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold S U ∧
          (∀ z ∈ U, IsSquaredCanonicalTensor (coframeComplexStructure (B z)) (S z)) ∧
          (∀ z ∈ U, S z ≠ 0) ∧
          ∀ (s : Parameter) y, (s.val, y) ∈ U →
            letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
            let Sinv := (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
              hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm
            let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) Sinv y
            coframeComplexStructure (B (s.val, y)) = D.inverse.comp ((Jnative s (Sinv y)).comp D) ∧
            S (s.val, y) = (Tnative s (Sinv y)).compContinuousLinearMap (fun _ => D) := by
  obtain ⟨W, hWV, hW, hpW, L, hL, hLinv, hLK⟩ :=
    exists_smooth_local_coordinateComplexCoframe P hV hpV
      (show (t.val, chartAt (Model (k + 1)) u u) ∈ parameterInterval ×ˢ univ from
        ⟨t.property, mem_univ _⟩) K hK (by
      intro z hz
      exact hsq ⟨z.1, hz.2.1⟩ z.2 hz.1)
  have hLK' : ∀ (s : Parameter) w, (s.val, w) ∈ W →
      ∀ v, L (s.val, w) (K (s.val, w) v) = coordinateComplexStructure n (L (s.val, w) v) := by
    intro s w hw
    exact hLK _ ⟨hw, s.property, mem_univ _⟩
  obtain ⟨U, hU, hpU, g, hg, hgp, hchart, heq, hcoords,
    hB, hBinv, hJ, hSq, hcan, hnz, _⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_interiorPrescribedGradingExtension hdim e b R hR
      hsquareA hδ C q hqnative hqend t u P W hW hpW L hL hLinv K hLK' T
      (hT.mono hWV) (fun s w hw => hcanonical s w (hWV hw)) hne
  let φ := fun z : ℝ × Q.source.ambientManifold.Point => chartAt (Model (k + 1)) u (g z)
  let B := pullbackCoordinateVerticalCoframe Q.source.ambientManifold φ L
  let S := fun z : ℝ × Q.source.ambientManifold.Point =>
    coordinateSquaredCoframeCoefficient (L (z.1, φ z)) (T (z.1, φ z)) •
      coframeSquaredGenerator (B z)
  refine ⟨U, hU, hpU, B, hB, hBinv, hJ, S, hSq, hcan, hnz, ?_⟩
  intro s y hy
  exact Q.ambientNativeSliceDiffeomorph_symm_interiorCoframe_matches hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    U hU g hg heq s y hy u (hchart _ hy) P _ (hLinv _ (hcoords _ hy))
    (Jnative s) (Tnative s) _ _ (hLK' s _ (hcoords _ hy))
    (hcanonical s _ (hWV (hcoords _ hy)))
    (hKnative s _ (hchart _ hy) (hWV (hcoords _ hy)))
    (hTnative s _ (hchart _ hy) (hWV (hcoords _ hy)))

end FsFltz.Geometry.PairDeformation
