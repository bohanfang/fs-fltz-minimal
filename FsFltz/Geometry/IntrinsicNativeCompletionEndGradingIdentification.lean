import FsFltz.Geometry.IntrinsicNativeCompletionInteriorGradingIdentification
import FsFltz.Geometry.IntrinsicNativeCompletionEndGradingDerivative
import FsFltz.Geometry.IntrinsicNativeCompletionEndPrescribedGrading
import FsFltz.Geometry.CoordinateComplexCoframe

/-!
# The prescribed original slice grading in the retained end inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
Source coordinate representatives are compared with the prescribed original
native slice data through the actual full cylinder and chart tangent
maps. The produced real inverse has that exact slice differential on the
interval. Consequently the coframe extension is the prescribed original
slice pullback, including the complete canonical-square tensor.
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

local instance endGradingIdentificationBandCharts : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance endGradingIdentificationProductCharts : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance endGradingIdentificationProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Original native fields represented in the retained end chart
pull back to the coframe extension through the original slice inverse.
Both matching equations are derived from source coordinate expressions and
the proved differential of the actual native inverse. -/
theorem ambientNativeSliceDiffeomorph_symm_endCoframe_matches
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U)
    (heq : ∀ (s : Parameter) y, (s.val, y) ∈ U →
      ∃ p : Band δ (IntrinsicBoundary.Point k M),
        p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
        (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
          totalCylinder (fun t p => C t p.val) (s, p))
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val, y) ∈ U) (u : IntrinsicBoundary.Point k M × ℝ)
    (hchart : g (s.val, y) ∈ (chartAt (Model k × ℝ) u).source)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpcoord : p.val = (-(g (s.val, y)).2, (g (s.val, y)).1))
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (L : (Model k × ℝ) →L[ℝ] TangentCoordinates n) (hL : L.IsInvertible)
    (Jnative : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      Model (k + 1) →L[ℝ] Model (k + 1))
    (Tnative : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (K : (Model k × ℝ) →L[ℝ] (Model k × ℝ))
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => (Model k × ℝ)) ℂ)
    (hLK : ∀ v, L (K v) = coordinateComplexStructure n (L v))
    (hcan : IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp (K.comp P.toContinuousLinearMap))
      (T.compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    let w := g (s.val, y)
    let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
    let H : Model (k + 1) →L[ℝ] (Model k × ℝ) := (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
      (chartAt (Model k × ℝ) u) w).comp
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y
    let A := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => chartAt (Model k × ℝ) u (g (s.val, z))) y
    K = H.comp ((Jnative (j p)).comp H.inverse) →
    T = (Tnative (j p)).compContinuousLinearMap (fun _ => H.inverse) →
    coframeComplexStructure (L.comp A) =
      D.inverse.comp ((Jnative ((Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)).comp D) ∧
    coordinateSquaredCoframeCoefficient L T • coframeSquaredGenerator (L.comp A) =
      (Tnative ((Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)).compContinuousLinearMap (fun _ => D) := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  dsimp only
  intro hK hT
  let w := g (s.val, y)
  let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
  let H : Model (k + 1) →L[ℝ] (Model k × ℝ) := (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
      (chartAt (Model k × ℝ) u) w).comp
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
  have hci : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
      (chartAt (Model k × ℝ) u) w).IsInvertible := by
    have hc := mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u
    apply ContinuousLinearMap.IsInvertible.of_inverse ?_ (hc.symm_comp_deriv hchart)
    have h := hc.comp_symm_deriv ((chartAt (Model k × ℝ) u).map_source hchart)
    rwa [(chartAt (Model k × ℝ) u).left_inv hchart] at h
  have hHi : H.IsInvertible := hci.comp
    ((isInvertible_mfderiv_endBandCoordinates p).comp
      (isInvertible_mfderiv_completionCylinder hδ (C s) (hemb s) (hC s)
        (hboundary s) (hinv s) (hzero s) p).inverse)
  have hA := Q.ambientNativeSliceDiffeomorph_symm_endChart_mfderiv hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    U hU g hg heq s y hy u hchart p hpcoord
  have htotal : (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
      totalCylinder (fun t p => C t p.val) (s, p) := by
    obtain ⟨p', hp', he'⟩ := heq s y hy
    have hp'p : p' = p := Subtype.ext (hp'.trans hpcoord.symm)
    simpa only [hp'p] using he'
  have hpoint := Q.ambientNativeSliceDiffeomorph_symm_eq_cylinder_of_total hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    s y p htotal
  rw [hpoint]
  refine ⟨?_, ?_⟩
  · rw [coframeComplexStructure_coordinateComp_eq L hL _ K hLK, hA, hK]
    simpa only [H, j, w, ContinuousLinearMap.comp_assoc] using
      conjugatedComplexStructure_coordinateCancel (E := Model (2 * n)) H hHi
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
          (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
            hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)
        (Jnative (j p))
  · have hrec := coordinateSquaredCoframe_reconstruction P L hL K hLK T hcan
    rw [smul_coframeSquaredGenerator_coordinateComp, ← hrec, hA, hT]
    simpa only [H, j, w, ContinuousLinearMap.comp_assoc] using
      squaredTensor_coordinateCancel (E := Model (2 * n)) H hHi
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
          (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
            hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)
        (Tnative (j p))

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- A smooth prescribed original source complex field produces its own local
coframe. The same original inverse germ carries a smooth nonzero canonical
square and its full native slice pullback, with source chart representatives
as the only grading-identification inputs. -/
theorem exists_ambientNativeSlice_endPrescribedGradingExtension
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r)
    (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (V : Set (ℝ × (Model k × ℝ))) (hV : IsOpen V)
    (hpV : (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ∈ V)
    (K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ))
    (hK : ContDiffOn ℝ ∞ K V)
    (hKsq : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      ∀ v, K (s.val, w) (K (s.val, w) v) = -v)
    (T : (ℝ × (Model k × ℝ)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => (Model k × ℝ)) ℂ)
    (hT : ContDiffOn ℝ ∞ T V)
    (hcanonical : ∀ (s : Parameter) w, (s.val, w) ∈ V →
      IsSquaredCanonicalTensor
        (P.symm.toContinuousLinearMap.comp ((K (s.val, w)).comp P.toContinuousLinearMap))
        ((T (s.val, w)).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)))
    (hne : T (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ≠ 0)
    (Jnative : ∀ s : Parameter,
      Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
        Model (k + 1) →L[ℝ] Model (k + 1))
    (Tnative : ∀ s : Parameter,
      Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)
    (hcoordinates : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      let w := endBandCoordinates p
      w ∈ (chartAt (Model k × ℝ) (x, r)).source →
      (s.val, chartAt (Model k × ℝ) (x, r) w) ∈ V →
      let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)
      let H := (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
        (chartAt (Model k × ℝ) (x, r)) w).comp
        ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse)
      K (s.val, chartAt (Model k × ℝ) (x, r) w) =
        H.comp ((Jnative s (j p)).comp H.inverse) ∧
      T (s.val, chartAt (Model k × ℝ) (x, r) w) =
        (Tnative s (j p)).compContinuousLinearMap (fun _ => H.inverse)) :
    ∃ L : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n,
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
        (∀ (s : Parameter) y, (s.val, y) ∈ U →
          coframeComplexStructure (B (s.val, y)) =
            (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
              (fun y => φ (s.val, y)) y).inverse.comp
              ((K (s.val, φ (s.val, y))).comp
                (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
                  (fun y => φ (s.val, y)) y)) ∧
          a' (s.val, y) • coframeSquaredGenerator (B (s.val, y)) =
            (T (s.val, φ (s.val, y))).compContinuousLinearMap
              (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, (Model k × ℝ))
                (fun y => φ (s.val, y)) y)) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
          let S := Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
            hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s
          let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) S.symm y
          coframeComplexStructure (B (s.val, y)) =
            D.inverse.comp ((Jnative s (S.symm y)).comp D) ∧
          a' (s.val, y) • coframeSquaredGenerator (B (s.val, y)) =
            (Tnative s (S.symm y)).compContinuousLinearMap (fun _ => D) := by
  let A : Set (ℝ × (Model k × ℝ)) := parameterInterval ×ˢ univ
  have hpA : (t.val, chartAt (Model k × ℝ) (x, r) (x, r)) ∈ A := ⟨t.property, mem_univ _⟩
  have hsq : ∀ z ∈ V ∩ A, ∀ v, K z (K z v) = -v := by
    intro z hz v
    exact hKsq ⟨z.1, hz.2.1⟩ z.2 hz.1 v
  obtain ⟨W, hWV, hW, hpW, L, hL, hLi, hLK₀⟩ :=
    exists_smooth_local_coordinateComplexCoframe P hV hpV hpA K hK hsq
  have hLK : ∀ (s : Parameter) w, (s.val, w) ∈ W →
      ∀ v, L (s.val, w) (K (s.val, w) v) = coordinateComplexStructure n (L (s.val, w) v) := by
    intro s w hw
    exact hLK₀ _ ⟨hw, ⟨s.property, mem_univ _⟩⟩
  obtain ⟨U, hU, hpU, g, hg, hgp, hgchart, heq, hUV, hB, hBi, hJ, hSq,
    hcan, hnz, hcoordpull⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_endPrescribedGradingExtension
      hdim α e hp hc b hb hsquareB R hsquareA hδ C hzero hode q hqnative hqend
      t x r hr P W hW hpW L hL hLi K hLK T (hT.mono hWV)
      (fun s w hw => hcanonical s w (hWV hw)) hne
  refine ⟨L, U, hU, hpU, g, hg, hgp, hgchart, heq,
    (fun z hz => hWV (hUV z hz)), hB, hBi, hJ, hSq, hcan, hnz, hcoordpull, ?_⟩
  intro s y hy
  obtain ⟨p, hpcoord, _⟩ := heq s y hy
  have hpc : endBandCoordinates p = g (s.val, y) := by
    change (p.val.2, -p.val.1) = g (s.val, y)
    rw [hpcoord]
    simp only [neg_neg, Prod.mk.eta]
  have hsrc := hcoordinates s p (hpc.symm ▸ hgchart _ hy)
    (hpc.symm ▸ hWV (hUV _ hy))
  dsimp only at hsrc
  rw [hpc] at hsrc
  have hm := Q.ambientNativeSliceDiffeomorph_symm_endCoframe_matches
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend U hU g hg heq s y hy (x, r) (hgchart _ hy)
    p hpcoord P (L (s.val, chartAt (Model k × ℝ) (x, r) (g (s.val, y))))
    (hLi _ (hUV _ hy)) (Jnative s) (Tnative s)
    (K (s.val, chartAt (Model k × ℝ) (x, r) (g (s.val, y))))
    (T (s.val, chartAt (Model k × ℝ) (x, r) (g (s.val, y))))
    (hLK s _ (hUV _ hy)) (hcanonical s _ (hWV (hUV _ hy)))
  simpa only [pullbackCoordinateVerticalCoframe, hpc] using hm
    hsrc.1 hsrc.2

end FsFltz.Geometry.PairDeformation
