import FsFltz.Geometry.IntrinsicNativeCompletionGradingGraphExtensions
import FsFltz.Geometry.NativeGradingEndpointPullback
import FsFltz.Geometry.IntrinsicNativeFiniteChain

/-!
# Original grading endpoints on the very same completed deformation

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 225–240;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
Original endpoint intertwinement and full tensor matching through the actual
native completion comparison produce all four presentation endpoint equations.
The represented source and target representatives remain arbitrary supplied
representatives. The constructor grades the same supplied deformation and
retains the literal original slice pullbacks at every interval parameter.
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

variable
  (Jnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (Tnative : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ)

local notation "Jref" => Q.ambientNativeSlicePullbackComplex hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative
local notation "Tref" => Q.ambientNativeSlicePullbackTensor hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Tnative
local notation "Sref" => Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
local notation "Scomplete" => Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend

/-- An original endpoint identification of the complex field through the
actual native completion comparison implies the reference presentation equation. -/
theorem ambientNativeSlicePullbackComplex_endpoint
    (s : Parameter) (endpoint : (Q.pair s).Maslov)
    (hJ : letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x
        (Jnative s x v) = endpoint.J (Scomplete s x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x v)) :
    Jref s.val = pullbackAlmostComplex Q.source.ambientManifold
      (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv endpoint.J := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let X := completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)
  have h := inverseNativeComplex_eq_presentationPullback X Q.source.ambientManifold
    (Q.pair s).ambientManifold (Sref s) (Q.ambientCompletionPresentation s).equiv
    (Jnative s) endpoint.J hJ
  funext y
  rw [Q.ambientNativeSlicePullbackComplex_apply hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative s y]
  exact congrFun h y

/-- Full native endpoint tensor matching implies the presentation equation,
using all tangent slots of the very same native completion map. -/
theorem ambientNativeSlicePullbackTensor_endpoint
    (s : Parameter) (endpoint : (Q.pair s).Maslov)
    (hT : letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      ∀ x, Tnative s x = (endpoint.tensor (Scomplete s x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x)) :
    Tref s = pullbackSquaredTensor Q.source.ambientManifold
      (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv endpoint.tensor := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let X := completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)
  exact inverseNativeTensor_eq_presentationPullback X Q.source.ambientManifold
    (Q.pair s).ambientManifold (Sref s) (Q.ambientCompletionPresentation s).equiv
    (Tnative s) endpoint.tensor hT

variable (PI : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hinterior : HasNativeInteriorGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative PI)
  (hend : HasNativeEndGradingCoordinateExtensions hδ C hemb hboundary hzero Jnative Tnative PE)

variable
  (hbp : ∀ t, (IntrinsicBoundary.smoothManifold k M).pullback
    (Q.pair t).ambientDomain.domain.boundary (b t)
    ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm (α t))
  (Λ : ∀ t, (completionManifold hδ (C t) (hemb t) (hC t)
    (hboundary t) (hinv t) (hzero t)).Form 1)
  (hΛnative : ∀ t, letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    ∀ x, (Λ t (original (fun p => C t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) x) = α t x)
  (hΛcylinder : ∀ t, (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
    (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t))
    (cylinder (fun p => C t p.val)) (Λ t) = cylinderPrimitive δ (α t))
  (hΛsmooth : ∀ s, (completionManifold hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s)).IsSmoothForm (Λ s))
  (hnative : ∀ s, IsCompatibleAlmostComplex
    (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s))
    ((completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)).exteriorDerivative
      (Λ s)) (Jnative s))


include hinterior hend hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- The original native endpoint restrictions grade this very deformation.
All four represented endpoint equations are derived through the actual native
completion maps; the supplied endpoint representatives are retained. The same
lift grades the literal deformation arrow in the original finite itinerary. -/
theorem exists_nativeGradedDeformation_of_nativeGradingEndpoints
    (source : Q.source.Maslov) (target : Q.target.Maslov)
    (eta : ℝ → Q.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive t))
    (hJ₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x
        (Jnative parameterZero x v) = source.J (Scomplete parameterZero x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x v))
    (hJ₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x
        (Jnative parameterOne x v) = target.J (Scomplete parameterOne x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x v))
    (hT₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x, Tnative parameterZero x =
        (source.tensor (Scomplete parameterZero x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x))
    (hT₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x, Tnative parameterOne x =
        (target.tensor (Scomplete parameterOne x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x)) :
    ∃ g : GradedPairDeformation Q source target,
      ∃ lift : NativeGradedComparisonStep (.deformation Q) source target,
        lift = .deformation g ∧
        (∀ t : Parameter, g.family.J t.val = Jref t.val) ∧
        ∀ (s : Parameter) y, g.family.tensor s.val y = Tref s y := by
  have hJzero := Q.ambientNativeSlicePullbackComplex_endpoint hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative parameterZero source hJ₀
  have hJone := Q.ambientNativeSlicePullbackComplex_endpoint hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative parameterOne target hJ₁
  have hTzero := Q.ambientNativeSlicePullbackTensor_endpoint hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Tnative parameterZero source hT₀
  have hTone := Q.ambientNativeSlicePullbackTensor_endpoint hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Tnative parameterOne target hT₁
  obtain ⟨g, hgJ, hgT⟩ := Q.exists_gradedPairDeformation_of_nativeGradingCoordinateExtensions
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative Tnative PI PE hinterior hend
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative source target eta heta
    hJzero hJone (congrFun hTzero) (congrFun hTone)
  exact ⟨g, .deformation g, rfl, hgJ, hgT⟩


include hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- Actual smooth native canonical-square section germs construct the full
source tensor extensions and feed the original endpoint transport consumer.
The resulting grading retains the same supplied deformation and its literal
native itinerary arrow, with no coordinate tensor regularity or represented
grading lift supplied as an input. Existence of the native section germs is
not asserted here. -/
theorem exists_nativeGradedDeformation_of_nativeSectionGerms
    (hinteriorGerms : HasNativeInteriorGradingSectionGerms
      hδ C hemb hboundary hzero Jnative Tnative PI)
    (hendGerms : HasNativeEndGradingSectionGerms
      hδ C hemb hboundary hzero Jnative Tnative PE)
    (source : Q.source.Maslov) (target : Q.target.Maslov)
    (eta : ℝ → Q.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive t))
    (hJ₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x
        (Jnative parameterZero x v) = source.J (Scomplete parameterZero x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x v))
    (hJ₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x
        (Jnative parameterOne x v) = target.J (Scomplete parameterOne x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x v))
    (hT₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x, Tnative parameterZero x =
        (source.tensor (Scomplete parameterZero x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x))
    (hT₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x, Tnative parameterOne x =
        (target.tensor (Scomplete parameterOne x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x)) :
    ∃ g : GradedPairDeformation Q source target,
      ∃ lift : NativeGradedComparisonStep (.deformation Q) source target,
        lift = .deformation g ∧
        (∀ t : Parameter, g.family.J t.val = Jref t.val) ∧
        ∀ (s : Parameter) y, g.family.tensor s.val y = Tref s y := by
  have hi := nativeInteriorGradingCoordinateExtensions_of_sectionGerms
    hδ C hemb hboundary hzero Jnative Tnative PI hinteriorGerms
  have he := nativeEndGradingCoordinateExtensions_of_sectionGerms
    hδ C hemb hboundary hzero Jnative Tnative PE hendGerms
  exact Q.exists_nativeGradedDeformation_of_nativeGradingEndpoints
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative Tnative PI PE hi he
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative source target eta heta hJ₀ hJ₁ hT₀ hT₁

include hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- Native bundle-valued graph extensions produce actual section germs,
then grade this very supplied deformation and its literal itinerary arrow.
Only the original parameter locus must have the correct base projection;
neither extending sections nor tensor regularity are supplied. The original
total-family atlas and graph-extension correspondence remain separate. -/
theorem exists_nativeGradedDeformation_of_nativeGraphExtensions
    (hinteriorGraphs : HasNativeInteriorGradingGraphExtensions
      hδ C hemb hboundary hzero Jnative Tnative PI)
    (hendGraphs : HasNativeEndGradingGraphExtensions
      hδ C hemb hboundary hzero Jnative Tnative PE)
    (source : Q.source.Maslov) (target : Q.target.Maslov)
    (eta : ℝ → Q.source.ambientManifold.Form 2)
    (heta : ∀ t : Parameter, eta t.val =
      Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive t))
    (hJ₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x
        (Jnative parameterZero x v) = source.J (Scomplete parameterZero x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x v))
    (hJ₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x
        (Jnative parameterOne x v) = target.J (Scomplete parameterOne x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x v))
    (hT₀ : letI := completionChartedSpace hδ (C parameterZero) (hemb parameterZero) (hboundary parameterZero) (hzero parameterZero)
      ∀ x, Tnative parameterZero x =
        (source.tensor (Scomplete parameterZero x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterZero) x))
    (hT₁ : letI := completionChartedSpace hδ (C parameterOne) (hemb parameterOne) (hboundary parameterOne) (hzero parameterOne)
      ∀ x, Tnative parameterOne x =
        (target.tensor (Scomplete parameterOne x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete parameterOne) x)) :
    ∃ g : GradedPairDeformation Q source target,
      ∃ lift : NativeGradedComparisonStep (.deformation Q) source target,
        lift = .deformation g ∧
        (∀ t : Parameter, g.family.J t.val = Jref t.val) ∧
        ∀ (s : Parameter) y, g.family.tensor s.val y = Tref s y := by
  have hi := nativeInteriorGradingSectionGerms_of_graphExtensions
    hδ C hemb hboundary hzero Jnative Tnative PI hinteriorGraphs
  have he := nativeEndGradingSectionGerms_of_graphExtensions
    hδ C hemb hboundary hzero Jnative Tnative PE hendGraphs
  exact Q.exists_nativeGradedDeformation_of_nativeSectionGerms
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative Tnative PI PE
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative hi he source target eta heta hJ₀ hJ₁ hT₀ hT₁

end FsFltz.Geometry.PairDeformation
