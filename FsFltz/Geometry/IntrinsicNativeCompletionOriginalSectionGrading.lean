import FsFltz.Geometry.IntrinsicNativeCompletionInteriorSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionEndSectionExtraction
import FsFltz.Geometry.IntrinsicNativeCompletionWholeSectionCorrespondence
import FsFltz.Geometry.IntrinsicNativeCompletionGradingEndpoints

/-!
# One original canonical section grades the same completed deformation

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–240; `g:chain`, lines 407–413; and `sec:lean`,
lines 788–814. The interior and cylinder constructions consume one original
canonical-square section. Its natural full tensor is derived internally;
neither graph extensions nor tensor regularity is supplied. The existing
cover and native endpoint laws then grade the very same supplied deformation.

The total-point local-cover convention is proved equivalent to the original
branch conditions by both actual mixed scalar extension transfers, and is
consumed below for the same deformation. The result uses the source's smooth
open-extension convention. A whole mixed-chart bundle topology, a converse
for bare boundary smoothness and general marked/graded-chain integration
remain separate obligations. No existence of a target grading is asserted.
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
  (PI : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (PE : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (σ : OriginalNativeCanonicalSection C Jnative PI)

local notation "Tnative" => originalNativeSectionTensor C Jnative PI σ

local notation "Jref" => Q.ambientNativeSlicePullbackComplex hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative
local notation "Tref" => Q.ambientNativeSlicePullbackTensor hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Tnative
local notation "Sref" => Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
local notation "Scomplete" => Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend

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


include PE hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- Actual original section data supply both branches of the same-deformation
grading constructor, preserving all interval fields and every tensor slot. -/
theorem exists_nativeGradedDeformation_of_originalSection
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hσI : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero Jnative PI σ)
    (hσE : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero Jnative PI σ)
    (hnσ : ∀ s x, σ s x ≠ 0)
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
  have hJsq : ∀ s x v, Jnative s x (Jnative s x v) = -v :=
    fun s => (hnative s).2.1
  have hi := originalNativeInteriorGradingSectionGerms
    hδ C hemb hboundary hzero Jnative PI hC hinv hJI hJsq σ hσI hnσ
  have he := originalNativeEndGradingSectionGerms
    hδ C hemb hboundary hzero Jnative PI PE hC hinv hJE hJsq σ hσE hnσ
  exact Q.exists_nativeGradedDeformation_of_nativeSectionGerms
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative Tnative PI PE
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative hi he source target eta heta hJ₀ hJ₁ hT₀ hT₁


include PE hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- One original section with a coefficient germ in either native covering
chart near each total-family point grades the same supplied deformation.
Both branch conditions are derived using the real mixed transitions. The
four prescribed endpoint equations and the exact full tensor are retained. -/
theorem exists_nativeGradedDeformation_of_originalTotalSection
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hσ : HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero Jnative PI σ)
    (hnσ : ∀ s x, σ s x ≠ 0)
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
  have hJsq : ∀ s x v, Jnative s x (Jnative s x v) = -v :=
    fun s => (hnative s).2.1
  obtain ⟨hσI, hσE⟩ := (originalTotalLocalSectionExtensions_iff
    hδ C hemb hboundary hzero Jnative PI hC hinv PE hjoint hmix hJI hJE hJsq σ).mp hσ
  exact Q.exists_nativeGradedDeformation_of_originalSection
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative PI PE σ
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative hJI hJE hσI hσE hnσ
    source target eta heta hJ₀ hJ₁ hT₀ hT₁

end FsFltz.Geometry.PairDeformation
