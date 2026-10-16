import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints
import FsFltz.Geometry.OriginalNativeCompletionJunctionGrading

/-!
# Original section endpoints feed the same arbitrary native junction

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–234; and `sec:lean`, lines 788–814.
The endpoint representatives are constructed from original completed-family
sections. Their native comparison equations feed the homotopy producer on
the exact generated completion identification. Original model comparisons
may have unequal tangent dimensions; their differential cancels in every
complex and tensor slot. No represented endpoint equation is supplied.

The original families, original section germs, strict junction and original
homotopy are conditional geometric data. Their toric existence, the full
embedded-core equality and prescribed final class remain unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- Cancel the original model comparison from two native complex-field
restrictions. Both restrictions are expressed on the original slice. -/
theorem nativeComplex_intertwines_of_originalComparisons {d n : ℕ}
    (Z : SmoothManifold d) (X P : SmoothManifold (2 * n))
    (U : Z.SmoothEquiv X) (S : X.SmoothEquiv P)
    (JZ : AlmostComplexField Z) (JX : AlmostComplexField X)
    (JP : AlmostComplexField P)
    (hX : ∀ x v,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) U x (JZ x v) =
        JX (U x) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) U x v))
    (hP : ∀ x v,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (U.trans S) x (JZ x v) =
        JP ((U.trans S) x)
          (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (U.trans S) x v)) :
    ∀ x v, mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x (JX x v) =
      JP (S x) (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x v) := by
  intro y v
  let x := U.symm y
  let E := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) U x
  have hE : E.IsInvertible := U.isInvertible_mfderiv (by simp)
  have h := hP x (E.inverse v)
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S ∘ U) x
      (JZ x (E.inverse v)) = JP (S (U x))
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S ∘ U) x
          (E.inverse v)) at h
  rw [mfderiv_comp x (S.mdifferentiable (by simp) (U x))
    (U.mdifferentiable (by simp) x)] at h
  change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S (U x)
      (E (JZ x (E.inverse v))) = JP (S (U x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S (U x)
          (E (E.inverse v))) at h
  have hX' := hX x (E.inverse v)
  change E (JZ x (E.inverse v)) = JX (U x) (E (E.inverse v)) at hX'
  rw [hX', hE.self_apply_inverse] at h
  have hUx : U x = y := U.apply_symm_apply y
  rw [hUx] at h
  exact h

/-- The corresponding cancellation recovers every slot of the full
canonical-square tensor through the retained endpoint comparison. -/
theorem nativeTensor_restriction_of_originalComparisons {d n : ℕ}
    (Z : SmoothManifold d) (X P : SmoothManifold (2 * n))
    (U : Z.SmoothEquiv X) (S : X.SmoothEquiv P)
    (TZ : Z.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ)
    (TX : X.Point → SquaredCanonicalTensor n)
    (TP : P.Point → SquaredCanonicalTensor n)
    (hX : ∀ x, TZ x = (TX (U x)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) U x))
    (hP : ∀ x, TZ x = (TP ((U.trans S) x)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (U.trans S) x)) :
    ∀ x vs, TX x vs = TP (S x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S x (vs i)) := by
  intro y vs
  let x := U.symm y
  let E := mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) U x
  have hE : E.IsInvertible := U.isInvertible_mfderiv (by simp)
  have h := congrArg (fun T => T (fun i => E.inverse (vs i)))
    ((hX x).symm.trans (hP x))
  change TX (U x) (fun i => E (E.inverse (vs i))) =
    TP (S (U x)) (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n))
      (S ∘ U) x (E.inverse (vs i))) at h
  rw [mfderiv_comp x (S.mdifferentiable (by simp) (U x))
    (U.mdifferentiable (by simp) x)] at h
  change TX (U x) (fun i => E (E.inverse (vs i))) = TP (S (U x))
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) S (U x)
      (E (E.inverse (vs i)))) at h
  simp only [hE.self_apply_inverse] at h
  have hUx : U x = y := U.apply_symm_apply y
  rw [hUx] at h
  exact h

end FsFltz.Geometry

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {kF n : ℕ} [NeZero n] {MF : Type} [TopologicalSpace MF] [T2Space MF]
  [SecondCountableTopology MF]
  [ChartedSpace (EuclideanHalfSpace (kF + 1)) MF]
  [IsManifold (𝓡∂ (kF + 1)) ∞ MF]
  (F : PairDeformation n) (hdimF : kF + 1 = 2 * n)
  (αF : Parameter → Form kF MF 1)
  (eF : ∀ t, Diffeomorph (𝓡∂ (kF + 1)) (𝓡∂ (2 * n)) MF
    (F.pair t).ambientDomain.domain.Point ∞)
  (hpF : ∀ t x, ((F.pair t).ambientDomain.liouville.primitive (eF t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (kF + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eF t y).val) x) = αF t x)
  (hcF : ∀ t, HasNativeCoordinateExtensions (k := kF)
    (F.pair t).ambientDomain.domain.extension (fun x => (eF t x).val))
  (bF : ∀ t, (IntrinsicBoundary.smoothManifold kF MF).SmoothEquiv
    (F.pair t).ambientDomain.domain.boundary)
  (hbF : ∀ t x, (F.pair t).ambientDomain.domain.boundaryInclusion.map (bF t x) = (eF t x.val).val)
  (hsquareBF : ∀ t x, (F.ambientPresentation t).boundaryEquiv (bF parameterZero x) = bF t x)
  (RF : ℝ → Diffeomorph (𝓡∂ (kF + 1)) (𝓡∂ (kF + 1)) MF MF ∞)
  (hRF : IsJointlySmoothDiffeomorphFamily (𝓡∂ (kF + 1)) RF)
  (hsquareAF : ∀ t x, (F.ambientPresentation t).extensionEquiv
    (eF parameterZero (RF t.val x)).val = (eF t x).val)
  {δF : ℝ} (hδF : 0 < δF) (CF : Parameter → ℝ × IntrinsicBoundary.Point kF MF → MF)
  (hembF : ∀ t, IsOpenEmbedding (fun p : Half δF (IntrinsicBoundary.Point kF MF) => CF t p.val))
  (hCF : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model kF)) (𝓡∂ (kF + 1)) ∞ (CF t)
    (Half δF (IntrinsicBoundary.Point kF MF)))
  (hboundaryF : ∀ t (p : Half δF (IntrinsicBoundary.Point kF MF)),
    (𝓡∂ (kF + 1)).IsBoundaryPoint (CF t p.val) ↔ p.val.1 = 0)
  (hinvF : ∀ t p, p ∈ Half δF (IntrinsicBoundary.Point kF MF) →
    ∃ g : MF → ℝ × IntrinsicBoundary.Point kF MF,
      ContMDiffAt (𝓡∂ (kF + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model kF)) ∞ g (CF t p) ∧
        ∀ᶠ qF in 𝓝[Half δF (IntrinsicBoundary.Point kF MF)] p, g (CF t qF) = qF)
  (hzeroF : ∀ t x, CF t (0, x) = x.val)
  (hjointF : IsOpenEmbedding (totalCollar
    (fun t (p : Half δF (IntrinsicBoundary.Point kF MF)) => CF t p.val)))
  (hmixF : HasRealMixedGerms (δ := δF) CF)
  (hodeF : ∀ t x, IsMIntegralCurveOn (fun s => CF t (s, x))
    (fun z => -liouvilleVector (αF t) (exteriorDerivative (αF t)) z) (Ico 0 δF))
  (qF : TotalSpace (fun t (p : Half δF (IntrinsicBoundary.Point kF MF)) => CF t p.val) →
    (F.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnativeF : ∀ t x,
    qF (original (totalCollar (fun t p => CF t p.val)) (t, x)) = F.ambientNativeReferenceMap eF t x)
  (hqendF : ∀ (t : Parameter) (p : Band δF (IntrinsicBoundary.Point kF MF)),
    qF (totalCylinder (fun t p => CF t p.val) (t, p)) =
      (F.ambientCompletionPresentation t).prescribedEndMap (bF parameterZero p.val.2, -p.val.1))

variable
  (JnativeF : ∀ s : Parameter, Space (fun p : Half δF (IntrinsicBoundary.Point kF MF) => CF s p.val) →
    Model (kF + 1) →L[ℝ] Model (kF + 1))
  (PIF : Model (2 * n) ≃L[ℝ] Model (kF + 1))
  (PEF : Model (2 * n) ≃L[ℝ] (Model kF × ℝ))
  (σF : OriginalNativeCanonicalSection CF JnativeF PIF)

local notation "TnativeF" => originalNativeSectionTensor CF JnativeF PIF σF

local notation "JrefF" => F.ambientNativeSlicePullbackComplex hdimF αF eF hpF hcF bF hbF hsquareBF RF hRF hsquareAF
  hδF CF hembF hCF hboundaryF hinvF hzeroF hjointF hmixF hodeF qF hqnativeF hqendF JnativeF
local notation "TrefF" => F.ambientNativeSlicePullbackTensor hdimF αF eF hpF hcF bF hbF hsquareBF RF hRF hsquareAF
  hδF CF hembF hCF hboundaryF hinvF hzeroF hjointF hmixF hodeF qF hqnativeF hqendF TnativeF
local notation "SrefF" => F.ambientNativeSliceDiffeomorph hdimF αF eF hpF hcF bF hbF hsquareBF RF hRF hsquareAF
  hδF CF hembF hCF hboundaryF hinvF hzeroF hjointF hmixF hodeF qF hqnativeF hqendF
local notation "ScompleteF" => F.ambientNativeSliceCompletionDiffeomorph hdimF αF eF hpF hcF bF hbF hsquareBF RF hRF hsquareAF
  hδF CF hembF hCF hboundaryF hinvF hzeroF hjointF hmixF hodeF qF hqnativeF hqendF

variable
  (hbpF : ∀ t, (IntrinsicBoundary.smoothManifold kF MF).pullback
    (F.pair t).ambientDomain.domain.boundary (bF t)
    ((F.pair t).ambientDomain.domain.boundaryForm (F.pair t).ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm (αF t))
  (ΛF : ∀ t, (completionManifold hδF (CF t) (hembF t) (hCF t)
    (hboundaryF t) (hinvF t) (hzeroF t)).Form 1)
  (hΛnativeF : ∀ t, letI := completionChartedSpace hδF (CF t) (hembF t) (hboundaryF t) (hzeroF t)
    ∀ x, (ΛF t (original (fun p => CF t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (kF + 1)) 𝓘(ℝ, Model (kF + 1))
        (original (fun p : Half δF (IntrinsicBoundary.Point kF MF) => CF t p.val)) x) = αF t x)
  (hΛcylinderF : ∀ t, (bandManifold δF (IntrinsicBoundary.smoothManifold kF MF)).pullback
    (completionManifold hδF (CF t) (hembF t) (hCF t) (hboundaryF t) (hinvF t) (hzeroF t))
    (cylinder (fun p => CF t p.val)) (ΛF t) = cylinderPrimitive δF (αF t))
  (hΛsmoothF : ∀ s, (completionManifold hδF (CF s) (hembF s) (hCF s)
    (hboundaryF s) (hinvF s) (hzeroF s)).IsSmoothForm (ΛF s))
  (hnativeF : ∀ s, IsCompatibleAlmostComplex
    (completionManifold hδF (CF s) (hembF s) (hCF s) (hboundaryF s) (hinvF s) (hzeroF s))
    ((completionManifold hδF (CF s) (hembF s) (hCF s) (hboundaryF s) (hinvF s) (hzeroF s)).exteriorDerivative
      (ΛF s)) (JnativeF s))


variable {kG : ℕ} {MG : Type} [TopologicalSpace MG] [T2Space MG]
  [SecondCountableTopology MG]
  [ChartedSpace (EuclideanHalfSpace (kG + 1)) MG]
  [IsManifold (𝓡∂ (kG + 1)) ∞ MG]
  (G : PairDeformation n) (hdimG : kG + 1 = 2 * n)
  (αG : Parameter → Form kG MG 1)
  (eG : ∀ t, Diffeomorph (𝓡∂ (kG + 1)) (𝓡∂ (2 * n)) MG
    (G.pair t).ambientDomain.domain.Point ∞)
  (hpG : ∀ t x, ((G.pair t).ambientDomain.liouville.primitive (eG t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (kG + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eG t y).val) x) = αG t x)
  (hcG : ∀ t, HasNativeCoordinateExtensions (k := kG)
    (G.pair t).ambientDomain.domain.extension (fun x => (eG t x).val))
  (bG : ∀ t, (IntrinsicBoundary.smoothManifold kG MG).SmoothEquiv
    (G.pair t).ambientDomain.domain.boundary)
  (hbG : ∀ t x, (G.pair t).ambientDomain.domain.boundaryInclusion.map (bG t x) = (eG t x.val).val)
  (hsquareBG : ∀ t x, (G.ambientPresentation t).boundaryEquiv (bG parameterZero x) = bG t x)
  (RG : ℝ → Diffeomorph (𝓡∂ (kG + 1)) (𝓡∂ (kG + 1)) MG MG ∞)
  (hRG : IsJointlySmoothDiffeomorphFamily (𝓡∂ (kG + 1)) RG)
  (hsquareAG : ∀ t x, (G.ambientPresentation t).extensionEquiv
    (eG parameterZero (RG t.val x)).val = (eG t x).val)
  {δG : ℝ} (hδG : 0 < δG) (CG : Parameter → ℝ × IntrinsicBoundary.Point kG MG → MG)
  (hembG : ∀ t, IsOpenEmbedding (fun p : Half δG (IntrinsicBoundary.Point kG MG) => CG t p.val))
  (hCG : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model kG)) (𝓡∂ (kG + 1)) ∞ (CG t)
    (Half δG (IntrinsicBoundary.Point kG MG)))
  (hboundaryG : ∀ t (p : Half δG (IntrinsicBoundary.Point kG MG)),
    (𝓡∂ (kG + 1)).IsBoundaryPoint (CG t p.val) ↔ p.val.1 = 0)
  (hinvG : ∀ t p, p ∈ Half δG (IntrinsicBoundary.Point kG MG) →
    ∃ g : MG → ℝ × IntrinsicBoundary.Point kG MG,
      ContMDiffAt (𝓡∂ (kG + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model kG)) ∞ g (CG t p) ∧
        ∀ᶠ qG in 𝓝[Half δG (IntrinsicBoundary.Point kG MG)] p, g (CG t qG) = qG)
  (hzeroG : ∀ t x, CG t (0, x) = x.val)
  (hjointG : IsOpenEmbedding (totalCollar
    (fun t (p : Half δG (IntrinsicBoundary.Point kG MG)) => CG t p.val)))
  (hmixG : HasRealMixedGerms (δ := δG) CG)
  (hodeG : ∀ t x, IsMIntegralCurveOn (fun s => CG t (s, x))
    (fun z => -liouvilleVector (αG t) (exteriorDerivative (αG t)) z) (Ico 0 δG))
  (qG : TotalSpace (fun t (p : Half δG (IntrinsicBoundary.Point kG MG)) => CG t p.val) →
    (G.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnativeG : ∀ t x,
    qG (original (totalCollar (fun t p => CG t p.val)) (t, x)) = G.ambientNativeReferenceMap eG t x)
  (hqendG : ∀ (t : Parameter) (p : Band δG (IntrinsicBoundary.Point kG MG)),
    qG (totalCylinder (fun t p => CG t p.val) (t, p)) =
      (G.ambientCompletionPresentation t).prescribedEndMap (bG parameterZero p.val.2, -p.val.1))

variable
  (JnativeG : ∀ s : Parameter, Space (fun p : Half δG (IntrinsicBoundary.Point kG MG) => CG s p.val) →
    Model (kG + 1) →L[ℝ] Model (kG + 1))
  (PIG : Model (2 * n) ≃L[ℝ] Model (kG + 1))
  (PEG : Model (2 * n) ≃L[ℝ] (Model kG × ℝ))
  (σG : OriginalNativeCanonicalSection CG JnativeG PIG)

local notation "TnativeG" => originalNativeSectionTensor CG JnativeG PIG σG

local notation "JrefG" => G.ambientNativeSlicePullbackComplex hdimG αG eG hpG hcG bG hbG hsquareBG RG hRG hsquareAG
  hδG CG hembG hCG hboundaryG hinvG hzeroG hjointG hmixG hodeG qG hqnativeG hqendG JnativeG
local notation "TrefG" => G.ambientNativeSlicePullbackTensor hdimG αG eG hpG hcG bG hbG hsquareBG RG hRG hsquareAG
  hδG CG hembG hCG hboundaryG hinvG hzeroG hjointG hmixG hodeG qG hqnativeG hqendG TnativeG
local notation "SrefG" => G.ambientNativeSliceDiffeomorph hdimG αG eG hpG hcG bG hbG hsquareBG RG hRG hsquareAG
  hδG CG hembG hCG hboundaryG hinvG hzeroG hjointG hmixG hodeG qG hqnativeG hqendG
local notation "ScompleteG" => G.ambientNativeSliceCompletionDiffeomorph hdimG αG eG hpG hcG bG hbG hsquareBG RG hRG hsquareAG
  hδG CG hembG hCG hboundaryG hinvG hzeroG hjointG hmixG hodeG qG hqnativeG hqendG

variable
  (hbpG : ∀ t, (IntrinsicBoundary.smoothManifold kG MG).pullback
    (G.pair t).ambientDomain.domain.boundary (bG t)
    ((G.pair t).ambientDomain.domain.boundaryForm (G.pair t).ambientDomain.liouville.primitive) =
      IntrinsicBoundary.restrictForm (αG t))
  (ΛG : ∀ t, (completionManifold hδG (CG t) (hembG t) (hCG t)
    (hboundaryG t) (hinvG t) (hzeroG t)).Form 1)
  (hΛnativeG : ∀ t, letI := completionChartedSpace hδG (CG t) (hembG t) (hboundaryG t) (hzeroG t)
    ∀ x, (ΛG t (original (fun p => CG t p.val) x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (kG + 1)) 𝓘(ℝ, Model (kG + 1))
        (original (fun p : Half δG (IntrinsicBoundary.Point kG MG) => CG t p.val)) x) = αG t x)
  (hΛcylinderG : ∀ t, (bandManifold δG (IntrinsicBoundary.smoothManifold kG MG)).pullback
    (completionManifold hδG (CG t) (hembG t) (hCG t) (hboundaryG t) (hinvG t) (hzeroG t))
    (cylinder (fun p => CG t p.val)) (ΛG t) = cylinderPrimitive δG (αG t))
  (hΛsmoothG : ∀ s, (completionManifold hδG (CG s) (hembG s) (hCG s)
    (hboundaryG s) (hinvG s) (hzeroG s)).IsSmoothForm (ΛG s))
  (hnativeG : ∀ s, IsCompatibleAlmostComplex
    (completionManifold hδG (CG s) (hembG s) (hCG s) (hboundaryG s) (hinvG s) (hzeroG s))
    ((completionManifold hδG (CG s) (hembG s) (hCG s) (hboundaryG s) (hinvG s) (hzeroG s)).exteriorDerivative
      (ΛG s)) (JnativeG s))

include PEF hbpF hΛnativeF hΛcylinderF hΛsmoothF hnativeF
  PEG hbpG hΛnativeG hΛcylinderG hΛsmoothG hnativeG in
/-- Two supplied original total-family sections construct their actual
endpoint representatives and deformation lifts. The original junction
homotopy is then transported using the two produced native endpoint laws.
The resulting grading decorates the exact three-arrow path; no represented
per-arrow lift or endpoint restriction is input.

`U` and `U'` are supplied original model comparisons, with explicit complex
and full-tensor restrictions on the original slices. Their compositions
with the retained junction presentations must be the actual `Scomplete`
maps. This is not an existence theorem for these original comparisons or
for a junction between arbitrary original bundle families. -/
theorem exists_gradedThreeStepChain_of_originalTotalSections
    (hJIF : HasOriginalInteriorComplexExtensions hδF CF hembF hboundaryF hzeroF JnativeF)
    (hJEF : HasOriginalEndComplexExtensions hδF CF hembF hboundaryF hzeroF JnativeF)
    (hσF : HasOriginalTotalLocalSectionExtensions hδF CF hembF hboundaryF hzeroF JnativeF PIF σF)
    (hnσF : ∀ s x, σF s x ≠ 0)
    (hJIG : HasOriginalInteriorComplexExtensions hδG CG hembG hboundaryG hzeroG JnativeG)
    (hJEG : HasOriginalEndComplexExtensions hδG CG hembG hboundaryG hzeroG JnativeG)
    (hσG : HasOriginalTotalLocalSectionExtensions hδG CG hembG hboundaryG hzeroG JnativeG PIG σG)
    (hnσG : ∀ s x, σG s x ≠ 0)
    (J : NativeCompletionJunction F.target G.source)
    (U : (completionManifold hδF (CF parameterOne) (hembF parameterOne)
      (hCF parameterOne) (hboundaryF parameterOne) (hinvF parameterOne)
      (hzeroF parameterOne)).SmoothEquiv J.ambient.X)
    (U' : (completionManifold hδG (CG parameterZero) (hembG parameterZero)
      (hCG parameterZero) (hboundaryG parameterZero) (hinvG parameterZero)
      (hzeroG parameterZero)).SmoothEquiv J.ambient.Y)
    (hU : letI := completionChartedSpace hδF (CF parameterOne) (hembF parameterOne) (hboundaryF parameterOne) (hzeroF parameterOne)
      U.trans J.ambient.S = ScompleteF parameterOne)
    (hU' : letI := completionChartedSpace hδG (CG parameterZero) (hembG parameterZero) (hboundaryG parameterZero) (hzeroG parameterZero)
      U'.trans J.ambient.S' = ScompleteG parameterZero)
    (nativeSource : MaslovRepresentative J.ambient.X
      (J.ambient.X.exteriorDerivative J.ambient.α))
    (nativeTarget : MaslovRepresentative J.ambient.Y
      (J.ambient.Y.exteriorDerivative J.ambient.β))
    (H : MaslovHomotopy nativeSource
      (nativeTarget.pullbackTo J.ambient.Ψ J.ambient.strictSymplectic.symm))
    (hOriginalSourceJ : letI := completionChartedSpace hδF (CF parameterOne) (hembF parameterOne) (hboundaryF parameterOne) (hzeroF parameterOne)
      ∀ x v, mfderiv 𝓘(ℝ, Model (kF + 1)) 𝓘(ℝ, Model (2 * n)) U x
        (JnativeF parameterOne x v) = nativeSource.J (U x)
          (mfderiv 𝓘(ℝ, Model (kF + 1)) 𝓘(ℝ, Model (2 * n)) U x v))
    (hOriginalSourceT : letI := completionChartedSpace hδF (CF parameterOne) (hembF parameterOne) (hboundaryF parameterOne) (hzeroF parameterOne)
      ∀ x, TnativeF parameterOne x = (nativeSource.tensor (U x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (kF + 1)) 𝓘(ℝ, Model (2 * n)) U x))
    (hOriginalTargetJ : letI := completionChartedSpace hδG (CG parameterZero) (hembG parameterZero) (hboundaryG parameterZero) (hzeroG parameterZero)
      ∀ x v, mfderiv 𝓘(ℝ, Model (kG + 1)) 𝓘(ℝ, Model (2 * n)) U' x
        (JnativeG parameterZero x v) = nativeTarget.J (U' x)
          (mfderiv 𝓘(ℝ, Model (kG + 1)) 𝓘(ℝ, Model (2 * n)) U' x v))
    (hOriginalTargetT : letI := completionChartedSpace hδG (CG parameterZero) (hembG parameterZero) (hboundaryG parameterZero) (hzeroG parameterZero)
      ∀ x, TnativeG parameterZero x = (nativeTarget.tensor (U' x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (kG + 1)) 𝓘(ℝ, Model (2 * n)) U' x)) :
    ∃ (endpointsF : ∀ s, (F.pair s).Maslov) (endpointsG : ∀ s, (G.pair s).Maslov),
      ∃ (gF : GradedPairDeformation F (endpointsF parameterZero) (endpointsF parameterOne))
        (gG : GradedPairDeformation G (endpointsG parameterZero) (endpointsG parameterOne)),
      ∃ mid : GradedCompletionIdentification J.identification
        (endpointsF parameterOne) (endpointsG parameterZero),
      let path := ((Quiver.Path.nil.cons (ComparisonStep.deformation F)).cons (ComparisonStep.identification J.identification)).cons (ComparisonStep.deformation G)
      ∃ grading : GradedComparisonChain F.source path
        (endpointsF parameterZero) (endpointsG parameterOne),
        grading = (by
          dsimp only [path]
          exact (((GradedComparisonChain.nil (endpointsF parameterZero)).cons
            (.deformation gF)).cons (.identification mid)).cons (.deformation gG)) ∧
        (∀ s : Parameter, gF.family.J s.val = JrefF s.val) ∧
        (∀ (s : Parameter) y, gF.family.tensor s.val y = TrefF s y) ∧
        (∀ s : Parameter, gG.family.J s.val = JrefG s.val) ∧
        (∀ (s : Parameter) y, gG.family.tensor s.val y = TrefG s y) ∧
        (∀ t, mid.family.J t = pullbackAlmostComplex F.target.ambientManifold
          J.ambient.X J.ambient.S.symm (H.family.J t)) ∧
        (∀ t, mid.family.tensor t = pullbackSquaredTensor F.target.ambientManifold
          J.ambient.X J.ambient.S.symm (H.family.tensor t)) ∧
        path.length = 3 ∧ path.vertices = [F.source, F.target, G.source, G.target] := by
  obtain ⟨endpointsF, hJF, hTF, _hJrefF, _hTrefF, gF, _liftF, _hliftF, hgFJ, hgFT⟩ :=
    F.exists_nativeGradedDeformation_with_endpoints_of_originalTotalSection
      hdimF αF eF hpF hcF bF hbF hsquareBF RF hRF hsquareAF hδF CF hembF hCF
      hboundaryF hinvF hzeroF hjointF hmixF hodeF qF hqnativeF hqendF JnativeF PIF PEF σF
      hbpF ΛF hΛnativeF hΛcylinderF hΛsmoothF hnativeF hJIF hJEF hσF hnσF
  obtain ⟨endpointsG, hJG, hTG, _hJrefG, _hTrefG, gG, _liftG, _hliftG, hgGJ, hgGT⟩ :=
    G.exists_nativeGradedDeformation_with_endpoints_of_originalTotalSection
      hdimG αG eG hpG hcG bG hbG hsquareBG RG hRG hsquareAG hδG CG hembG hCG
      hboundaryG hinvG hzeroG hjointG hmixG hodeG qG hqnativeG hqendG JnativeG PIG PEG σG
      hbpG ΛG hΛnativeG hΛcylinderG hΛsmoothG hnativeG hJIG hJEG hσG hnσG
  let := completionChartedSpace hδF (CF parameterOne) (hembF parameterOne)
    (hboundaryF parameterOne) (hzeroF parameterOne)
  let := completionChartedSpace hδG (CG parameterZero) (hembG parameterZero)
    (hboundaryG parameterZero) (hzeroG parameterZero)
  have hsourceJ := nativeComplex_intertwines_of_originalComparisons
    (completionManifold hδF (CF parameterOne) (hembF parameterOne) (hCF parameterOne)
      (hboundaryF parameterOne) (hinvF parameterOne) (hzeroF parameterOne))
    J.ambient.X F.target.ambientManifold U J.ambient.S
    (JnativeF parameterOne) nativeSource.J (endpointsF parameterOne).J hOriginalSourceJ
    (by rw [hU]; exact hJF parameterOne)
  have hsourceT := nativeTensor_restriction_of_originalComparisons
    (completionManifold hδF (CF parameterOne) (hembF parameterOne) (hCF parameterOne)
      (hboundaryF parameterOne) (hinvF parameterOne) (hzeroF parameterOne))
    J.ambient.X F.target.ambientManifold U J.ambient.S
    (TnativeF parameterOne) nativeSource.tensor (endpointsF parameterOne).tensor hOriginalSourceT
    (by rw [hU]; exact hTF parameterOne)
  have htargetJ := nativeComplex_intertwines_of_originalComparisons
    (completionManifold hδG (CG parameterZero) (hembG parameterZero) (hCG parameterZero)
      (hboundaryG parameterZero) (hinvG parameterZero) (hzeroG parameterZero))
    J.ambient.Y G.source.ambientManifold U' J.ambient.S'
    (JnativeG parameterZero) nativeTarget.J (endpointsG parameterZero).J hOriginalTargetJ
    (by rw [hU']; exact hJG parameterZero)
  have htargetT := nativeTensor_restriction_of_originalComparisons
    (completionManifold hδG (CG parameterZero) (hembG parameterZero) (hCG parameterZero)
      (hboundaryG parameterZero) (hinvG parameterZero) (hzeroG parameterZero))
    J.ambient.Y G.source.ambientManifold U' J.ambient.S'
    (TnativeG parameterZero) nativeTarget.tensor (endpointsG parameterZero).tensor hOriginalTargetT
    (by rw [hU']; exact hTG parameterZero)
  let mid := J.gradedLiftOfOriginalHomotopy nativeSource nativeTarget H
    (endpointsF parameterOne) (endpointsG parameterZero) hsourceJ hsourceT htargetJ htargetT
  let grading := ((GradedComparisonChain.nil (endpointsF parameterZero)).cons
    (.deformation gF)).cons (.identification mid) |>.cons (.deformation gG)
  exact ⟨endpointsF, endpointsG, gF, gG, mid, grading, rfl,
    hgFJ, hgFT, hgGJ, hgGT, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

end FsFltz.Geometry.PairDeformation
