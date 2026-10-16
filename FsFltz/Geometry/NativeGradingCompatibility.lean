import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.MaslovPullback
import FsFltz.Geometry.IntervalComplexFamilyExtension

/-!
# Compatibility from the original native slice grading

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The original native complex structure is
compatible with the original completed symplectic form. Its pullback through
the actual slice inverse is compatible with the represented completed form.
The tangent models may differ, so no dimension cast or assumed represented
compatibility is used. The form equality is derived from the established
native primitive equation and exterior-derivative naturality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- Local joint extensions make every original interval slice smooth,
including both endpoints. Restrict the glued extension to the fixed time
and use its literal interval agreement with the original field. -/
theorem HasLocalSmoothIntervalComplexExtensions.slice {d : ℕ}
    {M : SmoothManifold d} {J : ℝ → AlmostComplexField M}
    (hJ : HasLocalSmoothIntervalComplexExtensions M J) (s : Parameter) :
    IsSmoothAlmostComplexField M (J s.val) := by
  obtain ⟨K, hK, hKJ⟩ := exists_smoothComplexFamily_of_localExtensions J hJ
  rw [← hKJ s]
  intro a
  obtain ⟨U, hU, hsub, hsmooth⟩ := hK a
  exact hsmooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x hx => hsub ⟨s.property, hx⟩)

/-- Two-form evaluation commutes with the actual differential even when
the source and target tangent models have different dimensions. -/
theorem SmoothManifold.evalTwo_pullback_differentModels {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    (f : M.Point → N.Point) (eta : N.Form 2) (x : M.Point) (v w : M.Tangent x) :
    SmoothManifold.evalTwo (M.pullback N f eta) x v w =
      SmoothManifold.evalTwo eta (f x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x v)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x w) := by
  apply congrArg (eta (f x))
  funext i
  fin_cases i <;> rfl

/-- Original compatibility transports through an invertible actual tangent
map. Smoothness of the represented field is supplied by its local extensions;
the three geometric compatibility laws all follow from the original field. -/
theorem isCompatibleAlmostComplex_of_invertible_tangentPullback {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (f : M.Point → N.Point)
    (hD : ∀ x, (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x).IsInvertible)
    (etaM : M.Form 2) (etaN : N.Form 2)
    (heta : etaM = M.pullback N f etaN)
    (Jnative : AlmostComplexField N) (hnative : IsCompatibleAlmostComplex N etaN Jnative)
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (heq : ∀ x, J x =
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x).inverse.comp
        ((Jnative (f x)).comp (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x))) :
    IsCompatibleAlmostComplex M etaM J := by
  have hintertwines (x : M.Point) (v : M.Tangent x) :
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x (J x v) =
        Jnative (f x) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x v) := by
    rw [heq x]
    simp only [ContinuousLinearMap.comp_apply, (hD x).self_apply_inverse]
  refine ⟨hJ, ?_, ?_, ?_⟩
  · intro x v
    apply (hD x).injective
    rw [hintertwines, hintertwines, hnative.2.1, map_neg]
  · intro x v w
    rw [heta, M.evalTwo_pullback_differentModels, M.evalTwo_pullback_differentModels,
      hintertwines, hintertwines]
    exact hnative.2.2.1 _ _ _
  · intro x v hv
    rw [heta, M.evalTwo_pullback_differentModels, hintertwines]
    apply hnative.2.2.2
    intro hzero
    exact hv ((hD x).injective (hzero.trans (map_zero _).symm))

/-- Primitive preservation by the actual original slice diffeomorphism
produces the two-form identity needed for compatibility of its inverse
pullback. The original and represented tangent models need not coincide. -/
theorem isCompatibleAlmostComplex_inverse_of_primitivePullback {d e : ℕ}
    (X : SmoothManifold d) (N : SmoothManifold e) (S : X.SmoothEquiv N)
    (Λ : X.Form 1) (beta : N.Form 1) (hΛ : X.IsSmoothForm Λ)
    (hprimitive : X.pullback N S beta = Λ)
    (Jnative : AlmostComplexField X)
    (hnative : IsCompatibleAlmostComplex X (X.exteriorDerivative Λ) Jnative)
    (J : AlmostComplexField N) (hJ : IsSmoothAlmostComplexField N J)
    (heq : ∀ y, J y =
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) S.symm y).inverse.comp
        ((Jnative (S.symm y)).comp (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) S.symm y))) :
    IsCompatibleAlmostComplex N (N.exteriorDerivative beta) J := by
  have hback : N.pullback X S.symm Λ = beta := by
    rw [← hprimitive]
    exact X.pullback_symm_pullback N S beta
  have heta : N.exteriorDerivative beta =
      N.pullback X S.symm (X.exteriorDerivative Λ) := by
    rw [← hback]
    exact N.exteriorDerivative_pullback X ⟨S.symm, S.symm.contMDiff⟩ Λ hΛ
  exact isCompatibleAlmostComplex_of_invertible_tangentPullback N X S.symm
    (fun y => S.symm.isInvertible_mfderiv (by simp)) _ _ heta Jnative hnative J hJ heq

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
/-- The actual original slice map preserves the completed primitive in
the fixed source presentation. Its equation is derived from the native
and full-cylinder restrictions of the original quotient comparison. -/
theorem ambientNativeSliceDiffeomorph_primitive
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
    (s : Parameter) :
    (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)).pullback
      Q.source.ambientCompletion.ambient.manifold
      (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s)
      (Q.completedPrimitive s) = Λ s := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  have hqsmooth := Q.contMDiff_ambientNativeTotalMap hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hboundary hzero hjoint hmix hode q hqnative hqend
  exact Q.pullback_completedPrimitive_ambientNativeTotalMap α e hp b hbp hsquareB
    hδ C hemb hC hboundary hinv hzero hjoint hmix Λ hΛnative hΛcylinder
    q hqsmooth hqnative hqend s

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Original native compatibility gives compatibility of the represented
field along the actual native slice inverse. Only the represented field's
already produced smoothness and literal tangent pullback equation are
required; compatibility is proved from the original completed primitive. -/
theorem ambientNativeSliceDiffeomorph_symm_compatible
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
    (s : Parameter)
    (hΛsmooth : (completionManifold hδ (C s) (hemb s) (hC s)
      (hboundary s) (hinv s) (hzero s)).IsSmoothForm (Λ s))
    (Jnative : AlmostComplexField
      (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)))
    (hnative : IsCompatibleAlmostComplex
      (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s))
      ((completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)).exteriorDerivative
        (Λ s)) Jnative)
    (J : AlmostComplexField Q.source.ambientCompletion.ambient.manifold)
    (hJ : IsSmoothAlmostComplexField Q.source.ambientCompletion.ambient.manifold J)
    (heq : ∀ y,
      letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      let Sinv := (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm
      let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) Sinv y
      J y = D.inverse.comp ((Jnative (Sinv y)).comp D)) :
    IsCompatibleAlmostComplex Q.source.ambientCompletion.ambient.manifold
      (Q.source.ambientCompletion.ambient.manifold.exteriorDerivative (Q.completedPrimitive s)) J := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let X := completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s)
  let S := Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s
  have hprimitive := Q.ambientNativeSliceDiffeomorph_primitive hdim α e hp hc b hb hsquareB
    R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    hbp Λ hΛnative hΛcylinder s
  exact isCompatibleAlmostComplex_inverse_of_primitivePullback X Q.source.ambientCompletion.ambient.manifold
    S (Λ s) (Q.completedPrimitive s) hΛsmooth hprimitive Jnative hnative J hJ heq

end FsFltz.Geometry.PairDeformation
