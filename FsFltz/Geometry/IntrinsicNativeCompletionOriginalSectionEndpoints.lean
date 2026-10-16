import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionGrading
import FsFltz.Geometry.MaslovClassPullback

/-!
# Endpoint representatives constructed from an original completed-family section

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–240; and `sec:lean`, lines 788–814.
The original total-family section produces representatives on every completed
pair slice. Their restrictions through the actual native completion maps are
proved, including both endpoint equations needed by the grading constructor.
The supplied deformation and its native realization are retained.

This is representation of supplied geometric and grading data. It does not
construct the toric comparison chain, its markings, its full embedded core,
or the prescribed endpoint class in `thm:target`, lines 352–435.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- Restrict a smooth nonvanishing canonical-square family to an actual
parameter. Both the tensor and compatible complex field remain literal. -/
def MaslovFamily.representative {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : ℝ → M.Form 2} (f : MaslovFamily M eta) (s : Parameter) :
    MaslovRepresentative M (eta s.val) where
  J := f.J s.val
  compatible := f.compatible s.val s.property
  tensor := f.tensor s.val
  canonical := f.canonical s.val s.property
  smooth := by
    intro a
    obtain ⟨U, hU, hsub, h⟩ := f.smoothSection a
    exact h.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => hsub ⟨s.property, hx⟩)
  nowhereZero := f.nowhereZero s.val s.property

/-- Recover the native complex-field equation from its actual inverse
pullback, allowing unequal native and represented tangent models. -/
theorem nativeComplex_intertwines_of_inversePullback {d n : ℕ}
    (X : SmoothManifold d) (M N : SmoothManifold (2 * n))
    (S : X.SmoothEquiv M) (P : M.SmoothEquiv N)
    (Jnative : AlmostComplexField X) (J : AlmostComplexField N)
    (hJ : ∀ y,
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y).inverse.comp
        ((Jnative (S.symm y)).comp
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y)) =
        pullbackAlmostComplex M N P J y) :
    ∀ x v, mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x (Jnative x v) =
      J ((S.trans P) x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x v) := by
  intro x v
  let D : Model (2 * n) →L[ℝ] Model d :=
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm (S x)
  let E : Model d →L[ℝ] Model (2 * n) :=
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) S x
  have hD : D.IsInvertible := S.symm.isInvertible_mfderiv (by simp)
  have hDE : D.comp E = ContinuousLinearMap.id ℝ (Model d) := by
    have he : S.symm ∘ S = id := funext S.symm_apply_apply
    rw [← mfderiv_comp x (S.symm.mdifferentiable (by simp) (S x))
      (S.mdifferentiable (by simp) x), he, mfderiv_id]
    rfl
  have hDEv (w : Model d) : D (E w) = w := congrArg (fun L => L w) hDE
  have hnative : E (Jnative x v) = pullbackAlmostComplex M N P J (S x) (E v) := by
    apply hD.injective
    have h := congrArg (fun L => D (L (E v))) (hJ (S x))
    change D (D.inverse (Jnative (S.symm (S x)) (D (E v)))) =
      D (pullbackAlmostComplex M N P J (S x) (E v)) at h
    rw [hD.self_apply_inverse, S.symm_apply_apply, hDEv] at h
    rw [hDEv]
    exact h
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (P ∘ S) x (Jnative x v) =
    J (P (S x)) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (P ∘ S) x v)
  rw [mfderiv_comp x (P.mdifferentiable (by simp) (S x))
    (S.mdifferentiable (by simp) x)]
  change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) P (S x)
      (E (Jnative x v)) = J (P (S x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) P (S x) (E v))
  rw [hnative, pullbackAlmostComplex_intertwines]

/-- Every native tensor slot is recovered by cancellation of the actual
slice derivative with its inverse, followed by the completion presentation. -/
theorem nativeTensor_restriction_of_inversePullback {d n : ℕ}
    (X : SmoothManifold d) (M N : SmoothManifold (2 * n))
    (S : X.SmoothEquiv M) (P : M.SmoothEquiv N)
    (Tnative : X.Point → ContinuousMultilinearMap ℝ
      (fun _ : Fin n ⊕ Fin n => Model d) ℂ)
    (T : N.Point → SquaredCanonicalTensor n)
    (hT : ∀ y, (Tnative (S.symm y)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm y) =
        pullbackSquaredTensor M N P T y) :
    ∀ x, Tnative x = (T ((S.trans P) x)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (S.trans P) x) := by
  intro x
  ext v
  let D : Model (2 * n) →L[ℝ] Model d :=
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model d) S.symm (S x)
  let E : Model d →L[ℝ] Model (2 * n) :=
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) S x
  have hDE : D.comp E = ContinuousLinearMap.id ℝ (Model d) := by
    have he : S.symm ∘ S = id := funext S.symm_apply_apply
    rw [← mfderiv_comp x (S.symm.mdifferentiable (by simp) (S x))
      (S.mdifferentiable (by simp) x), he, mfderiv_id]
    rfl
  have hDEv (w : Model d) : D (E w) = w := congrArg (fun L => L w) hDE
  have h := congrArg (fun L => L (fun i => E (v i))) (hT (S x))
  change Tnative (S.symm (S x)) (fun i => D (E (v i))) =
    T (P (S x)) (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
      P (S x) (E (v i))) at h
  rw [S.symm_apply_apply] at h
  simp_rw [hDEv] at h
  change Tnative x v = T (P (S x))
    (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) (P ∘ S) x (v i))
  rw [mfderiv_comp x (P.mdifferentiable (by simp) (S x))
    (S.mdifferentiable (by simp) x)]
  exact h

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

open scoped Classical in
/-- The actual completed symplectic family on the interval, extended by
zero elsewhere. Grading compatibility is required only on the interval. -/
def completedSymplecticExtension : ℝ → Q.source.ambientManifold.Form 2 :=
  fun t => if ht : t ∈ parameterInterval then
    Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive ⟨t, ht⟩)
  else 0

omit [NeZero n] in
@[simp] theorem completedSymplecticExtension_apply (s : Parameter) :
    Q.completedSymplecticExtension s.val =
      Q.source.ambientManifold.exteriorDerivative (Q.completedPrimitive s) := by
  unfold completedSymplecticExtension
  split
  · rfl
  · rename_i h
    exact (h s.property).elim

include PE hbp hΛnative hΛcylinder hΛsmooth hnative in
/-- An original total-family section constructs the representatives on all
actual completed pair slices. Restriction through the same native completion
map recovers the complex structure and every slot of the original tensor.
The existing total-section consumer grades this very deformation at the two
constructed endpoints; no endpoint representative or matching equation is
an input. -/
theorem exists_nativeGradedDeformation_with_endpoints_of_originalTotalSection
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero Jnative)
    (hσ : HasOriginalTotalLocalSectionExtensions hδ C hemb hboundary hzero Jnative PI σ)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    ∃ endpoints : ∀ s, (Q.pair s).Maslov,
      (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
        ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x
          (Jnative s x v) = (endpoints s).J (Scomplete s x)
            (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x v)) ∧
      (∀ s, letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
        ∀ x, Tnative s x = ((endpoints s).tensor (Scomplete s x)).compContinuousLinearMap
          (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x)) ∧
      (∀ s, Jref s.val = pullbackAlmostComplex Q.source.ambientManifold
        (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv (endpoints s).J) ∧
      (∀ s, Tref s = pullbackSquaredTensor Q.source.ambientManifold
        (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv (endpoints s).tensor) ∧
      ∃ g : GradedPairDeformation Q (endpoints parameterZero) (endpoints parameterOne),
        ∃ lift : NativeGradedComparisonStep (.deformation Q)
            (endpoints parameterZero) (endpoints parameterOne),
          lift = .deformation g ∧
          (∀ s : Parameter, g.family.J s.val = Jref s.val) ∧
          ∀ (s : Parameter) y, g.family.tensor s.val y = Tref s y := by
  have hJsq : ∀ s x v, Jnative s x (Jnative s x v) = -v := fun s => (hnative s).2.1
  obtain ⟨hσI, hσE⟩ := (originalTotalLocalSectionExtensions_iff
    hδ C hemb hboundary hzero Jnative PI hC hinv PE hjoint hmix hJI hJE hJsq σ).mp hσ
  have hi := nativeInteriorGradingCoordinateExtensions_of_sectionGerms
    hδ C hemb hboundary hzero Jnative Tnative PI
    (originalNativeInteriorGradingSectionGerms
      hδ C hemb hboundary hzero Jnative PI hC hinv hJI hJsq σ hσI hnσ)
  have he := nativeEndGradingCoordinateExtensions_of_sectionGerms
    hδ C hemb hboundary hzero Jnative Tnative PE
    (originalNativeEndGradingSectionGerms
      hδ C hemb hboundary hzero Jnative PI PE hC hinv hJE hJsq σ hσE hnσ)
  have hJ := Q.ambientNativeSlicePullbackComplex_localExtensions hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hi he
  let sectionRef := Q.ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend Jnative Tnative PI PE hi he
  have hs := Q.ambientNativeSlicePullbackTensorSection_localCoefficients hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hi he
  have hn := Q.ambientNativeSlicePullbackTensorSection_ne_zero hdim α e hp hc b hb hsquareB R hR
    hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hi he
  have hmap := Q.canonicalSquareMap_ambientNativeSlicePullbackTensorSection hdim α e hp hc b hb
    hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
    Jnative Tnative PI PE hi he
  have hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex Q.source.ambientManifold (Q.completedSymplecticExtension t) (Jref t) := by
    intro t ht
    let s : Parameter := ⟨t, ht⟩
    rw [Q.completedSymplecticExtension_apply s]
    exact Q.ambientNativeSlicePullbackComplex_compatible hdim α e hp hc b hb hsquareB R hR
      hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      Jnative Tnative PI PE hi he hbp Λ hΛnative hΛcylinder hΛsmooth hnative s
  obtain ⟨f, hfJ, hfT⟩ := exists_maslovFamily_of_localExtensions Jref hcompatible hJ sectionRef hn hs
  have hfTensor (s : Parameter) : f.tensor s.val = Tref s := by
    funext y
    exact (hfT (s, y)).trans (hmap (s, y))
  have hform (s : Parameter) : Q.source.ambientManifold.pullback (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientSymplecticForm =
        Q.completedSymplecticExtension s.val := by
    rw [Q.completedSymplecticExtension_apply]
    exact (Q.source.ambientManifold.exteriorDerivative_pullback (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv.toContMDiffMap
      (Q.pair s).ambientCompletion.ambient.primitive
      (Q.pair s).ambientCompletion.ambient.smooth_primitive).symm
  have hinvForm (s : Parameter) : (Q.pair s).ambientManifold.pullback Q.source.ambientManifold
      (Q.ambientCompletionPresentation s).equiv.symm (Q.completedSymplecticExtension s.val) =
        (Q.pair s).ambientSymplecticForm := by
    rw [← hform s]
    exact Q.source.ambientManifold.pullback_symm_pullback (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv (Q.pair s).ambientSymplecticForm
  let endpoints : ∀ s, (Q.pair s).Maslov := fun s =>
    (f.representative s).pullbackTo (Q.ambientCompletionPresentation s).equiv.symm (hinvForm s)
  have hJrep (s : Parameter) : Jref s.val = pullbackAlmostComplex Q.source.ambientManifold
      (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv (endpoints s).J := by
    rw [← hfJ s]
    change f.J s.val = pullbackAlmostComplex Q.source.ambientManifold (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv
      (pullbackAlmostComplex (Q.pair s).ambientManifold Q.source.ambientManifold
        (Q.ambientCompletionPresentation s).equiv.symm (f.J s.val))
    rw [← pullbackAlmostComplex_trans, Diffeomorph.self_trans_symm, pullbackAlmostComplex_refl]
  have hTrep (s : Parameter) : Tref s = pullbackSquaredTensor Q.source.ambientManifold
      (Q.pair s).ambientManifold (Q.ambientCompletionPresentation s).equiv (endpoints s).tensor := by
    rw [← hfTensor s]
    change f.tensor s.val = pullbackSquaredTensor Q.source.ambientManifold (Q.pair s).ambientManifold
      (Q.ambientCompletionPresentation s).equiv
      (pullbackSquaredTensor (Q.pair s).ambientManifold Q.source.ambientManifold
        (Q.ambientCompletionPresentation s).equiv.symm (f.tensor s.val))
    rw [← pullbackSquaredTensor_trans, Diffeomorph.self_trans_symm, pullbackSquaredTensor_refl]
  have hJnative (s : Parameter) : letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      ∀ x v, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x
        (Jnative s x v) = (endpoints s).J (Scomplete s x)
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x v) := by
    let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    exact nativeComplex_intertwines_of_inversePullback
      (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s))
      Q.source.ambientManifold (Q.pair s).ambientManifold (Sref s)
      (Q.ambientCompletionPresentation s).equiv (Jnative s) (endpoints s).J
      (fun y => (Q.ambientNativeSlicePullbackComplex_apply hdim α e hp hc b hb hsquareB R hR
        hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
        Jnative s y).symm.trans (congrFun (hJrep s) y))
  have hTnative (s : Parameter) : letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
      ∀ x, Tnative s x = ((endpoints s).tensor (Scomplete s x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (Scomplete s) x) := by
    let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    exact nativeTensor_restriction_of_inversePullback
      (completionManifold hδ (C s) (hemb s) (hC s) (hboundary s) (hinv s) (hzero s))
      Q.source.ambientManifold (Q.pair s).ambientManifold (Sref s)
      (Q.ambientCompletionPresentation s).equiv (Tnative s) (endpoints s).tensor
      (congrFun (hTrep s))
  refine ⟨endpoints, hJnative, hTnative, hJrep, hTrep, ?_⟩
  exact Q.exists_nativeGradedDeformation_of_originalTotalSection
    hdim α e hp hc b hb hsquareB R hR hsquareA hδ C hemb hC hboundary hinv hzero
    hjoint hmix hode q hqnative hqend Jnative PI PE σ
    hbp Λ hΛnative hΛcylinder hΛsmooth hnative hJI hJE hσ hnσ
    (endpoints parameterZero) (endpoints parameterOne) Q.completedSymplecticExtension
    Q.completedSymplecticExtension_apply (hJnative parameterZero) (hJnative parameterOne)
    (hTnative parameterZero) (hTnative parameterOne)

end FsFltz.Geometry.PairDeformation
