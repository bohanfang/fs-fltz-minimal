import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseSmooth
import FsFltz.Geometry.IntrinsicCompletionFamilySlices
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyPrimitive

/-!
# The original completion slices and their exact diffeomorphisms

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
Restricting the parameter-preserving total comparison gives actual smooth
equivalences from the original completion slices. Their inverse smoothness
uses the already constructed original slice retractions, so neither a new
slice atlas nor slice compatibility is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section Equivalence

variable {T M B N : Type*} [TopologicalSpace T] [TopologicalSpace M]
  [TopologicalSpace B] {δ : ℝ} (c : T → Half δ B → M)
  (A : TotalSpace c ≃ T × N) (hparam : ∀ z, (A z).1 = parameter c z)

/-- Restriction to the original quotient slice of a parameter-preserving
equivalence. Its inverse lies in that exact parameter fiber. -/
def sliceEquivOfParameterEquiv (t : T) : Space (c t) ≃ N where
  toFun x := (A (sliceIn c t x)).2
  invFun y := (fiberEquiv c t).symm ⟨A.symm (t, y),
    (hparam _).symm.trans (congrArg Prod.fst (A.apply_symm_apply (t, y)))⟩
  left_inv x := by
    apply (fiberEquiv c t).injective
    apply Subtype.ext
    change ((fiberEquiv c t) ((fiberEquiv c t).symm _)).val = sliceIn c t x
    rw [Equiv.apply_symm_apply]
    change A.symm (t, (A (sliceIn c t x)).2) = sliceIn c t x
    have he : (t, (A (sliceIn c t x)).2) = A (sliceIn c t x) :=
      Prod.ext ((hparam _).trans (parameter_sliceIn c t x)).symm rfl
    rw [he, Equiv.symm_apply_apply]
  right_inv y := by
    have he := congrArg Subtype.val ((fiberEquiv c t).apply_symm_apply
      ⟨A.symm (t, y), (hparam _).symm.trans (congrArg Prod.fst (A.apply_symm_apply (t, y)))⟩)
    change (A (sliceIn c t ((fiberEquiv c t).symm _))).2 = y
    change sliceIn c t ((fiberEquiv c t).symm _) = A.symm (t, y) at he
    rw [he, Equiv.apply_symm_apply]

omit [TopologicalSpace M] in
@[simp] theorem sliceEquivOfParameterEquiv_apply (t : T) (x : Space (c t)) :
    sliceEquivOfParameterEquiv c A hparam t x = (A (sliceIn c t x)).2 := rfl

omit [TopologicalSpace M] in
/-- The inverse of the restricted equivalence is the actual total inverse
followed by the established original fiber equivalence. -/
@[simp] theorem sliceIn_sliceEquivOfParameterEquiv_symm (t : T) (y : N) :
    sliceIn c t ((sliceEquivOfParameterEquiv c A hparam t).symm y) = A.symm (t, y) :=
  congrArg Subtype.val ((fiberEquiv c t).apply_symm_apply
    ⟨A.symm (t, y), (hparam _).symm.trans (congrArg Prod.fst (A.apply_symm_apply (t, y)))⟩)

end Equivalence

section Smooth

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
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
  (N : SmoothManifold d)

include hC hboundary hinv hmix in
/-- A parameter-preserving smooth total equivalence restricts to an actual
diffeomorphism of every original completion slice, with its old atlas.
Inverse smoothness is reflected by the produced original slice retractions. -/
def sliceDiffeomorphOfParameterDiffeomorph
    (A : letI := totalFamilyChartedSpace hδ C hzero hjoint
      Diffeomorph (familyModel (k + 1)) (familyModel d)
        (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
        (Parameter × N.Point) ∞)
    (hparam : ∀ z, (A z).1 = parameter (fun t p => C t p.val) z) (t : Parameter) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
      (Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) N.Point ∞ := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let E := sliceEquivOfParameterEquiv c A.toEquiv hparam t
  refine { toEquiv := E, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact contMDiff_snd.comp (A.contMDiff.comp
      (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t))
  · apply (contMDiff_sliceIn_comp_iff hδ C hemb hC hboundary hinv hzero hjoint hmix t E.symm).mpr
    have h : sliceIn c t ∘ E.symm = fun y => A.symm (t, y) := by
      funext y
      exact sliceIn_sliceEquivOfParameterEquiv_symm c A.toEquiv hparam t y
    rw [h]
    exact A.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)

end Smooth

end FsFltz.Geometry.IntrinsicCompletionGluing

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
/-- The literal spatial restriction of the actual total comparison is a
diffeomorphism from the already constructed original completion slice to
the same fixed reference completion. -/
def ambientNativeSliceDiffeomorph (t : Parameter) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      (Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point ∞ :=
  sliceDiffeomorphOfParameterDiffeomorph hδ C hemb hC hboundary hinv hzero hjoint hmix
    (Q.pair parameterZero).ambientCompletion.ambient.manifold
    (Q.ambientNativeTotalDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hboundary hzero hjoint hmix hode q hqnative hqend)
    (fun _ => rfl) t

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- The new diffeomorphism is the same exact spatial quotient map. -/
@[simp] theorem ambientNativeSliceDiffeomorph_apply (t : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t x =
        q (sliceIn (fun t p => C t p.val) t x) := rfl

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- The inverse slice map includes to exactly the already proved total
inverse at the prescribed parameter, in the original total atlas. -/
@[simp] theorem sliceIn_ambientNativeSliceDiffeomorph_symm (t : Parameter)
    (y : (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    sliceIn (fun t p => C t p.val) t
      ((Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t).symm y) =
        (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (t, y) :=
  sliceIn_sliceEquivOfParameterEquiv_symm _ _ (fun _ => rfl) t y

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Composing the exact original slice map with the very same deformation's
completion presentation gives its actual completion diffeomorphism. -/
def ambientNativeSliceCompletionDiffeomorph (t : Parameter) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
      (Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
      (Q.pair t).ambientCompletion.ambient.manifold.Point ∞ := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  exact (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t).trans
      (Q.ambientCompletionPresentation t).equiv

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
@[simp] theorem ambientNativeSliceCompletionDiffeomorph_apply (t : Parameter)
    (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t x =
        (Q.ambientCompletionPresentation t).equiv
          (q (sliceIn (fun t p => C t p.val) t x)) := rfl

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Every original native point is preserved by the completion comparison. -/
theorem ambientNativeSliceCompletionDiffeomorph_native (t : Parameter) (x : M) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t
        (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val) x) =
          (Q.pair t).ambientCompletion.inclusion.map (e t x).val := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  change (Q.ambientCompletionPresentation t).equiv
    (q (sliceIn (fun t p => C t p.val) t (original (fun p => C t p.val) x))) = _
  rw [sliceIn_original, hqnative]
  exact (Q.ambientCompletionPresentation t).equiv.apply_symm_apply _

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- The exact completion comparison preserves the entire original cylinder,
including its inward collar and outward end, with the source boundary map. -/
theorem ambientNativeSliceCompletionDiffeomorph_cylinder (t : Parameter)
    (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
    Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t
        (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val) p) =
          (Q.pair t).ambientCompletion.endMap (b t p.val.2, -p.val.1) := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  change (Q.ambientCompletionPresentation t).equiv
    (q (sliceIn (fun t p => C t p.val) t (cylinder (fun p => C t p.val) p))) = _
  rw [sliceIn_cylinder, hqend]
  change (Q.ambientCompletionPresentation t).equiv
    ((Q.ambientCompletionPresentation t).equiv.symm
      ((Q.pair t).ambientCompletion.endMap
        ((Q.ambientPresentation t).boundaryEquiv (b parameterZero p.val.2), -p.val.1))) = _
  rw [Diffeomorph.apply_symm_apply, hsquareB]

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- The actual slice completion diffeomorphism preserves the produced
original primitive. This equality consumes its native and full-cylinder
restrictions, rather than assuming strictness of the comparison. -/
theorem ambientNativeSliceCompletionDiffeomorph_primitive
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
    (t : Parameter) :
    (completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)).pullback
      (Q.pair t).ambientCompletion.ambient.manifold
      (Q.ambientNativeSliceCompletionDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
        hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend t)
      (Q.pair t).ambientCompletion.ambient.primitive = Λ t := by
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let X := completionManifold hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t)
  have hqsmooth := Q.contMDiff_ambientNativeTotalMap hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hboundary hzero hjoint hmix hode q hqnative hqend
  have hqs := hqsmooth.comp (contMDiff_sliceIn hδ C hemb hC hboundary hinv hzero hjoint hmix t)
  change X.pullback (Q.pair t).ambientCompletion.ambient.manifold
    ((Q.ambientCompletionPresentation t).equiv ∘ (q ∘ sliceIn (fun t p => C t p.val) t))
    (Q.pair t).ambientCompletion.ambient.primitive = Λ t
  rw [X.pullback_comp (Q.pair parameterZero).ambientCompletion.ambient.manifold
    (Q.pair t).ambientCompletion.ambient.manifold
    (fun x => hqs.mdifferentiableAt (by simp))
    (fun x => (Q.ambientCompletionPresentation t).equiv.contMDiff.mdifferentiableAt (by simp))]
  exact Q.pullback_completedPrimitive_ambientNativeTotalMap α e hp b hbp hsquareB
    hδ C hemb hC hboundary hinv hzero hjoint hmix Λ hΛnative hΛcylinder
    q hqsmooth hqnative hqend t

end FsFltz.Geometry.PairDeformation
