import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalField
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorGerms
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalExterior
import FsFltz.Geometry.SmoothFormOpenGluing

/-!
# Real open field coefficients on original completion patches

Source: `geoemtric-part-fsf.tex`, smoothness conventions, lines 119–122;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
Real extensions of the reference primitive and the actual patch maps produce
real smooth coefficients of the same transported tangent field. Invertibility
is needed only at interval points; the open inversion neighborhood is produced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section RealPatch
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {a d : ℕ} (P : SmoothManifold a) (N : SmoothManifold d)

/-- Real coefficient extensions of a zero-parameter field in an actual
interval-product patch of the original total atlas. The equality uses the
full differential of the specified patch, including the parameter endpoints. -/
def HasRealFieldCoefficientsInPatch
    (V : (z : X) → TangentSpace I z) (j : Parameter × P.Point → X) : Prop :=
  ∃ W : (s : ℝ) → (x : P.Point) → P.Tangent x,
    P.IsSmoothVectorFieldFamily W ∧
    ∀ (t : Parameter) (x : P.Point),
      mfderiv (familyModel a) I j (t, x) (0, W t.val x) = V (j (t, x))

omit [IsManifold I ∞ X] in
/-- An actual real spatial patch map and a real-extendible reference primitive
produce real-open coefficients of the same field pulled through the total
diffeomorphism. Spatial invertibility is required only on the interval. -/
theorem hasRealFieldCoefficientsInPatch_of_realMap
    (hdim : a = d)
    (F : Diffeomorph I (familyModel d) X (Parameter × N.Point) ∞)
    (α : Parameter → N.Form 1) (hα : N.IsSmoothIntervalFormFamily α)
    (hnd : ∀ t x, N.Nondegenerate (N.exteriorDerivative (α t)) x)
    (Z : (t : Parameter) → (x : N.Point) → N.Tangent x)
    (hZ : ∀ t x, Z t x = N.liouvilleVector (α t) x)
    (j : Parameter × P.Point → X) (hj : ContMDiff (familyModel a) I ∞ j)
    (f : ℝ → P.Point → N.Point)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model a)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × P.Point => f p.1 p.2))
    (hsquare : ∀ p : Parameter × P.Point, F (j p) = (p.1, f p.1.val p.2))
    (hbij : ∀ (t : Parameter) x,
      Function.Bijective (mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) (f t.val) x)) :
    HasRealFieldCoefficientsInPatch P (pulledVerticalField N F Z) j := by
  let β : Parameter → P.Form 1 := fun t => P.pullback N (f t.val) (α t)
  have hβ : P.IsSmoothIntervalFormFamily β :=
    P.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family N f hf α hα
  have hfs (t : ℝ) : ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hβnd : ∀ t x, P.Nondegenerate (P.exteriorDerivative (β t)) x := by
    intro t x
    exact P.nondegenerate_exteriorDerivative_pullback N (f t.val) (hfs t.val)
      (α t) (hα.slice t) x (hbij t x) (hnd t (f t.val x))
  obtain ⟨W, hW, heW⟩ := P.isSmoothIntervalVectorFieldFamily_liouvilleVector β hβ hβnd
  refine ⟨W, hW, ?_⟩
  intro t x
  let s : P.Point → X := fun y => j (t, y)
  have hs : ContMDiff 𝓘(ℝ, Model a) I ∞ s :=
    hj.comp (contMDiff_const.prodMk contMDiff_id)
  have hmap : ∀ y, mfderiv 𝓘(ℝ, Model a) (familyModel d) (F ∘ s) y
      (P.liouvilleVector (β t) y) = (0, Z (F (s y)).1 (F (s y)).2) := by
    intro y
    have he : F ∘ s = fun y => (t, f t.val y) := funext (fun y => hsquare (t, y))
    rw [he]
    erw [mfderiv_prodMk mdifferentiableAt_const ((hfs t.val).mdifferentiable (by simp) y),
      mfderiv_const]
    change (0, mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model d) (f t.val) y
      (P.liouvilleVector (β t) y)) = _
    rw [P.map_liouvilleVector_of_primitive_pullback N hdim (f t.val) (hfs t.val)
      (β t) (α t) (hα.slice t) rfl y (hβnd t y) (hnd t (f t.val y)), hsquare (t, y), hZ]
  have h := mfderiv_slice_pulledVerticalField N F Z P s hs
    (P.liouvilleVector (β t)) hmap x
  have hd := mfderiv_comp x (hj.mdifferentiable (by simp) (t, x))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  change mfderiv 𝓘(ℝ, Model a) I (j ∘ fun y : P.Point => (t, y)) x = _ at hd
  rw [mfderiv_prod_right] at hd
  rw [heW t]
  exact (congrArg (fun L => L (P.liouvilleVector (β t) x)) hd).symm.trans h

end RealPatch

/-- The original cylinder restricted to a seam and outward strip. The
negative cutoff leaves a real neighborhood of the completion seam. -/
def fieldCylinderStrip {k : ℕ} (δ : ℝ) (B : SmoothManifold k) (a : ℝ) :
    TopologicalSpace.Opens (bandManifold δ B).Point :=
  ⟨{p | a < -p.val.1},
    isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).neg⟩

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open SmoothManifold IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n)
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞
    (C t) (Half δ (IntrinsicBoundary.Point k M)))
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
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    Q.source.ambientCompletion.ambient.manifold.Point)
  (F : letI := totalFamilyChartedSpace hδ C hzero hjoint
    Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
      (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
      (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) ∞)
  (hF : ∀ z, F z = (parameter (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) z, q z))

omit [NeZero n] in
/-- The actual reference completed primitive determines its actual pulled
Liouville field, with no separate equation supplied by the caller. -/
theorem completedAmbientField_eq_liouvilleVector (t : Parameter)
    (x : Q.source.ambientCompletion.ambient.manifold.Point) :
    Q.source.ambientCompletion.ambient.manifold.pullbackVectorField
      (Q.pair t).ambientCompletion.ambient.manifold
      (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field x =
        Q.source.ambientCompletion.ambient.manifold.liouvilleVector (Q.completedPrimitive t) x := by
  let N := Q.source.ambientCompletion.ambient.manifold
  let Y := (Q.pair t).ambientCompletion.ambient
  exact (N.liouvilleVector_eq _ x
    (Y.nondegenerate_pullback_primitive N (Q.ambientCompletionPresentation t).equiv x)
    (Y.liouvilleEquation_pullback_field N (Q.ambientCompletionPresentation t).equiv x)).symm

include hemb hC hboundary hinv hzero hjoint hmix hF in
/-- Real-open coefficients of the same original total Liouville field on
its entire original native interior patch. The real compact map supplies
the endpoint extension; its interval differential is the actual slice map. -/
theorem ambientNativeInteriorField_coefficients
    (hdim : k + 1 = 2 * n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    (hqnative : ∀ t x,
      q (original (totalCollar (fun t p => C t p.val)) (t, x)) =
        Q.ambientNativeReferenceMap e t x) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    let N := Q.source.ambientCompletion.ambient.manifold
    let Z := fun t => N.pullbackVectorField (Q.pair t).ambientCompletion.ambient.manifold
      (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field
    HasRealFieldCoefficientsInPatch (IntrinsicInterior.smoothManifold k M)
      (pulledVerticalField N F Z) (totalInterior c) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ambientCompletion.ambient.manifold
  let Z := fun t => N.pullbackVectorField (Q.pair t).ambientCompletion.ambient.manifold
    (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field
  let f₀ : M → N.Point := fun x => Q.source.ambientCompletion.inclusion.map (e parameterZero x).val
  have hf₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞ f₀ :=
    Q.source.ambientCompletion.inclusion.map.contMDiff.comp
      (Q.source.ambientDomain.domain.contMDiff_subtype_val.comp (e parameterZero).contMDiff)
  let f : ℝ → P.Point → N.Point := fun t x => f₀ (R t x.val)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hf₀.comp (hR.1.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val))
  have hsquare : ∀ p : Parameter × P.Point, F (totalInterior c p) = (p.1, f p.1.val p.2) := by
    intro p
    rw [hF]
    refine Prod.ext ?_ ?_
    · rfl
    exact (hqnative p.1 p.2.val).trans
      (Q.ambientNativeReferenceMap_eq_compact e R hsquareA p.1 p.2.val)
  apply hasRealFieldCoefficientsInPatch_of_realMap P N hdim F
    Q.completedPrimitive Q.completedAmbientPrimitive_smooth
    (fun t x => (Q.pair t).ambientCompletion.ambient.nondegenerate_pullback_primitive
      N (Q.ambientCompletionPresentation t).equiv x)
    Z Q.completedAmbientField_eq_liouvilleVector (totalInterior c)
    (contMDiff_totalInterior hδ C hboundary hzero hjoint hmix) f hf hsquare
  intro t x
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let S := sliceDiffeomorphOfParameterDiffeomorph hδ C hemb hC hboundary hinv hzero hjoint hmix
    N F (fun z => congrArg Prod.fst (hF z)) t
  have he : f t.val = S ∘ interiorIn (c t) := by
    funext y
    change f t.val y = (F (sliceIn c t (interiorIn (c t) y))).2
    change f t.val y = (F (totalInterior c (t, y))).2
    rw [hsquare]
  rw [he, mfderiv_comp x
    (S.mdifferentiable (by simp) _)
    ((contMDiff_completionInterior hδ (C t) (hemb t) (hC t) (hboundary t)
      (hinv t) (hzero t)).mdifferentiable (by simp) x)]
  exact (S.mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
    (bijective_mfderiv_completionInterior hδ (C t) (hemb t) (hC t) (hboundary t)
      (hinv t) (hzero t) x)

include hemb hC hboundary hinv hzero hjoint hmix hF in
/-- The actual cylinder admits real-open coefficients of the same total
field on a seam and outward strip. The real cylinder comparison supplies
the extension, while the original slice differential supplies invertibility. -/
theorem exists_ambientNativeCylinderField_coefficients
    (hdim : k + 1 = 2 * n)
    (α : Parameter → IntrinsicLiouville.Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, IntrinsicLiouville.HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -IntrinsicLiouville.liouvilleVector (α t)
        (IntrinsicLiouville.exteriorDerivative (α t)) z) (Ico 0 δ))
    (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      q (totalCylinder (fun t p => C t p.val) (t, p)) =
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    let N := Q.source.ambientCompletion.ambient.manifold
    let Z := fun t => N.pullbackVectorField (Q.pair t).ambientCompletion.ambient.manifold
      (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field
    ∃ a : ℝ, a < 0 ∧
      HasRealFieldCoefficientsInPatch
        ((bandManifold δ (IntrinsicBoundary.smoothManifold k M)).restrict
          (fieldCylinderStrip δ (IntrinsicBoundary.smoothManifold k M) a))
        (pulledVerticalField N F Z)
        (fun p => totalCylinder c (p.1, p.2.val)) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let := totalFamily_isManifold hδ C hboundary hzero hjoint hmix
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let B := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ambientCompletion.ambient.manifold
  let Z := fun t => N.pullbackVectorField (Q.pair t).ambientCompletion.ambient.manifold
    (Q.ambientCompletionPresentation t).equiv (Q.pair t).ambientCompletion.ambient.field
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquareB C hode hzero
  let U := fieldCylinderStrip δ (IntrinsicBoundary.smoothManifold k M) a
  let P := B.restrict U
  let f₀ : ℝ → B.Point → N.Point := fun t p => β t (p.val.2, -p.val.1)
  have hf₀ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × B.Point => f₀ p.1 p.2) :=
    hβ.comp (contMDiff_fst.prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val δ).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val δ).comp contMDiff_snd)).neg))
  let f : ℝ → P.Point → N.Point := fun t p => f₀ t p.val
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hf₀.comp (contMDiff_id.prodMap contMDiff_subtype_val)
  let j : Parameter × P.Point → TotalSpace c := fun p => totalCylinder c (p.1, p.2.val)
  have hj : ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ j :=
    (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix).comp
      (contMDiff_id.prodMap contMDiff_subtype_val)
  have hsquare : ∀ p : Parameter × P.Point, F (j p) = (p.1, f p.1.val p.2) := by
    intro p
    rw [hF]
    refine Prod.ext (parameter_totalCylinder c (p.1, p.2.val)) ?_
    exact (hqend p.1 p.2.val).trans
      (heβ p.1 p.2.val.val.2 (-p.2.val.val.1) p.2.property).symm
  refine ⟨a, ha, hasRealFieldCoefficientsInPatch_of_realMap P N hdim F
    Q.completedPrimitive Q.completedAmbientPrimitive_smooth
    (fun t x => (Q.pair t).ambientCompletion.ambient.nondegenerate_pullback_primitive
      N (Q.ambientCompletionPresentation t).equiv x)
    Z Q.completedAmbientField_eq_liouvilleVector j hj f hf hsquare ?_⟩
  intro t x
  let := completionChartedSpace hδ (C t) (hemb t) (hboundary t) (hzero t)
  let S := sliceDiffeomorphOfParameterDiffeomorph hδ C hemb hC hboundary hinv hzero hjoint hmix
    N F (fun z => congrArg Prod.fst (hF z)) t
  have he : f t.val = (S ∘ cylinder (c t)) ∘ (Subtype.val : U → B.Point) := by
    funext y
    change f t.val y = (F (sliceIn c t (cylinder (c t) y.val))).2
    rw [sliceIn_cylinder]
    exact (congrArg Prod.snd (hsquare (t, y))).symm
  have hS : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (S ∘ cylinder (c t)) :=
    S.contMDiff.comp (contMDiff_cylinder hδ (C t) (hemb t) (hC t) (hboundary t)
      (hinv t) (hzero t))
  have hd : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n)) (f t.val) x =
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n))
        (S ∘ cylinder (c t)) x.val := by
    rw [he]
    exact B.mfderiv_comp_restrict_val N U x (hS.mdifferentiableAt (by simp))
  rw [hd, mfderiv_comp x.val (S.mdifferentiable (by simp) _)
      ((contMDiff_cylinder hδ (C t) (hemb t) (hC t) (hboundary t)
        (hinv t) (hzero t)).mdifferentiable (by simp) x.val)]
  exact (S.mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
    (bijective_mfderiv_cylinder hδ (C t) (hemb t) (hC t) (hboundary t)
      (hinv t) (hzero t) x.val)

end FsFltz.Geometry.PairDeformation
