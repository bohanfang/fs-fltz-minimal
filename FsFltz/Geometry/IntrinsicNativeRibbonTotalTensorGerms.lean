import FsFltz.Geometry.IntrinsicNativeRibbonTotalTensors
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyExteriorGerms
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFieldGerms

/-!
# Real-open spatial tensor coefficients on the original ribbon atlas

Source: `geoemtric-part-fsf.tex`, smoothness conventions, lines 119–128;
`def:pair`, lines 132–160; `def:chain`, lines 163–169; and `sec:lean`,
lines 784–827. These are coefficient producers for the spatial exterior
derivative and Liouville field of the same retained ribbon comparison.
The real extensions are jointly smooth in the parameter and spatial chart
variables on real open neighborhoods, including both interval endpoints.
The native interior and a cylinder strip containing the seam and every
outward radius cover the original completion. The spatial two-form is
pulled back with its full total differential, retaining parameter components.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
open SmoothManifold IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → IntrinsicLiouville.Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include RM hRM hsquare

/-- Full real-open coefficients of the original ribbon's canonical spatial
two-form on its entire native interior. The coefficients include every
parameter and spatial tangent direction. -/
theorem interiorTwoForm_coefficients :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    let N := Q.source.ribbonCompletion.ambient.manifold
    let Ξ := nativeTotalTwoForm (familyModel (k + 1)) N (parameter c) S.totalMap
      (fun t => N.exteriorDerivative (Q.completedRibbonPrimitive t))
    (IntrinsicInterior.smoothManifold k M).HasRealIntervalTwoFormCoefficientsOn
      (fun p => (Ξ (totalInterior c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ribbonCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedRibbonPrimitive t)
  obtain ⟨f₀, hf₀, hef⟩ := S.exists_realInteriorExtension RM hRM hsquare
  let f : ℝ → P.Point → N.Point := fun t x => f₀ (t, x)
  apply P.hasRealIntervalTwoFormCoefficientsOn_of_realMap N f hf₀
    η Q.completedRibbonPrimitive_smooth.exteriorDerivative _ univ isOpen_univ
  intro p _
  rw [nativeTotalTwoForm_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) S.totalMap η (S.contMDiff_totalMap RM hRM hsquare) (totalInterior c)
    (contMDiff_totalInterior S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) p]
  have hparam : parameter c ∘ totalInterior c = Prod.fst := by
    funext z
    rfl
  have he : S.totalMap ∘ totalInterior c =
      (fun p : Parameter × P.Point => f p.1.val p.2) := by
    funext p
    exact (hef p.1 p.2).symm
  rw [hparam, he]

/-- Full real-open coefficients of the same spatial two-form on a genuine
seam and outward cylinder strip. The cutoff is negative, so the strip
contains a spatial neighborhood of the seam. -/
theorem exists_cylinderTwoForm_coefficients :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    let N := Q.source.ribbonCompletion.ambient.manifold
    let Ξ := nativeTotalTwoForm (familyModel (k + 1)) N (parameter c) S.totalMap
      (fun t => N.exteriorDerivative (Q.completedRibbonPrimitive t))
    ∃ a : ℝ, a < 0 ∧
      (bandManifold S.width (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalTwoFormCoefficientsOn
        (fun p => (Ξ (totalCylinder c p)).compContinuousLinearMap
          (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
        {p | a < -p.val.1} := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let P := bandManifold S.width (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ribbonCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedRibbonPrimitive t)
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ := S.exists_realCylinderExtension RM hRM hsquare
  let f : ℝ → P.Point → N.Point := fun t p => β t (p.val.2, -p.val.1)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n - 2)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hβ.comp (contMDiff_fst.prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).neg))
  have hA : IsOpen {p : P.Point | a < -p.val.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).neg
  refine ⟨a, ha, P.hasRealIntervalTwoFormCoefficientsOn_of_realMap N f hf
    η Q.completedRibbonPrimitive_smooth.exteriorDerivative _ _ hA ?_⟩
  intro p hpA
  rw [nativeTotalTwoForm_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) S.totalMap η (S.contMDiff_totalMap RM hRM hsquare) (totalCylinder c)
    (contMDiff_totalCylinder S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) p]
  have hparam : parameter c ∘ totalCylinder c = Prod.fst := by
    funext z
    exact parameter_totalCylinder c z
  rw [hparam]
  have he : S.totalMap ∘ totalCylinder c =ᶠ[𝓝 p]
      (fun z : Parameter × P.Point => f z.1.val z.2) := by
    have hn : ∀ᶠ z : Parameter × P.Point in 𝓝 p,
        z.2 ∈ {p : P.Point | a < -p.val.1} :=
      continuous_snd.continuousAt.preimage_mem_nhds (hA.mem_nhds hpA)
    filter_upwards [hn] with z hz
    exact (heβ z.1 z.2 hz).symm
  have hvalue := he.eq_of_nhds
  have hderiv := he.mfderiv_eq (I := familyModel (k + 1))
    (I' := 𝓘(ℝ, Model (2 * n - 2)))
  have hd : mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
      (S.totalMap ∘ totalCylinder c) p =
      mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
        (fun z : Parameter × P.Point => f z.1.val z.2) p := by
    ext v
    exact congrArg (fun L : TangentSpace (familyModel (k + 1)) p →L[ℝ]
      Model (2 * n - 2) => L v) hderiv
  change S.totalMap (totalCylinder c p) = f p.1.val p.2 at hvalue
  ext vs
  dsimp only [nativeTotalTwoForm, Function.comp_def]
  erw [hvalue, hd]

/-- Real-open coefficients of the actual transported ribbon Liouville
field on the entire native interior. The real coefficient family maps to
the exact same total field by the actual interior patch differential. -/
theorem interiorField_coefficients (hdim : k + 1 = 2 * n - 2) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    HasRealFieldCoefficientsInPatch (IntrinsicInterior.smoothManifold k M)
      (pulledVerticalField Q.source.ribbonCompletion.ambient.manifold
        (S.totalDiffeomorph hdim RM hRM hsquare) Q.completedRibbonField)
      (totalInterior c) := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ribbonCompletion.ambient.manifold
  let F := S.totalDiffeomorph hdim RM hRM hsquare
  obtain ⟨f₀, hf₀, hef⟩ := S.exists_realInteriorExtension RM hRM hsquare
  let f : ℝ → P.Point → N.Point := fun t x => f₀ (t, x)
  have hsquareF : ∀ p : Parameter × P.Point, F (totalInterior c p) =
      (p.1, f p.1.val p.2) := by
    intro p
    exact Prod.ext rfl (hef p.1 p.2).symm
  apply hasRealFieldCoefficientsInPatch_of_realMap P N hdim F
    Q.completedRibbonPrimitive Q.completedRibbonPrimitive_smooth
    (fun t x => (Q.pair t).ribbonCompletion.ambient.nondegenerate_pullback_primitive
      N (Q.ribbonCompletionPresentation t).equiv x)
    Q.completedRibbonField Q.completedRibbonField_eq_liouvilleVector (totalInterior c)
    (contMDiff_totalInterior S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) f hf₀ hsquareF
  intro t x
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  have he : f t.val = S.referenceEquiv t ∘ interiorIn (c t) := by
    funext y
    exact (hef t y).trans (S.totalMap_sliceIn t (interiorIn (c t) y))
  rw [he, mfderiv_comp x
    ((S.referenceEquiv t).contMDiff.mdifferentiable (by simp) _)
    ((contMDiff_completionInterior S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).mdifferentiable (by simp) x)]
  exact ((S.referenceEquiv t).mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
    (bijective_mfderiv_completionInterior S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t) x)

/-- Real-open coefficients of the same actual transported Liouville field
on a cylinder strip containing the seam and every outward radius. Spatial
invertibility follows from the retained strict slice comparison and the
original cylinder chart, rather than an extra hypothesis on a real map. -/
theorem exists_cylinderField_coefficients (hdim : k + 1 = 2 * n - 2) :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    ∃ a : ℝ, a < 0 ∧
      HasRealFieldCoefficientsInPatch
        ((bandManifold S.width (IntrinsicBoundary.smoothManifold k M)).restrict
          (fieldCylinderStrip S.width (IntrinsicBoundary.smoothManifold k M) a))
        (pulledVerticalField Q.source.ribbonCompletion.ambient.manifold
          (S.totalDiffeomorph hdim RM hRM hsquare) Q.completedRibbonField)
        (fun p => totalCylinder c (p.1, p.2.val)) := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let B := bandManifold S.width (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ribbonCompletion.ambient.manifold
  let F := S.totalDiffeomorph hdim RM hRM hsquare
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ := S.exists_realCylinderExtension RM hRM hsquare
  let U := fieldCylinderStrip S.width (IntrinsicBoundary.smoothManifold k M) a
  let P := B.restrict U
  let f₀ : ℝ → B.Point → N.Point := fun t p => β t (p.val.2, -p.val.1)
  have hf₀ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n - 2)) ∞ (fun p : ℝ × B.Point => f₀ p.1 p.2) :=
    hβ.comp (contMDiff_fst.prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).neg))
  let f : ℝ → P.Point → N.Point := fun t p => f₀ t p.val
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n - 2)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hf₀.comp (contMDiff_id.prodMap contMDiff_subtype_val)
  let j : Parameter × P.Point → TotalSpace c := fun p => totalCylinder c (p.1, p.2.val)
  have hj : ContMDiff (familyModel (k + 1)) (familyModel (k + 1)) ∞ j :=
    (contMDiff_totalCylinder S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs).comp
        (contMDiff_id.prodMap contMDiff_subtype_val)
  have hsquareF : ∀ p : Parameter × P.Point, F (j p) = (p.1, f p.1.val p.2) := by
    intro p
    refine Prod.ext (parameter_totalCylinder c (p.1, p.2.val)) ?_
    exact (heβ p.1 p.2.val p.2.property).symm
  refine ⟨a, ha, hasRealFieldCoefficientsInPatch_of_realMap P N hdim F
    Q.completedRibbonPrimitive Q.completedRibbonPrimitive_smooth
    (fun t x => (Q.pair t).ribbonCompletion.ambient.nondegenerate_pullback_primitive
      N (Q.ribbonCompletionPresentation t).equiv x)
    Q.completedRibbonField Q.completedRibbonField_eq_liouvilleVector j hj f hf hsquareF ?_⟩
  intro t x
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  have he : f t.val = (S.referenceEquiv t ∘ cylinder (c t)) ∘
      (Subtype.val : U → B.Point) := by
    funext y
    exact (heβ t y.val y.property).trans (S.totalMap_cylinder t y.val)
  have hS : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞
      (S.referenceEquiv t ∘ cylinder (c t)) :=
    (S.referenceEquiv t).contMDiff.comp
      (contMDiff_cylinder S.width_pos (S.collar t) (S.collar_embedding t)
        (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t))
  have hd : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (f t.val) x =
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
        (S.referenceEquiv t ∘ cylinder (c t)) x.val := by
    rw [he]
    exact B.mfderiv_comp_restrict_val N U x (hS.mdifferentiableAt (by simp))
  rw [hd, mfderiv_comp x.val ((S.referenceEquiv t).contMDiff.mdifferentiable (by simp) _)
    ((contMDiff_cylinder S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).mdifferentiable (by simp) x.val)]
  exact ((S.referenceEquiv t).mfderivToContinuousLinearEquiv (by simp) _).bijective.comp
    (bijective_mfderiv_cylinder S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t) x.val)

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
