import FsFltz.Geometry.IntrinsicNativeRibbonTotalCovector
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyCovectorAtlas

/-!
# Real open coefficients of the original ribbon primitive covector

Source: `geoemtric-part-fsf.tex`, smooth extension conventions, lines 119–122;
`def:pair`, lines 142–160; `def:chain`, lines 163–169; and `sec:lean`,
lines 788–814. The real interior and cylinder extensions of the already
retained total comparison give real open coefficient germs of its canonical
primitive covector in the original total atlas. All tangent directions,
including the parameter direction at both endpoints, are retained.
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
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include RM hRM hsquare

/-- The real extension of the retained ribbon comparison gives full real
covector coefficients on the entire original native interior patch. -/
theorem interiorCovector_coefficients :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    let Ω := nativeTotalCovector (familyModel (k + 1))
      Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive
    (IntrinsicInterior.smoothManifold k M).HasRealIntervalCovectorCoefficientsOn
      (fun p => (Ω (totalInterior c p)).compContinuousLinearMap
        (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalInterior c) p)) univ := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let P := IntrinsicInterior.smoothManifold k M
  let N := Q.source.ribbonCompletion.ambient.manifold
  obtain ⟨f, hf, hef⟩ := S.exists_realInteriorExtension RM hRM hsquare
  apply P.hasRealIntervalCovectorCoefficientsOn_of_realMap N
    (fun t x => f (t, x)) hf Q.completedRibbonPrimitive
    Q.completedRibbonPrimitive_smooth _ univ isOpen_univ
  intro p _
  rw [nativeTotalCovector_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) S.totalMap Q.completedRibbonPrimitive
    (S.contMDiff_totalMap RM hRM hsquare) (totalInterior c)
    (contMDiff_totalInterior S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) p]
  have hparam : parameter c ∘ totalInterior c = Prod.fst := by
    funext z
    rfl
  have he : S.totalMap ∘ totalInterior c =
      (fun p : Parameter × P.Point => f (p.1.val, p.2)) := by
    funext z
    exact (hef z.1 z.2).symm
  rw [hparam, he]

/-- The same covector has full real coefficients in its original cylinder
patch on a uniform seam/outward strip. Matching uses the entire cylinder
map differential, including its moving boundary and parameter components. -/
theorem exists_cylinderCovector_coefficients :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    let Ω := nativeTotalCovector (familyModel (k + 1))
      Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive
    ∃ a : ℝ, a < 0 ∧
      (bandManifold S.width (IntrinsicBoundary.smoothManifold k M)).HasRealIntervalCovectorCoefficientsOn
        (fun p => (Ω (totalCylinder c p)).compContinuousLinearMap
          (mfderiv (familyModel (k + 1)) (familyModel (k + 1)) (totalCylinder c) p))
        {p | a < -p.val.1} := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let P := bandManifold S.width (IntrinsicBoundary.smoothManifold k M)
  let N := Q.source.ribbonCompletion.ambient.manifold
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ := S.exists_realCylinderExtension RM hRM hsquare
  let f : ℝ → P.Point → N.Point := fun t p => β t (p.val.2, -p.val.1)
  have hf : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (2 * n - 2)) ∞ (fun p : ℝ × P.Point => f p.1 p.2) :=
    hβ.comp (contMDiff_fst.prodMk
      ((contMDiff_snd.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).prodMk
        (contMDiff_fst.comp ((contMDiff_band_val S.width).comp contMDiff_snd)).neg))
  have hA : IsOpen {p : P.Point | a < -p.val.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val).neg
  refine ⟨a, ha, P.hasRealIntervalCovectorCoefficientsOn_of_realMap N f hf
    Q.completedRibbonPrimitive Q.completedRibbonPrimitive_smooth _ _ hA ?_⟩
  intro p hpA
  rw [nativeTotalCovector_comp (familyModel (k + 1)) (familyModel (k + 1))
    N (parameter c) S.totalMap Q.completedRibbonPrimitive
    (S.contMDiff_totalMap RM hRM hsquare) (totalCylinder c)
    (contMDiff_totalCylinder S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) p]
  have hparam : parameter c ∘ totalCylinder c = Prod.fst := by
    funext z
    exact parameter_totalCylinder c z
  rw [hparam]
  have he : S.totalMap ∘ totalCylinder c =ᶠ[𝓝 p]
      (fun z : Parameter × P.Point => f z.1.val z.2) := by
    have hn : ∀ᶠ z : Parameter × P.Point in 𝓝 p, z.2 ∈ {p : P.Point | a < -p.val.1} :=
      continuous_snd.continuousAt.preimage_mem_nhds (hA.mem_nhds hpA)
    filter_upwards [hn] with z hz
    exact (heβ z.1 z.2 hz).symm
  have hvalue := he.eq_of_nhds
  have hderiv := he.mfderiv_eq (I := familyModel (k + 1)) (I' := 𝓘(ℝ, Model (2 * n - 2)))
  have hd : mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
      (S.totalMap ∘ totalCylinder c) p =
        mfderiv (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
          (fun z : Parameter × P.Point => f z.1.val z.2) p := by
    ext v
    exact congrArg (fun L : TangentSpace (familyModel (k + 1)) p →L[ℝ] Model (2 * n - 2) => L v)
      hderiv
  change S.totalMap (totalCylinder c p) = f p.1.val p.2 at hvalue
  ext vs
  dsimp only [nativeTotalCovector, Function.comp_def]
  erw [hvalue, hd]

/-- Every point of the original ribbon total atlas admits an actual chart
whose coefficients for its canonical primitive covector extend smoothly
to a real open neighborhood. The covector is exactly the existing one,
and the chart identity covers its full native tangent fiber. -/
theorem hasRealOpenCovectorCoefficients_totalCovector :
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    HasRealOpenCovectorCoefficients (familyModel (k + 1))
      (nativeTotalCovector (familyModel (k + 1))
        Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap
        Q.completedRibbonPrimitive) := by
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) S.width
  obtain ⟨a, ha, hCylinder⟩ := S.exists_cylinderCovector_coefficients RM hRM hsquare
  exact hasRealOpenCovectorCoefficients_totalFamily_of_patches S.width_pos S.collar
    S.collar_boundary S.collar_zero S.collar_joint_embedding S.mixed_germs a ha
    _ (S.interiorCovector_coefficients RM hRM hsquare) hCylinder

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
