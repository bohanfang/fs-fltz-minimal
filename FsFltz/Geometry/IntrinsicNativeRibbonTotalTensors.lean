import FsFltz.Geometry.IntrinsicNativeRibbonTotalCovector
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalExterior
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVerticalField

/-!
# Spatial tensors on the original ribbon total atlas

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The same retained original ribbon comparison transports the spatial exterior
derivative and the form-determined Liouville field of its exact primitive.
The resulting native total two-form and tangent section are jointly smooth,
and restrict exactly to those original tensors on every spatial slice.
The two-form is the transported spatial derivative, not the total exterior
derivative of the parameterized covector. Real-open coefficient germs are
supplied separately.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

/-- The actual completed ribbon field in this deformation's fixed source
presentation, using the same presentation as `completedRibbonPrimitive`. -/
def completedRibbonField {n : ℕ} (Q : PairDeformation n) (t : Parameter)
    (x : Q.source.ribbonCompletion.ambient.manifold.Point) :
    Q.source.ribbonCompletion.ambient.manifold.Tangent x :=
  Q.source.ribbonCompletion.ambient.manifold.pullbackVectorField
    (Q.pair t).ribbonCompletion.ambient.manifold (Q.ribbonCompletionPresentation t).equiv
    (Q.pair t).ribbonCompletion.ambient.field x

/-- The actual reference completed field is determined by the same reference
primitive; primitive preservation proves its contraction equation. -/
theorem completedRibbonField_eq_liouvilleVector {n : ℕ} (Q : PairDeformation n)
    (t : Parameter) (x : Q.source.ribbonCompletion.ambient.manifold.Point) :
    Q.completedRibbonField t x =
      Q.source.ribbonCompletion.ambient.manifold.liouvilleVector
        (Q.completedRibbonPrimitive t) x := by
  let N := Q.source.ribbonCompletion.ambient.manifold
  let Y := (Q.pair t).ribbonCompletion.ambient
  exact (N.liouvilleVector_eq _ x
    (Y.nondegenerate_pullback_primitive N (Q.ribbonCompletionPresentation t).equiv x)
    (Y.liouvilleEquation_pullback_field N (Q.ribbonCompletionPresentation t).equiv x)).symm

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)

/-- Spatial naturality for the exact retained strict comparison. -/
theorem referenceEquiv_exteriorDerivative (t : Parameter) :
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).pullback Q.source.ribbonCompletion.ambient.manifold
        (S.referenceEquiv t)
        (Q.source.ribbonCompletion.ambient.manifold.exteriorDerivative
          (Q.completedRibbonPrimitive t)) =
      (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
        (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
        (S.collar_zero t)).exteriorDerivative (S.primitive t) := by
  let X := completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t)
  have hd := X.exteriorDerivative_pullback Q.source.ribbonCompletion.ambient.manifold
    ⟨S.referenceEquiv t, (S.referenceEquiv t).contMDiff⟩
    (Q.completedRibbonPrimitive t) (Q.completedRibbonPrimitive_smooth.slice t)
  change X.exteriorDerivative
    (X.pullback Q.source.ribbonCompletion.ambient.manifold
      (S.referenceEquiv t) (Q.completedRibbonPrimitive t)) = _ at hd
  rw [S.referenceEquiv_primitive t] at hd
  exact hd.symm

/-- The spatial restriction of the same total map transports the exact
spatial exterior derivative of the already selected original primitive. -/
theorem totalMap_slice_exteriorDerivative (t : Parameter) :
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).pullback Q.source.ribbonCompletion.ambient.manifold
        (S.totalMap ∘ sliceIn (fun t p => S.collar t p.val) t)
        (Q.source.ribbonCompletion.ambient.manifold.exteriorDerivative
          (Q.completedRibbonPrimitive t)) =
      (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
        (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
        (S.collar_zero t)).exteriorDerivative (S.primitive t) := by
  have he : S.totalMap ∘ sliceIn (fun t p => S.collar t p.val) t = S.referenceEquiv t := by
    funext x
    exact S.totalMap_sliceIn t x
  rw [he]
  exact S.referenceEquiv_exteriorDerivative t

/-- The retained slice comparison sends the original form-determined
Liouville vector to the actual reference field of this very deformation. -/
theorem map_liouvilleVector_referenceEquiv (hdim : k + 1 = 2 * n - 2)
    (t : Parameter)
    (x : Space (fun p : Half S.width (IntrinsicBoundary.Point k M) => S.collar t p.val)) :
    letI := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_boundary t) (S.collar_zero t)
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n - 2))
      (S.referenceEquiv t) x
      ((completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
        (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
        (S.collar_zero t)).liouvilleVector (S.primitive t) x) =
      Q.completedRibbonField t (S.referenceEquiv t x) := by
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  let X := completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t)
  rw [Q.completedRibbonField_eq_liouvilleVector]
  exact X.map_liouvilleVector_of_primitive_pullback
    Q.source.ribbonCompletion.ambient.manifold hdim (S.referenceEquiv t)
    (S.referenceEquiv t).contMDiff (S.primitive t) (Q.completedRibbonPrimitive t)
    (Q.completedRibbonPrimitive_smooth.slice t) (S.referenceEquiv_primitive t) x
    (S.primitive_nondegenerate t x)
    ((Q.pair t).ribbonCompletion.ambient.nondegenerate_pullback_primitive
      Q.source.ribbonCompletion.ambient.manifold (Q.ribbonCompletionPresentation t).equiv
      (S.referenceEquiv t x))

variable
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include RM hRM hsquare

/-- The canonical transported spatial two-form has smooth evaluation on
the native tangent-pair bundle. On every actual spatial slice it is exactly
the exterior derivative of the primitive retained by `S`. -/
theorem totalTwoForm_extension :
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    letI := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs
    let Ξ := nativeTotalTwoForm (familyModel (k + 1))
      Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap
      (fun t => Q.source.ribbonCompletion.ambient.manifold.exteriorDerivative
        (Q.completedRibbonPrimitive t))
    ContMDiff ((familyModel (k + 1)).prod
        𝓘(ℝ, (Model 1 × Model (k + 1)) × (Model 1 × Model (k + 1)))) 𝓘(ℝ, ℝ) ∞
      (fun v : TangentPairBundle (familyModel (k + 1)) (X := TotalSpace c) =>
        Ξ v.proj ![v.2.1, v.2.2]) ∧
      ∀ t,
        letI := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
          (S.collar_boundary t) (S.collar_zero t)
        ∀ x, (Ξ (sliceIn c t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x) =
            (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
              (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
              (S.collar_zero t)).exteriorDerivative (S.primitive t) x := by
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
  let N := Q.source.ribbonCompletion.ambient.manifold
  let η := fun t => N.exteriorDerivative (Q.completedRibbonPrimitive t)
  have hq := S.contMDiff_totalMap RM hRM hsquare
  refine ⟨contMDiff_nativeTotalTwoForm_eval (familyModel (k + 1)) N
    (parameter c) S.totalMap η
    (contMDiff_parameter S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) hq
    Q.completedRibbonPrimitive_smooth.exteriorDerivative, ?_⟩
  intro t
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  intro x
  rw [nativeTotalTwoForm_restrict (familyModel (k + 1))
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t))
    N (parameter c) S.totalMap η hq (sliceIn c t)
    (contMDiff_sliceIn S.width_pos S.collar S.collar_embedding S.collar_smooth
      S.collar_boundary S.collar_inverse S.collar_zero S.collar_joint_embedding S.mixed_germs t)
    t (parameter_sliceIn c t) x]
  exact congrFun (S.totalMap_slice_exteriorDerivative t) x

/-- The same total diffeomorphism transports the actual reference completed
field to a smooth native tangent section. Its exact spatial restriction is
the form-determined Liouville field of the retained original primitive. -/
theorem exists_totalField_extension_eq (hdim : k + 1 = 2 * n - 2) :
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    letI := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs
    ∃ V : (z : TotalSpace c) → TangentSpace (familyModel (k + 1)) z,
      V = pulledVerticalField Q.source.ribbonCompletion.ambient.manifold
        (S.totalDiffeomorph hdim RM hRM hsquare) Q.completedRibbonField ∧
      ContMDiff (familyModel (k + 1)) (familyModel (k + 1)).tangent ∞
        (fun z => (⟨z, V z⟩ : TangentBundle (familyModel (k + 1)) (TotalSpace c))) ∧
      ∀ t,
        letI := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
          (S.collar_boundary t) (S.collar_zero t)
        ∀ x, mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x
          ((completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
            (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
            (S.collar_zero t)).liouvilleVector (S.primitive t) x) = V (sliceIn c t x) := by
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
  let N := Q.source.ribbonCompletion.ambient.manifold
  let F := S.totalDiffeomorph hdim RM hRM hsquare
  refine ⟨pulledVerticalField N F Q.completedRibbonField, rfl,
    contMDiff_pulledVerticalField N F Q.completedRibbonField Q.completedRibbonField_smooth, ?_⟩
  intro t
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  let X := completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t)
  have hs := contMDiff_sliceIn S.width_pos S.collar S.collar_embedding S.collar_smooth
    S.collar_boundary S.collar_inverse S.collar_zero S.collar_joint_embedding S.mixed_germs t
  apply mfderiv_slice_pulledVerticalField N F Q.completedRibbonField X
    (sliceIn c t) hs (X.liouvilleVector (S.primitive t))
  intro x
  have he : F ∘ sliceIn c t = fun x => (t, S.referenceEquiv t x) := by
    funext y
    exact S.totalDiffeomorph_sliceIn hdim RM hRM hsquare t y
  rw [he]
  erw [mfderiv_prodMk (f := fun _ : X.Point => t) mdifferentiableAt_const
    ((S.referenceEquiv t).contMDiff.mdifferentiable (by simp) x)]
  change (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ 1) (fun _ : X.Point => t) x
      (X.liouvilleVector (S.primitive t) x),
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (S.referenceEquiv t) x
      (X.liouvilleVector (S.primitive t) x)) = _
  rw [mfderiv_const, zero_apply, S.map_liouvilleVector_referenceEquiv hdim,
    S.totalDiffeomorph_sliceIn]
  rfl

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
