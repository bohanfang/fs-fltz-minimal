import FsFltz.Geometry.IntrinsicNativeRibbonTotalComparisonInverse
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyVertical

/-!
# The exact primitive covector on the original ribbon total atlas

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The retained strict ribbon comparison pulls the same deformation's reference
primitive back to the already selected original slice primitive. The existing
native total covector construction then gives an actual jointly smooth
covector on the original total tangent bundle, with that exact spatial slice
restriction. Parameter components are allowed. Real coefficient extensions,
the spatial exterior derivative and Liouville field are separate producers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

/-- The completed ribbon primitive in the fixed source presentation of
this very deformation. Its interval regularity is retained by `Q`. -/
def completedRibbonPrimitive {n : ℕ} (Q : PairDeformation n) (t : Parameter) :
    Q.source.ribbonCompletion.ambient.manifold.Form 1 :=
  Q.source.ribbonCompletion.ambient.manifold.pullback
    (Q.pair t).ribbonCompletion.ambient.manifold (Q.ribbonCompletionPresentation t).equiv
    (Q.pair t).ribbonCompletion.ambient.primitive

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)

/-- The exact retained reference comparison preserves the already chosen
primitive after transport through the same completion presentation. -/
theorem referenceEquiv_primitive (t : Parameter) :
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).pullback Q.source.ribbonCompletion.ambient.manifold
        (S.referenceEquiv t) (Q.completedRibbonPrimitive t) = S.primitive t := by
  let X := completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t)
  change X.pullback Q.source.ribbonCompletion.ambient.manifold
    ((Q.ribbonCompletionPresentation t).equiv.symm ∘ S.comparison t)
    (Q.source.ribbonCompletion.ambient.manifold.pullback
      (Q.pair t).ribbonCompletion.ambient.manifold (Q.ribbonCompletionPresentation t).equiv
      (Q.pair t).ribbonCompletion.ambient.primitive) = S.primitive t
  rw [X.pullback_comp (Q.pair t).ribbonCompletion.ambient.manifold
    Q.source.ribbonCompletion.ambient.manifold
    (fun x => (S.comparison t).contMDiff.mdifferentiableAt (by simp))
    (fun x => (Q.ribbonCompletionPresentation t).equiv.symm.contMDiff.mdifferentiableAt (by simp))]
  have hc := (Q.pair parameterZero).ribbonCompletion.ambient.manifold.pullback_symm_pullback
    (Q.pair t).ribbonCompletion.ambient.manifold (Q.ribbonCompletionPresentation t).equiv
    (Q.pair t).ribbonCompletion.ambient.primitive
  exact (congrArg (X.pullback (Q.pair t).ribbonCompletion.ambient.manifold (S.comparison t)) hc).trans
    (S.comparison_primitive t)

/-- The spatial restriction of the same total map pulls the reference
ribbon primitive back to the exact original completion primitive. -/
theorem totalMap_slice_primitive (t : Parameter) :
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).pullback Q.source.ribbonCompletion.ambient.manifold
        (S.totalMap ∘ sliceIn (fun t p => S.collar t p.val) t)
        (Q.completedRibbonPrimitive t) = S.primitive t := by
  have he : S.totalMap ∘ sliceIn (fun t p => S.collar t p.val) t = S.referenceEquiv t := by
    funext x
    exact S.totalMap_sliceIn t x
  rw [he]
  exact S.referenceEquiv_primitive t

variable
  (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
  (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
    (eMs parameterZero (RM t.val x)).val = (eMs t x).val)

include RM hRM hsquare

/-- The original ribbon total tangent bundle carries its canonical actual
smooth covector. Its restriction to every original spatial tangent fiber
is exactly the primitive retained by `S`, at every interval parameter. -/
theorem exists_totalCovector_extension_eq :
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    letI := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
    letI := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs
    ∃ Ω : (z : TotalSpace c) → TangentSpace (familyModel (k + 1)) z [⋀^Fin 1]→L[ℝ] ℝ,
      Ω = nativeTotalCovector (familyModel (k + 1))
        Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive ∧
      ContMDiff (familyModel (k + 1)).tangent 𝓘(ℝ, ℝ) ∞
        (fun v : TangentBundle (familyModel (k + 1)) (TotalSpace c) => Ω v.proj (fun _ => v.2)) ∧
      ∀ t,
        letI := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
          (S.collar_boundary t) (S.collar_zero t)
        ∀ x, (Ω (sliceIn c t x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, Model (k + 1)) (familyModel (k + 1)) (sliceIn c t) x) =
            S.primitive t x := by
  let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
  let := totalFamilyChartedSpace S.width_pos S.collar S.collar_zero S.collar_joint_embedding
  let := totalFamily_isManifold S.width_pos S.collar S.collar_boundary
    S.collar_zero S.collar_joint_embedding S.mixed_germs
  let Ω := nativeTotalCovector (familyModel (k + 1))
    Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive
  have hq := S.contMDiff_totalMap RM hRM hsquare
  refine ⟨Ω, rfl, contMDiff_nativeTotalCovector_eval (familyModel (k + 1))
    Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive
    (contMDiff_parameter S.width_pos S.collar S.collar_boundary
      S.collar_zero S.collar_joint_embedding S.mixed_germs) hq Q.completedRibbonPrimitive_smooth, ?_⟩
  intro t
  let := completionChartedSpace S.width_pos (S.collar t) (S.collar_embedding t)
    (S.collar_boundary t) (S.collar_zero t)
  intro x
  rw [nativeTotalCovector_restrict (familyModel (k + 1))
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t) (S.collar_zero t))
    Q.source.ribbonCompletion.ambient.manifold (parameter c) S.totalMap Q.completedRibbonPrimitive hq
    (sliceIn c t) (contMDiff_sliceIn S.width_pos S.collar S.collar_embedding S.collar_smooth
      S.collar_boundary S.collar_inverse S.collar_zero S.collar_joint_embedding S.mixed_germs t)
    t (parameter_sliceIn c t) x]
  exact congrFun (S.totalMap_slice_primitive t) x

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
