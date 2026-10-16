import FsFltz.Geometry.IntrinsicNativeRibbonBoundaryFamily
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseSmooth

/-!
# The total comparison of the original ribbon quotients

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–160;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
The strict comparisons already retained on the original ribbon quotients
descend through their shared attachment. The inverse is obtained on each
actual parameter fiber. Both maps retain the same slice comparison, native
inclusion and full cylinder; smoothness is proved in the following module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

namespace NativeRibbonCompletionSlices

variable (S : NativeRibbonCompletionSlices Q μ eMs)

/-- The retained strict slice comparison in the same reference completion. -/
def referenceEquiv (t : Parameter) :
    (completionManifold S.width_pos (S.collar t) (S.collar_embedding t)
      (S.collar_smooth t) (S.collar_boundary t) (S.collar_inverse t)
      (S.collar_zero t)).SmoothEquiv Q.source.ribbonCompletion.ambient.manifold :=
  (S.comparison t).trans (Q.ribbonCompletionPresentation t).equiv.symm

/-- The native inclusion square uses the exact retained comparison. -/
theorem referenceEquiv_native (t : Parameter) (x : M) :
    S.referenceEquiv t (original (fun p => S.collar t p.val) x) =
      (Q.ribbonCompletionPresentation t).equiv.symm
        ((Q.pair t).ribbonCompletion.inclusion.map (eMs t x).val) :=
  congrArg (Q.ribbonCompletionPresentation t).equiv.symm (S.comparison_native t x)

/-- Compact coherence identifies the reference native map with the actual
all-real native relabeling and the fixed source inclusion. -/
theorem referenceEquiv_native_eq_compact
    (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (eMs parameterZero (RM t.val x)).val = (eMs t x).val)
    (t : Parameter) (x : M) :
    S.referenceEquiv t (original (fun p => S.collar t p.val) x) =
      Q.source.ribbonCompletion.inclusion.map (eMs parameterZero (RM t.val x)).val := by
  rw [S.referenceEquiv_native]
  have h := (Q.ribbonCompletionPresentation t).compact_square
    (eMs parameterZero (RM t.val x)).val (eMs parameterZero (RM t.val x)).property
  rw [hsquare] at h
  rw [← h, (Q.ribbonCompletionPresentation t).equiv.symm_apply_apply]
  rfl

/-- The whole cylinder, including the inward collar, keeps the moving
reference boundary coordinate determined by the same pair presentation. -/
theorem referenceEquiv_cylinder (t : Parameter)
    (p : Band S.width (IntrinsicBoundary.Point k M)) :
    S.referenceEquiv t (cylinder (fun p => S.collar t p.val) p) =
      (Q.ribbonCompletionPresentation t).prescribedEndMap
        ((Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t p.val.2),
          -p.val.1) := by
  change (Q.ribbonCompletionPresentation t).equiv.symm
    (S.comparison t (cylinder (fun p => S.collar t p.val) p)) = _
  rw [S.comparison_cylinder]
  change _ = (Q.ribbonCompletionPresentation t).equiv.symm
    ((Q.pair t).ribbonCompletion.endMap
      ((Q.ribbonPresentation t).boundaryEquiv
        ((Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t p.val.2)),
          -p.val.1))
  rw [(Q.ribbonPresentation t).boundaryEquiv.apply_symm_apply]

/-- Spatial descent through the original shared ribbon attachment. -/
def totalMap :
    TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val) →
      Q.source.ribbonCompletion.ambient.manifold.Point :=
  totalDescendMap (fun t p => S.collar t p.val)
    (fun p => S.referenceEquiv p.1 (original (fun q => S.collar p.1 q.val) p.2))
    (fun p => S.referenceEquiv p.1 (cylinder (fun q => S.collar p.1 q.val) p.2))

private theorem totalMap_seam (t : Parameter)
    (p : Half S.width (IntrinsicBoundary.Point k M)) :
    S.referenceEquiv t (original (fun q => S.collar t q.val) (S.collar t p.val)) =
      S.referenceEquiv t (cylinder (fun q => S.collar t q.val) (halfToBand p)) :=
  congrArg (S.referenceEquiv t) (original_collar_eq_cylinder _ p)

/-- The descended map restricts literally to the retained strict comparison. -/
@[simp] theorem totalMap_sliceIn (t : Parameter)
    (x : Space (fun p : Half S.width (IntrinsicBoundary.Point k M) => S.collar t p.val)) :
    S.totalMap (sliceIn (fun t p => S.collar t p.val) t x) = S.referenceEquiv t x := by
  rw [totalMap, totalDescendMap_sliceIn _ _ _ S.totalMap_seam]
  exact congrFun (descendMap_unique _ _ _ (S.referenceEquiv t)
    (fun _ => rfl) (fun _ => rfl)).symm x

@[simp] theorem totalMap_native (t : Parameter) (x : M) :
    S.totalMap (original (totalCollar (fun t p => S.collar t p.val)) (t, x)) =
      S.referenceEquiv t (original (fun p => S.collar t p.val) x) := rfl

@[simp] theorem totalMap_cylinder (t : Parameter)
    (p : Band S.width (IntrinsicBoundary.Point k M)) :
    S.totalMap (totalCylinder (fun t p => S.collar t p.val) (t, p)) =
      S.referenceEquiv t (cylinder (fun p => S.collar t p.val) p) :=
  totalDescendMap_cylinder _ _ _ S.totalMap_seam (t, p)

/-- The inverse uses the original parameter slice, with its existing atlas. -/
def totalInverse (p : Parameter × Q.source.ribbonCompletion.ambient.manifold.Point) :
    TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val) :=
  sliceIn (fun t p => S.collar t p.val) p.1 ((S.referenceEquiv p.1).symm p.2)

/-- The same slice maps and quotient fibers give the parameter-preserving
total equivalence. No independently chosen inverse is supplied. -/
def totalEquiv :
    TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val) ≃
      Parameter × Q.source.ribbonCompletion.ambient.manifold.Point where
  toFun z := (parameter (fun t p => S.collar t p.val) z, S.totalMap z)
  invFun := S.totalInverse
  left_inv z := by
    let c := fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val
    let t := parameter c z
    let w := (fiberEquiv c t).symm ⟨z, rfl⟩
    have hw : sliceIn c t w = z :=
      congrArg Subtype.val ((fiberEquiv c t).apply_symm_apply ⟨z, rfl⟩)
    change sliceIn c t ((S.referenceEquiv t).symm (S.totalMap z)) = z
    rw [← hw, S.totalMap_sliceIn, (S.referenceEquiv t).symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · exact parameter_sliceIn _ _ _
    · exact (S.totalMap_sliceIn p.1 _).trans ((S.referenceEquiv p.1).apply_symm_apply p.2)

@[simp] theorem totalEquiv_apply
    (z : TotalSpace (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val)) :
    S.totalEquiv z = (parameter (fun t p => S.collar t p.val) z, S.totalMap z) := rfl

/-- Forward restriction to every original completion slice. -/
@[simp] theorem totalEquiv_sliceIn (t : Parameter)
    (x : Space (fun p : Half S.width (IntrinsicBoundary.Point k M) => S.collar t p.val)) :
    S.totalEquiv (sliceIn (fun t p => S.collar t p.val) t x) =
      (t, S.referenceEquiv t x) :=
  Prod.ext (parameter_sliceIn _ _ _) (S.totalMap_sliceIn t x)

/-- The inverse has the exact retained slice comparison at every parameter. -/
@[simp] theorem totalEquiv_symm_apply
    (t : Parameter) (y : Q.source.ribbonCompletion.ambient.manifold.Point) :
    S.totalEquiv.symm (t, y) =
      sliceIn (fun t p => S.collar t p.val) t ((S.referenceEquiv t).symm y) := rfl

@[simp] theorem parameter_totalEquiv_symm
    (p : Parameter × Q.source.ribbonCompletion.ambient.manifold.Point) :
    parameter (fun t (p : Half S.width (IntrinsicBoundary.Point k M)) => S.collar t p.val)
      (S.totalEquiv.symm p) = p.1 := parameter_sliceIn _ _ _

end NativeRibbonCompletionSlices
end FsFltz.Geometry.PairDeformation
