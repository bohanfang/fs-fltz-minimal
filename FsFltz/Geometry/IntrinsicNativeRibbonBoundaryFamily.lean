import FsFltz.Geometry.IntrinsicNativeRibbonCompletionFamily

/-!
# Moving native ribbon boundary comparison

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and
`sec:lean`, lines 788–814. An actual all-real smooth native diffeomorphism
family restricts smoothly to the actual intrinsic boundary. The retained
compact square then determines the moving ribbon boundary map in the same
completed pair presentation. No fixed-boundary assumption is added.

This supplies the moving boundary ingredient consumed by the joint
positive-dimensional ribbon total comparison and its inverse in
`IntrinsicNativeRibbonTotalComparisonInverse.lean`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicBoundary

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

section SmoothMaps
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

/-- Smoothness into the actual native boundary is detected by its original
native inclusion. Boundary charts drop the normal coordinate of that same
ambient chart; no boundary-valued germ is supplied. -/
theorem contMDiffAt_iff_val {f : X → Point k M} {x : X} :
    ContMDiffAt I 𝓘(ℝ, Model k) ∞ f x ↔
      ContMDiffAt I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) x := by
  constructor
  · intro hf
    exact contMDiff_val.contMDiffAt.comp x hf
  · intro hf
    have hc : ContinuousAt f x :=
      Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuousAt
    apply contMDiffAt_iff_target.mpr
    refine ⟨hc, ?_⟩
    let c := chartAt (f x)
    have hcs : f x ∈ c.chart.source := mem_chartAt_source (f x)
    have hes : (f x).val ∈ c.ambient.source := by rwa [c.source_eq] at hcs
    have he := c.ambient.contMDiffAt_extend (I := 𝓡∂ (k + 1)) (n := ∞)
      (IsManifold.subset_maximalAtlas c.mem_atlas) hes
    apply ((boundaryDrop k).contDiff.contMDiff.contMDiffAt.comp x (he.comp x hf))
      |>.congr_of_eventuallyEq
    filter_upwards [hc.eventually_mem (c.chart.open_source.mem_nhds hcs)] with y hy
    exact c.toFun_eq (f y) hy

/-- Global form of reflection through the actual native boundary inclusion. -/
theorem contMDiff_iff_val {f : X → Point k M} :
    ContMDiff I 𝓘(ℝ, Model k) ∞ f ↔
      ContMDiff I (𝓡∂ (k + 1)) ∞ (Subtype.val ∘ f) := by
  constructor <;> intro h x
  · exact contMDiffAt_iff_val.mp (h x)
  · exact contMDiffAt_iff_val.mpr (h x)

end SmoothMaps

/-- Restriction of the actual native diffeomorphism to its literal boundary. -/
def diffeomorph (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞) :
    Diffeomorph 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) (Point k M) (Point k M) ∞ where
  toFun x := ⟨e x.val, by
    change e x.val ∈ (𝓡∂ (k + 1)).boundary M
    rw [← e.image_boundary (by simp)]
    exact ⟨x.val, x.property, rfl⟩⟩
  invFun x := ⟨e.symm x.val, by
    change e.symm x.val ∈ (𝓡∂ (k + 1)).boundary M
    rw [← e.symm.image_boundary (by simp)]
    exact ⟨x.val, x.property, rfl⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  contMDiff_toFun := contMDiff_iff_val.mpr (e.contMDiff.comp contMDiff_val)
  contMDiff_invFun := contMDiff_iff_val.mpr (e.symm.contMDiff.comp contMDiff_val)

@[simp] theorem diffeomorph_val
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞) (x : Point k M) :
    (diffeomorph e x).val = e x.val := rfl

/-- All-real native smoothness restricts in both directions to all-real
boundary smoothness, including neighborhoods of both interval endpoints. -/
theorem jointlySmooth_diffeomorph
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R) :
    IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model k) (fun s => diffeomorph (R s)) := by
  constructor
  · apply contMDiff_iff_val.mpr
    exact hR.1.comp (contMDiff_fst.prodMk (contMDiff_val.comp contMDiff_snd))
  · apply contMDiff_iff_val.mpr
    exact hR.2.comp (contMDiff_fst.prodMk (contMDiff_val.comp contMDiff_snd))

end FsFltz.Geometry.IntrinsicBoundary

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville

variable {k n : ℕ} [NeZero (2 * n - 2)]
  {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {Q : PairDeformation n} {μ : Parameter → Form k M 1}
  {eMs : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
    (Q.pair t).ribbonDomain.domain.Point ∞}

/-- The actual compact coherence determines the moving native boundary
square. The native relabeling is restricted to its own boundary; no assertion
that it fixes that boundary pointwise is needed. -/
theorem NativeRibbonCompletionSlices.boundary_reference_square
    (S : NativeRibbonCompletionSlices Q μ eMs)
    (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (eMs parameterZero (RM t.val x)).val = (eMs t x).val)
    (t : Parameter) (x : IntrinsicBoundary.Point k M) :
    (Q.ribbonPresentation t).boundaryEquiv
      (S.boundary_comparison parameterZero (IntrinsicBoundary.diffeomorph (RM t.val) x)) =
        S.boundary_comparison t x := by
  apply (Q.pair t).ribbonDomain.domain.boundaryInclusion.embedding.injective
  exact ((Q.ribbonPresentation t).boundary_square _).symm.trans
    ((congrArg (Q.ribbonPresentation t).extensionEquiv
      (S.boundary_native parameterZero (IntrinsicBoundary.diffeomorph (RM t.val) x))).trans
        ((hsquare t x.val).trans (S.boundary_native t x).symm))

/-- The reference native ribbon boundary map and its inverse have actual
all-real jointly smooth extensions. Both interval equations name the exact
boundary maps retained by the same original ribbon quotient comparisons. -/
theorem NativeRibbonCompletionSlices.exists_jointReferenceBoundaryComparison
    (S : NativeRibbonCompletionSlices Q μ eMs)
    (RM : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hRM : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) RM)
    (hsquare : ∀ t x, (Q.ribbonPresentation t).extensionEquiv
      (eMs parameterZero (RM t.val x)).val = (eMs t x).val) :
    ∃ B : ℝ → (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
        Q.source.ribbonDomain.domain.boundary,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
        𝓘(ℝ, Model ((2 * n - 2) - 1)) ∞
          (fun p : ℝ × IntrinsicBoundary.Point k M => B p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model ((2 * n - 2) - 1)))
        𝓘(ℝ, Model k) ∞
          (fun p : ℝ × Q.source.ribbonDomain.domain.boundary.Point => (B p.1).symm p.2) ∧
      (∀ (t : Parameter) x, B t.val x =
        (Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t x)) ∧
      (∀ (t : Parameter) y, (B t.val).symm y =
        (S.boundary_comparison t).symm ((Q.ribbonPresentation t).boundaryEquiv y)) ∧
      (∀ (t : Parameter) (p : IntrinsicCompletionGluing.Band S.width (IntrinsicBoundary.Point k M)),
        (Q.ribbonCompletionPresentation t).equiv.symm
          (S.comparison t (IntrinsicCompletionGluing.cylinder (fun p => S.collar t p.val) p)) =
            (Q.ribbonCompletionPresentation t).prescribedEndMap (B t.val p.val.2, -p.val.1)) := by
  let b₀ := S.boundary_comparison parameterZero
  let B := fun s => (IntrinsicBoundary.diffeomorph (RM s)).trans b₀
  have hRboundary := IntrinsicBoundary.jointlySmooth_diffeomorph RM hRM
  have hb (t : Parameter) (x : IntrinsicBoundary.Point k M) : B t.val x =
      (Q.ribbonPresentation t).boundaryEquiv.symm (S.boundary_comparison t x) := by
    apply (Q.ribbonPresentation t).boundaryEquiv.injective
    exact (S.boundary_reference_square RM hsquare t x).trans
      ((Q.ribbonPresentation t).boundaryEquiv.apply_symm_apply _).symm
  refine ⟨B, b₀.contMDiff.comp hRboundary.1,
    hRboundary.2.comp (contMDiff_fst.prodMk (b₀.symm.contMDiff.comp contMDiff_snd)), hb, ?_, ?_⟩
  · intro t y
    apply (B t.val).injective
    have hh : B t.val ((S.boundary_comparison t).symm
        ((Q.ribbonPresentation t).boundaryEquiv y)) = y :=
      (hb t _).trans ((congrArg (Q.ribbonPresentation t).boundaryEquiv.symm
        ((S.boundary_comparison t).apply_symm_apply _)).trans
          ((Q.ribbonPresentation t).boundaryEquiv.symm_apply_apply y))
    exact ((B t.val).apply_symm_apply y).trans hh.symm
  · intro t p
    have hbt := (congrArg (Q.ribbonPresentation t).boundaryEquiv (hb t p.val.2)).trans
      ((Q.ribbonPresentation t).boundaryEquiv.apply_symm_apply _)
    exact congrArg (Q.ribbonCompletionPresentation t).equiv.symm
      ((S.comparison_cylinder t p).trans
        (congrArg (fun b => (Q.pair t).ribbonCompletion.endMap (b, -p.val.1)) hbt.symm))

end FsFltz.Geometry.PairDeformation
