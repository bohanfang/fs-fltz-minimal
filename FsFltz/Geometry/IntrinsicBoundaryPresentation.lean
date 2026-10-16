import FsFltz.Geometry.IntrinsicBoundaryForm

/-!
# Native boundary transport through an intrinsic compact presentation

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The ambient inclusion of a constructed compact presentation
also supplies its boundary presentation. Its restriction maps the literal
native boundary onto the actual ambient frontier. The chain rule proves
immersion, and equal boundary dimensions give a smooth inverse by the inverse
function theorem. Composing with the already proved frontier presentation
gives the diffeomorphism to the supplied boundary, with the same ambient
inclusion and the actual restricted primitive.

The hypotheses below are properties already proved for the source-derived
compact and Liouville presentations. No boundary equivalence or form-transport
certificate is required as a new premise. No completion or comparison chain
is constructed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The same ambient inclusion, restricted to the literal native boundary. -/
def boundaryFrontierMap (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (x : IntrinsicBoundary.Point k M) : D.FrontierPoint :=
  ⟨i x.val, hfrontier ▸ ⟨x.val, x.property, rfl⟩⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem boundaryFrontierMap_val (D : CompactDomain (k + 1))
    (i : M → D.extension.Point)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (x : IntrinsicBoundary.Point k M) :
    (boundaryFrontierMap D i hfrontier x).val = i x.val := rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Frontier surjectivity and ambient injectivity give boundary bijectivity. -/
theorem bijective_boundaryFrontierMap (D : CompactDomain (k + 1))
    (i : M → D.extension.Point) (hinj : Function.Injective i)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M) :
    Function.Bijective (boundaryFrontierMap D i hfrontier) := by
  constructor
  · intro x y hxy
    exact Subtype.ext (hinj (congrArg Subtype.val hxy))
  · intro y
    have hy : y.val ∈ i '' (𝓡∂ (k + 1)).boundary M := by
      rw [← hfrontier]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Native boundary smoothness follows through the actual ambient inclusion. -/
theorem contMDiff_boundaryFrontierMap (D : CompactDomain (k + 1))
    (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M) :
    ContMDiff 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ (boundaryFrontierMap D i hfrontier) := by
  apply D.contMDiff_frontier_iff_val.mpr
  exact hi.comp IntrinsicBoundary.contMDiff_val

/-- The frontier-map differential is injective by the chain rule for the
same inclusion and the native boundary inclusion. -/
theorem injective_mfderiv_boundaryFrontierMap (D : CompactDomain (k + 1))
    (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (x : IntrinsicBoundary.Point k M) :
    Function.Injective (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k)
      (boundaryFrontierMap D i hfrontier) x) := by
  have hd₁ := mfderiv_comp (f := boundaryFrontierMap D i hfrontier)
    (g := (Subtype.val : D.FrontierPoint → D.extension.Point)) x
    (D.contMDiff_frontier_val.mdifferentiableAt (by simp))
    ((contMDiff_boundaryFrontierMap D i hi hfrontier).mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (f := (Subtype.val : IntrinsicBoundary.Point k M → M))
    (g := i) x (hi.mdifferentiableAt (by simp))
    (IntrinsicBoundary.contMDiff_val.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
    (i ∘ (Subtype.val : IntrinsicBoundary.Point k M → M)) x = _ at hd₁
  rw [hd₂] at hd₁
  intro v w hvw
  apply IntrinsicBoundary.injective_mfderiv_val x
  apply hdi x.val
  have he := congrArg (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1))
    (Subtype.val : D.FrontierPoint → D.extension.Point)
      (boundaryFrontierMap D i hfrontier x)) hvw
  exact (congrArg (fun A => A v) hd₁).trans
    (he.trans (congrArg (fun A => A w) hd₁).symm)

/-- Equal native boundary dimensions give a local diffeomorphism without
assuming smoothness of any inverse boundary map. -/
theorem isLocalDiffeomorph_boundaryFrontierMap (D : CompactDomain (k + 1))
    (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (x : IntrinsicBoundary.Point k M) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞
      (boundaryFrontierMap D i hfrontier) x := by
  apply isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ
    (contMDiff_boundaryFrontierMap D i hi hfrontier).contMDiffOn (mem_univ x)
  have hinj := injective_mfderiv_boundaryFrontierMap D i hi hdi hfrontier x
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

variable [T2Space M] [SecondCountableTopology M]

/-- The native boundary is diffeomorphic to the actual ambient frontier by
the same inclusion used for the compact presentation. -/
def boundaryFrontierEquiv (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hinj : Function.Injective i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M) :
    (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.intrinsicBoundary := by
  let e := Equiv.ofBijective (boundaryFrontierMap D i hfrontier)
    (bijective_boundaryFrontierMap D i hinj hfrontier)
  refine { e with
    contMDiff_toFun := contMDiff_boundaryFrontierMap D i hi hfrontier
    contMDiff_invFun := ?_ }
  intro y
  obtain ⟨q, hxq, hq⟩ := isLocalDiffeomorph_boundaryFrontierMap D i hi hdi hfrontier (e.symm y)
  have hqy : q (e.symm y) = y := (hq hxq).symm.trans (e.apply_symm_apply y)
  have hyq : y ∈ q.target := hqy ▸ q.map_source hxq
  apply (q.contMDiffOn_invFun.contMDiffAt (q.open_target.mem_nhds hyq))
    |>.congr_of_eventuallyEq
  filter_upwards [q.open_target.mem_nhds hyq] with z hz
  apply e.injective
  have hqz : e (q.invFun z) = z := (hq (q.map_target hz)).trans (q.right_inv hz)
  exact (e.apply_symm_apply z).trans hqz.symm

/-- The actual native boundary presentation in the supplied boundary model. -/
def boundaryPresentationEquiv (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hinj : Function.Injective i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M) :
    (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.boundary :=
  (boundaryFrontierEquiv D i hi hinj hdi hfrontier).trans D.boundaryDiffeomorph.symm

/-- Boundary transport preserves the SAME compact presentation's ambient map. -/
@[simp] theorem boundaryPresentationEquiv_inclusion (D : CompactDomain (k + 1))
    (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hinj : Function.Injective i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (x : IntrinsicBoundary.Point k M) :
    D.boundaryInclusion.map (boundaryPresentationEquiv D i hi hinj hdi hfrontier x) =
      i x.val := by
  have h := congrArg Subtype.val (D.boundaryDiffeomorph.apply_symm_apply
    (boundaryFrontierEquiv D i hi hinj hdi hfrontier x))
  exact h

/-- The actual restricted primitive is transported through the boundary
equivalence derived from its ambient pullback. -/
theorem pullback_boundaryForm (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hinj : Function.Injective i)
    (hdi : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (α : Form k M 1) (lam : D.extension.Form 1)
    (hpull : (fun x => (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α) :
    (IntrinsicBoundary.smoothManifold k M).pullback D.boundary
      (boundaryPresentationEquiv D i hi hinj hdi hfrontier) (D.boundaryForm lam) =
        IntrinsicBoundary.restrictForm α := by
  let e := boundaryPresentationEquiv D i hi hinj hdi hfrontier
  have he (x : IntrinsicBoundary.Point k M) : D.boundaryInclusion.map (e x) = i x.val :=
    boundaryPresentationEquiv_inclusion D i hi hinj hdi hfrontier x
  have hcomp : D.boundaryInclusion.map ∘ e =
      i ∘ (Subtype.val : IntrinsicBoundary.Point k M → M) := funext he
  ext x vs
  have hd₁ := mfderiv_comp (f := e) (g := D.boundaryInclusion.map) x
    (D.boundaryInclusion.map.contMDiff.mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp (f := (Subtype.val : IntrinsicBoundary.Point k M → M))
    (g := i) x (hi.mdifferentiableAt (by simp))
    (IntrinsicBoundary.contMDiff_val.mdifferentiableAt (by simp))
  rw [hcomp, hd₂] at hd₁
  change lam (D.boundaryInclusion.map (e x)) (fun a =>
      mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model (k + 1)) D.boundaryInclusion.map (e x)
        (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) e x (vs a))) =
    α x.val (fun a => mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
      (Subtype.val : IntrinsicBoundary.Point k M → M) x (vs a))
  rw [he, ← congrFun hpull x.val]
  apply congrArg (lam (i x.val))
  funext a
  exact congrArg (fun A => A (vs a)) hd₁.symm

end FsFltz.Geometry.IntrinsicLiouville
