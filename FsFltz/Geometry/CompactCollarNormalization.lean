import FsFltz.Geometry.CompletionCollarExtension
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Transverse germs of existing compact presentations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and `sec:lean`,
lines 788–814. The compact presentation is existing data. Its local collar
transition is constructed from the actual completion inclusions and end maps.
The side-preservation equation and invertible differential force its normal
derivative at the boundary to be strictly positive.

This is a prerequisite for relative collar normalization, not that theorem.
`CollarIsotopy` uses the positive normal coefficient in a direct smooth
interpolation and constructs a common collar of embeddings; it requires no
division by a vanishing rescaling parameter. Extension through the compact
interior and coherent choices for varying completions remain separate
foundations. No geometric target is asserted here.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false in
private theorem normal_derivative_pos
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    {f : M × ℝ → N × ℝ} {x : M}
    (hf : ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) ∞ f (x, 0))
    (hd : Function.Surjective
      (mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) f (x, 0)))
    (hb : ∀ᶠ y in 𝓝 x, (f (y, 0)).2 = 0)
    (hside : ∀ᶠ r in 𝓝 (0 : ℝ), (f (x, r)).2 ≤ 0 ↔ r ≤ 0) :
    0 < (mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) f (x, 0) (0, 1)).2 := by
  let L : E × ℝ →L[ℝ] F × ℝ := mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, F)).prod 𝓘(ℝ, ℝ)) f (x, 0)
  let g : M × ℝ → ℝ := fun p => (f p).2
  have hg : MDifferentiableAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g (x, 0) :=
    mdifferentiableAt_snd.comp (x, 0) (hf.mdifferentiableAt (by simp))
  have hgd : mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g (x, 0) =
      (ContinuousLinearMap.snd ℝ F ℝ).comp L := by
    exact (mfderiv_comp (x, 0) mdifferentiableAt_snd
      (hf.mdifferentiableAt (by simp))).trans (by rw [mfderiv_snd]; rfl)
  have ht (v : E) : (L (v, 0)).2 = 0 := by
    have he : (fun y : M => g (y, 0)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := hb
    have h := congrArg (fun A => A v) (he.mfderiv_eq
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)))
    have hc := mfderiv_comp (f := fun y : M => (y, (0 : ℝ))) (g := g) x hg
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => g (y, 0)) x = _ at hc
    rw [hc, mfderiv_prod_left, hgd, mfderiv_const] at h
    exact h
  have hn : (L (0, 1)).2 ≠ 0 := by
    intro hz
    obtain ⟨⟨v, r⟩, he⟩ := hd (0, 1)
    have hsplit : (v, r) = (v, 0) + r • (0, 1) := by ext <;> simp
    have he' : (L (v, r)).2 = 1 := congrArg Prod.snd he
    rw [hsplit, map_add, map_smul] at he'
    change (L (v, 0)).2 + r * (L (0, 1)).2 = 1 at he'
    rw [ht, hz, mul_zero, add_zero] at he'
    exact zero_ne_one he'
  have hr : HasDerivAt (fun r : ℝ => g (x, r)) (L (0, 1)).2 0 := by
    have h := mfderiv_comp (f := fun r : ℝ => (x, r)) (g := g) 0 hg
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right, hgd, mfderiv_eq_fderiv] at h
    have hdg := (hg.comp 0 (mdifferentiableAt_const.prodMk mdifferentiableAt_id)).differentiableAt
    apply hdg.hasFDerivAt.hasDerivAt.congr_deriv
    have he := congrArg (fun A : ℝ →L[ℝ] ℝ => A (1 : ℝ)) h
    exact he
  have hzero : g (x, 0) = 0 := hb.self_of_nhds
  have hnonneg : 0 ≤ (L (0, 1)).2 := by
    apply ge_of_tendsto hr.tendsto_slope_zero_right
    filter_upwards [hside.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hs hrpos
    have hgpos : 0 < g (x, r) := lt_of_not_ge (fun hn =>
      (not_le_of_gt hrpos) (hs.mp hn))
    simp only [zero_add, hzero, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hrpos)) (le_of_lt hgpos)
  exact lt_of_le_of_ne hnonneg hn.symm

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- A representative of the source compact collar germ at one boundary
point. The selected inverse is only used on its proved neighborhood. -/
def compactCollarAt (x : D.domain.boundary.Point)
    (q : D.domain.boundary.Point × ℝ) : D.domain.extension.Point :=
  (C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)).localInverse
    (C.endMap q)

@[simp] theorem compactCollarAt_zero (x : D.domain.boundary.Point) :
    C.compactCollarAt x (x, 0) = D.domain.boundaryInclusion.map x := by
  rw [compactCollarAt, C.endMap_zero]
  exact (C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)).localInverse_left_inv
    (C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)).localInverse_mem_target

/-- The actual collar transition of the supplied compact presentation,
represented by local inverse maps near `(x,0)`. It retains the presentation's
own boundary map, rather than extending an arbitrary boundary map. -/
def compactCollarTransitionAt (x : D.domain.boundary.Point)
    (q : D.domain.boundary.Point × ℝ) : E.domain.boundary.Point × ℝ :=
  (C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)).localInverse
    (C'.inclusion.map (h.extensionEquiv (C.compactCollarAt x q)))

@[simp] theorem compactCollarTransitionAt_zero (x : D.domain.boundary.Point) :
    C.compactCollarTransitionAt C' h x (x, 0) = (h.boundaryEquiv x, 0) := by
  rw [compactCollarTransitionAt, C.compactCollarAt_zero, h.boundary_square,
    ← C'.endMap_zero]
  exact (C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)).localInverse_left_inv
    (C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)).localInverse_mem_target

/-- This representative is a genuine local diffeomorphism at its boundary
point. Each of its four factors is an actual local diffeomorphism. -/
theorem isLocalDiffeomorphAt_compactCollarTransitionAt (x : D.domain.boundary.Point) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.compactCollarTransitionAt C' h x) (x, 0) := by
  let l := C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)
  have hs : IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ (C.compactCollarAt x) (x, 0) := by
    apply (C.endMap_isLocalDiffeomorph (x, 0)).comp
      𝓘(ℝ, Model d) D.domain.extension.Point
    apply l.localInverse.isLocalDiffeomorphAt
    rw [C.endMap_zero]
    exact l.localInverse_mem_source
  have hh := hs.comp 𝓘(ℝ, Model d) E.domain.extension.Point
    (h.extensionEquiv.isLocalDiffeomorph _)
  have hi := hh.comp 𝓘(ℝ, Model d) C'.ambient.manifold.Point
    (C'.inclusion_isLocalDiffeomorph _)
  apply hi.comp ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (E.domain.boundary.Point × ℝ)
  apply (C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)).localInverse.isLocalDiffeomorphAt
  change C'.inclusion.map (h.extensionEquiv (C.compactCollarAt x (x, 0))) ∈ _
  rw [C.compactCollarAt_zero, h.boundary_square, ← C'.endMap_zero]
  exact (C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)).localInverse_mem_source

theorem contMDiffAt_compactCollarTransitionAt (x : D.domain.boundary.Point) :
    ContMDiffAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.compactCollarTransitionAt C' h x) (x, 0) :=
  (C.isLocalDiffeomorphAt_compactCollarTransitionAt C' h x).contMDiffAt

/-- The boundary equation holds on an actual neighborhood, not merely at
the selected point. No agreement at negative radius is an input. -/
theorem compactCollarTransitionAt_boundary_eventually (x : D.domain.boundary.Point) :
    ∀ᶠ y in 𝓝 x,
      C.compactCollarTransitionAt C' h x (y, 0) = (h.boundaryEquiv y, 0) := by
  let l := C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)
  let m := C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)
  have hs := l.localInverse_eventuallyEq_left.comp_tendsto
    D.domain.boundaryInclusion.map.contMDiff.continuous.continuousAt
  have ht := m.localInverse_eventuallyEq_left.comp_tendsto
    (h.boundaryEquiv.contMDiff.continuous.continuousAt.prodMk continuousAt_const)
  filter_upwards [hs, ht] with y hy hz
  change l.localInverse (C.inclusion.map (D.domain.boundaryInclusion.map y)) =
    D.domain.boundaryInclusion.map y at hy
  change m.localInverse (C'.endMap (h.boundaryEquiv y, 0)) = (h.boundaryEquiv y, 0) at hz
  change m.localInverse (C'.inclusion.map
    (h.extensionEquiv (l.localInverse (C.endMap (y, 0))))) = _
  rw [C.endMap_zero, hy, h.boundary_square, ← C'.endMap_zero]
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- Both completion equations hold throughout some open neighborhood of
the boundary point for this constructed transition germ. -/
theorem compactCollarTransitionAt_equations_eventually (x : D.domain.boundary.Point) :
    ∀ᶠ q in 𝓝 (x, (0 : ℝ)),
      C.inclusion.map (C.compactCollarAt x q) = C.endMap q ∧
      C'.endMap (C.compactCollarTransitionAt C' h x q) =
        C'.inclusion.map (h.extensionEquiv (C.compactCollarAt x q)) := by
  let l := C.inclusion_isLocalDiffeomorph (D.domain.boundaryInclusion.map x)
  let m := C'.endMap_isLocalDiffeomorph (h.boundaryEquiv x, 0)
  have hs : ContMDiffAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Model d) ∞ (C.compactCollarAt x) (x, 0) := by
    have hl : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ l.localInverse
        (C.endMap (x, 0)) := by
      rw [C.endMap_zero]
      exact l.localInverse_contMDiffAt
    exact hl.comp (x, 0) (C.smooth_endMap (x, 0))
  have htarget : Tendsto (fun q => C'.inclusion.map
      (h.extensionEquiv (C.compactCollarAt x q))) (𝓝 (x, 0))
      (𝓝 (C'.endMap (h.boundaryEquiv x, 0))) := by
    have hc := C'.inclusion.map.contMDiff.continuous.continuousAt.comp
      (h.extensionEquiv.contMDiff.continuous.continuousAt.comp hs.continuousAt)
    simpa only [ContinuousAt, Function.comp_def, C.compactCollarAt_zero,
      h.boundary_square, C'.endMap_zero] using hc
  have hsource : Tendsto C.endMap (𝓝 (x, 0))
      (𝓝 (C.inclusion.map (D.domain.boundaryInclusion.map x))) := by
    rw [← C.endMap_zero]
    exact C.smooth_endMap.continuous.continuousAt
  filter_upwards [l.localInverse_eventuallyEq_right.comp_tendsto hsource,
    m.localInverse_eventuallyEq_right.comp_tendsto htarget] with q hs ht
  exact ⟨hs, ht⟩

/-- Compact-side preservation of the original presentation is the exact
radius-side equation in the constructed transition coordinates. -/
theorem compactCollarTransitionAt_side_eventually (x : D.domain.boundary.Point) :
    ∀ᶠ q in 𝓝 (x, (0 : ℝ)),
      (C.compactCollarTransitionAt C' h x q).2 ≤ 0 ↔ q.2 ≤ 0 := by
  filter_upwards [C.compactCollarTransitionAt_equations_eventually C' h x] with q hq
  have hs : C.compactCollarAt x q ∈ D.domain.carrier ↔ q.2 ≤ 0 := by
    rw [← C.endMap_mem_compact_iff, ← hq.1]
    exact C.inclusion.embedding.injective.mem_set_image.symm
  have ht : h.extensionEquiv (C.compactCollarAt x q) ∈ E.domain.carrier ↔
      (C.compactCollarTransitionAt C' h x q).2 ≤ 0 := by
    rw [← C'.endMap_mem_compact_iff, hq.2]
    exact C'.inclusion.embedding.injective.mem_set_image.symm
  exact ht.symm.trans ((h.mem_carrier_iff _).trans hs)

/-- The positive normal coefficient is proved from the existing compact
presentation, actual completion collars, and carrier preservation. It is not
an added compatibility hypothesis for the collar-normalization problem. -/
theorem compactCollarTransitionAt_normal_derivative_pos (x : D.domain.boundary.Point) :
    0 < (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (C.compactCollarTransitionAt C' h x) (x, 0) (0, 1)).2 := by
  apply normal_derivative_pos
    (C.contMDiffAt_compactCollarTransitionAt C' h x)
  · exact (C.isLocalDiffeomorphAt_compactCollarTransitionAt C' h x).mfderivToContinuousLinearEquiv
      (by simp) |>.surjective
  · filter_upwards [C.compactCollarTransitionAt_boundary_eventually C' h x] with y hy
    exact congrArg Prod.snd hy
  · exact (continuousAt_const.prodMk continuousAt_id).eventually
      (C.compactCollarTransitionAt_side_eventually C' h x)

/-- The normal coefficient of the actual presentation's transition germ.
It is fixed at the selected boundary point in the normalization below. -/
def compactCollarNormalCoefficient (x : D.domain.boundary.Point) : ℝ :=
  (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (C.compactCollarTransitionAt C' h x) (x, 0) (0, 1)).2

theorem compactCollarNormalCoefficient_pos (x : D.domain.boundary.Point) :
    0 < C.compactCollarNormalCoefficient C' h x :=
  C.compactCollarTransitionAt_normal_derivative_pos C' h x

private def radiusDivision (a : ℝ) (ha : a ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun := fun r => r / a
  invFun := fun r => r * a
  left_inv := fun r => div_mul_cancel₀ r ha
  right_inv := fun r => mul_div_cancel_right₀ r ha
  contMDiff_toFun := (contDiff_id.div_const a).contMDiff
  contMDiff_invFun := (contDiff_id.mul contDiff_const).contMDiff

/-- An actual first-order normalization of the transition germ. Only the
target radius is divided by the positive coefficient at the basepoint;
exact agreement with the intrinsic collar at negative radii is not claimed. -/
def normalizedCompactCollarTransitionAt (x : D.domain.boundary.Point)
    (q : D.domain.boundary.Point × ℝ) : E.domain.boundary.Point × ℝ :=
  ((C.compactCollarTransitionAt C' h x q).1,
    (C.compactCollarTransitionAt C' h x q).2 / C.compactCollarNormalCoefficient C' h x)

/-- Positive radial division produces an actual local diffeomorphism germ,
consuming the proved normal coefficient without an extra transversality input. -/
theorem isLocalDiffeomorphAt_normalizedCompactCollarTransitionAt
    (x : D.domain.boundary.Point) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) ∞
      (C.normalizedCompactCollarTransitionAt C' h x) (x, 0) := by
  let s := (Diffeomorph.refl 𝓘(ℝ, Model (d - 1)) E.domain.boundary.Point ∞).prodCongr
    (radiusDivision (C.compactCollarNormalCoefficient C' h x)
      (ne_of_gt (C.compactCollarNormalCoefficient_pos C' h x)))
  exact (C.isLocalDiffeomorphAt_compactCollarTransitionAt C' h x).comp
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ)) (E.domain.boundary.Point × ℝ)
    (s.isLocalDiffeomorph _)

@[simp] theorem normalizedCompactCollarTransitionAt_zero (x : D.domain.boundary.Point) :
    C.normalizedCompactCollarTransitionAt C' h x (x, 0) = (h.boundaryEquiv x, 0) := by
  simp [normalizedCompactCollarTransitionAt]

theorem normalizedCompactCollarTransitionAt_boundary_eventually
    (x : D.domain.boundary.Point) :
    ∀ᶠ y in 𝓝 x,
      C.normalizedCompactCollarTransitionAt C' h x (y, 0) = (h.boundaryEquiv y, 0) := by
  filter_upwards [C.compactCollarTransitionAt_boundary_eventually C' h x] with y hy
  simp [normalizedCompactCollarTransitionAt, hy]

theorem normalizedCompactCollarTransitionAt_side_eventually (x : D.domain.boundary.Point) :
    ∀ᶠ q in 𝓝 (x, (0 : ℝ)),
      (C.normalizedCompactCollarTransitionAt C' h x q).2 ≤ 0 ↔ q.2 ≤ 0 := by
  filter_upwards [C.compactCollarTransitionAt_side_eventually C' h x] with q hq
  change (C.compactCollarTransitionAt C' h x q).2 /
    C.compactCollarNormalCoefficient C' h x ≤ 0 ↔ q.2 ≤ 0
  rw [div_le_iff₀ (C.compactCollarNormalCoefficient_pos C' h x), zero_mul]
  exact hq

set_option backward.isDefEq.respectTransparency false in
/-- The constructed normalized germ has unit transverse derivative. This
is first-order normalization at one boundary point, not a collar isotopy. -/
theorem normalizedCompactCollarTransitionAt_normal_derivative
    (x : D.domain.boundary.Point) :
    (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
      (C.normalizedCompactCollarTransitionAt C' h x) (x, 0) (0, 1)).2 = 1 := by
  let f := C.compactCollarTransitionAt C' h x
  let a := C.compactCollarNormalCoefficient C' h x
  have hf := (C.contMDiffAt_compactCollarTransitionAt C' h x).mdifferentiableAt (by simp)
  have hg := (mdifferentiableAt_snd.comp (x, 0) hf).hasMFDerivAt
  have hgs := hg.const_smul a⁻¹
  have hd := mfderiv_prodMk (mdifferentiableAt_fst.comp (x, 0) hf) hgs.mdifferentiableAt
  have hval := congrArg (fun L => (L (0, (1 : ℝ))).2) hd
  change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (fun q => ((f q).1, a⁻¹ • (f q).2)) (x, 0) (0, 1)).2 = _ at hval
  have hcomp := mfderiv_comp (f := f) (g := Prod.snd) (x, 0) mdifferentiableAt_snd hf
  rw [hgs.mfderiv, hcomp, mfderiv_snd] at hval
  change (mfderiv ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    (fun q => ((f q).1, a⁻¹ * (f q).2)) (x, 0) (0, 1)).2 = a⁻¹ * a at hval
  have he : (fun q => ((f q).1, a⁻¹ * (f q).2)) =
      C.normalizedCompactCollarTransitionAt C' h x := by
    funext q
    simp only [normalizedCompactCollarTransitionAt, f, a, div_eq_mul_inv, mul_comm]
  rw [he, inv_mul_cancel₀ (ne_of_gt (C.compactCollarNormalCoefficient_pos C' h x))] at hval
  exact hval

end Completion
end FsFltz.Geometry
