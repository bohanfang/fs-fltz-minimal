import FsFltz.Analysis.ConvexLegendre
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-!
# Strong convexity and Legendre maps smooth away from the origin

Analytic producers for the homogeneous assertion of `lem:potential` in
`geometric-part-fsf-proof.tex`, lines 636–642. Uniform convexity gives
injectivity and coercive minimization gives surjectivity without assuming
second differentiability at the origin.
-/

noncomputable section

open Function Set Filter
open scoped Topology ContDiff

namespace FsFltz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A differentiable convex function lies above its tangent affine function. -/
theorem fderiv_le_sub_of_convex {φ : E → ℝ}
    (hconv : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) (x y : E) :
    (fderiv ℝ φ x) (y - x) ≤ φ y - φ x := by
  let v := y - x
  let f : ℝ → ℝ := fun t => φ (x + t • v)
  have hl : ConvexOn ℝ univ f := by
    have h := hconv.comp_affineMap (AffineMap.lineMap x y)
    simpa only [preimage_univ, Function.comp_def, AffineMap.lineMap_apply,
      vsub_eq_sub, vadd_eq_add, add_comm, f, v] using h
  have hp : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hf : HasDerivAt f ((fderiv ℝ φ x) v) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero, f] using
      (hd _).hasFDerivAt.comp_hasDerivAt 0 hp
  have h := hl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hf
  simpa [slope_def_field, f, v] using h

/-- Strong convexity expressed by subtracting a quadratic gives a quantitative
monotonicity estimate for the actual gradient, without second derivatives. -/
theorem mul_norm_sq_le_inner_gradient_sub_of_convex_quadratic {φ : E → ℝ} {c : ℝ}
    (hd : Differentiable ℝ φ)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2)) (x y : E) :
    2 * c * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient φ y - gradient φ x) (y - x) := by
  let f := fun x => φ x - c * ‖x‖ ^ 2
  have hdf : Differentiable ℝ f := hd.fun_sub
    ((differentiable_const c).mul
      (Differentiable.norm_sq ℝ (differentiable_id : Differentiable ℝ (fun x : E => x))))
  have hx := fderiv_le_sub_of_convex hconv hdf x y
  have hy := fderiv_le_sub_of_convex hconv hdf y x
  have hD (z v : E) : (fderiv ℝ f z) v =
      inner ℝ (gradient φ z) v - 2 * c * inner ℝ z v := by
    have hq := ((hasFDerivAt_id z).norm_sq.const_mul c)
    have hs : HasFDerivAt f
        (fderiv ℝ φ z - c • 2 • (innerSL ℝ) z) z := by
      simpa only [f, id_eq, Pi.sub_apply, ContinuousLinearMap.comp_id] using
        (hd z).hasFDerivAt.fun_sub hq
    rw [hs.fderiv]
    simp [inner_gradient_left, mul_comm, mul_left_comm]
  rw [hD x (y - x)] at hx
  rw [hD y (x - y)] at hy
  have hn : ‖y - x‖ ^ 2 = inner ℝ y y + inner ℝ x x - 2 * inner ℝ x y := by
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm x y]
    ring
  simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hx hy ⊢
  rw [hn]
  nlinarith

/-- Uniform convexity gives a quantitative global embedding of the gradient. -/
theorem antilipschitz_gradient_of_convex_quadratic {φ : E → ℝ} {c : ℝ}
    (hd : Differentiable ℝ φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2)) :
    AntilipschitzWith ⟨(2 * c)⁻¹, inv_nonneg.mpr (by positivity)⟩ (gradient φ) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist x y ≤ (2 * c)⁻¹ * dist (gradient φ x) (gradient φ y)
  rw [dist_eq_norm, dist_eq_norm]
  have hb := mul_norm_sq_le_inner_gradient_sub_of_convex_quadratic hd hconv y x
  have hi : inner ℝ (gradient φ x - gradient φ y) (x - y) ≤
      ‖gradient φ x - gradient φ y‖ * ‖x - y‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (gradient φ x - gradient φ y) (x - y)))
  by_cases hzero : x = y
  · simp [hzero]
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
  apply (le_inv_mul_iff₀ (show 0 < 2 * c by positivity)).mpr
  nlinarith

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Quadratic growth makes every linear perturbation attain its minimum.
The proof uses compact minimization, not an assumed minimizer. -/
theorem exists_min_linear_perturbation_of_quadratic_lower_bound {φ : E → ℝ} {c : ℝ}
    (hφ : Continuous φ) (hc : 0 < c) (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (p : E) :
    ∃ x, ∀ y, φ x - inner ℝ p x ≤ φ y - inner ℝ p y := by
  let f : E → ℝ := fun x => φ x - inner ℝ p x
  have hfc : Continuous f := hφ.sub (continuous_const.inner continuous_id)
  apply hfc.exists_forall_le' 0
  rw [← Metric.cobounded_eq_cocompact]
  let R := max 1 ((‖p‖ + |φ 0|) / c)
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop R)] with x hx
  have hn : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hr : (‖p‖ + |φ 0|) / c ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hm : ‖p‖ + |φ 0| ≤ c * ‖x‖ := by
    simpa [mul_comm] using (div_le_iff₀ hc).mp hr
  have hmn := mul_le_mul_of_nonneg_right hm (norm_nonneg x)
  have hi : inner ℝ p x ≤ ‖p‖ * ‖x‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) p x))
  have habs := mul_le_mul_of_nonneg_left hn (abs_nonneg (φ 0))
  have hl := hlower x
  dsimp [f]
  simp only [inner_zero_right]
  nlinarith [le_abs_self (φ 0)]

/-- A differentiable function with a positive quadratic lower bound has a
surjective actual gradient, by Fermat's theorem at a coercive minimizer. -/
theorem surjective_gradient_of_quadratic_lower_bound {φ : E → ℝ} {c : ℝ}
    (hd : Differentiable ℝ φ) (hc : 0 < c) (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) :
    Surjective (gradient φ) := by
  intro p
  obtain ⟨x, hx⟩ := exists_min_linear_perturbation_of_quadratic_lower_bound
    hd.continuous hc hlower p
  have hmin : IsLocalMin (fun y => φ y - inner ℝ p y) x :=
    (show IsMinOn (fun y => φ y - inner ℝ p y) univ x from fun _ _ => hx _).isLocalMin
      (univ_mem : (univ : Set E) ∈ 𝓝 x)
  have hf : HasFDerivAt (fun y => φ y - inner ℝ p y)
      (fderiv ℝ φ x - innerSL ℝ p) x := by
    exact (hd x).hasFDerivAt.fun_sub (innerSL ℝ p).hasFDerivAt
  have hz := hmin.hasFDerivAt_eq_zero hf
  refine ⟨x, ?_⟩
  apply (InnerProductSpace.toDual ℝ E).injective
  ext v
  simpa only [toDual_gradient, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply] using congrArg (fun L : E →L[ℝ] ℝ => L v) (sub_eq_zero.mp hz)

/-- The global Legendre homeomorphism requires only `C¹` regularity; its
derivative at the origin need not be twice differentiable. -/
def strongConvexGradientHomeomorph {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) : E ≃ₜ E := by
  have hd := hφ.differentiable (by norm_num)
  have ha := antilipschitz_gradient_of_convex_quadratic hd hc hconv
  have hcont : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (contDiff_one_iff_fderiv.mp hφ).2
  exact (Equiv.ofBijective (gradient φ)
    ⟨ha.injective, surjective_gradient_of_quadratic_lower_bound hd hc hlower⟩).toHomeomorphOfIsInducing
      (ha.isInducing hcont)

@[simp]
theorem strongConvexGradientHomeomorph_apply {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (x : E) :
    strongConvexGradientHomeomorph hφ hc hconv hlower x = gradient φ x := rfl

@[simp]
theorem strongConvexGradientHomeomorph_coe {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) :
    (strongConvexGradientHomeomorph hφ hc hconv hlower : E → E) = gradient φ := rfl

omit [FiniteDimensional ℝ E] in
/-- Local smoothness of the actual gradient where the potential is smooth. -/
theorem contDiffAt_gradient {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ ∞ φ x) :
    ContDiffAt ℝ ∞ (gradient φ) x :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
    (hφ.fderiv_right (by simp))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem injective_of_positive_inner {L : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hb : ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (L v) v) : Injective L := by
  intro v w hvw
  have hz : L (v - w) = 0 := by simp [map_sub, hvw]
  have hb := hb (v - w)
  rw [hz, inner_zero_left] at hb
  have hn : ‖v - w‖ = 0 := by
    by_contra h
    have := mul_pos hc (sq_pos_of_ne_zero h)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The inverse Legendre map is smooth at every nonzero covector, although
the gradient may fail to be differentiable at the origin. -/
theorem contDiffAt_symm_strongConvexGradientHomeomorph {φ : E → ℝ} {c d : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (hφ0 : gradient φ 0 = 0)
    (hφs : ∀ x ≠ 0, ContDiffAt ℝ ∞ φ x) (hd : 0 < d)
    (hb : ∀ x ≠ 0, ∀ v, d * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    {p : E} (hp : p ≠ 0) :
    ContDiffAt ℝ ∞ (strongConvexGradientHomeomorph hφ hc hconv hlower).symm p := by
  let H := strongConvexGradientHomeomorph hφ hc hconv hlower
  let x := H.symm p
  have hx : x ≠ 0 := by
    intro hx
    have he : H x = p := H.apply_symm_apply p
    rw [hx] at he
    exact hp (by simpa [H, hφ0] using he.symm)
  have hgrad : ContDiffAt ℝ ∞ (gradient φ) x := contDiffAt_gradient (hφs x hx)
  have hi := injective_of_positive_inner hd (hb x hx)
  let L : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ (gradient φ) x).toLinearMap
    ⟨hi, (fderiv ℝ (gradient φ) x).toLinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv
  have hL : (L : E →L[ℝ] E) = fderiv ℝ (gradient φ) x := by ext v; rfl
  have hDeriv : HasFDerivAt H (L : E →L[ℝ] E) x := by
    simpa [H, hL] using hgrad.differentiableAt (by simp) |>.hasFDerivAt
  exact H.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ p) hDeriv
    (by simpa [H] using hgrad)

/-- The homogeneous gradient restricts to a literal homeomorphism of the
punctured spaces when its value at zero is zero. -/
def puncturedGradientHomeomorph {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (hφ0 : gradient φ 0 = 0) :
    {x : E // x ≠ 0} ≃ₜ {x : E // x ≠ 0} := by
  let H := strongConvexGradientHomeomorph hφ hc hconv hlower
  apply H.subtype
  intro x
  constructor
  · intro hx hzero
    apply hx
    apply H.injective
    simpa [H, hφ0] using hzero
  · intro hx hzero
    exact hx (by simpa [H, hzero] using hφ0)

@[simp]
theorem puncturedGradientHomeomorph_apply {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (hφ0 : gradient φ 0 = 0)
    (x : {x : E // x ≠ 0}) :
    (puncturedGradientHomeomorph hφ hc hconv hlower hφ0 x).val = gradient φ x.val := rfl

/-- Smoothness of the punctured gradient in ambient coordinates. -/
theorem contDiffOn_strongConvexGradientHomeomorph {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x)
    (hφs : ∀ x ≠ 0, ContDiffAt ℝ ∞ φ x) :
    ContDiffOn ℝ ∞ (strongConvexGradientHomeomorph hφ hc hconv hlower)
      ({0}ᶜ : Set E) := by
  intro x hx
  simpa using (contDiffAt_gradient (hφs x (by simpa using hx))).contDiffWithinAt

/-- Smoothness of the punctured inverse in ambient coordinates. -/
theorem contDiffOn_symm_strongConvexGradientHomeomorph {φ : E → ℝ} {c d : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x => φ x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, c * ‖x‖ ^ 2 ≤ φ x) (hφ0 : gradient φ 0 = 0)
    (hφs : ∀ x ≠ 0, ContDiffAt ℝ ∞ φ x) (hd : 0 < d)
    (hb : ∀ x ≠ 0, ∀ v, d * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v) :
    ContDiffOn ℝ ∞ (strongConvexGradientHomeomorph hφ hc hconv hlower).symm
      ({0}ᶜ : Set E) := by
  intro p hp
  exact (contDiffAt_symm_strongConvexGradientHomeomorph hφ hc hconv hlower hφ0
    hφs hd hb (by simpa using hp)).contDiffWithinAt

end FsFltz
