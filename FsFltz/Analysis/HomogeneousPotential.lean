import FsFltz.Analysis.CoordinateLegendre

/-!
# Euler identities for the homogeneous potential end

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 686–692.
Degree-two homogeneity gives the exact radial identities used by the
adapted Liouville field. These identities concern the homogeneous end
function; no global homogeneity of its smoothed extension is asserted.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace FsFltz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Euler's identity for a degree-one homogeneous map, at a differentiable
point. Positive scalars suffice. -/
theorem fderiv_self_of_homogeneous_one {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x)
    (hhom : ∀ t : ℝ, 0 < t → g (t • x) = t • g x) :
    fderiv ℝ g x x = g x := by
  have hp : HasDerivAt (fun t : ℝ => t • x) x 1 :=
    by simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hd : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g x x) 1 := by
    have hg' : HasFDerivAt g (fderiv ℝ g x) ((1 : ℝ) • x) := by simpa using hg.hasFDerivAt
    exact hg'.comp_hasDerivAt 1 hp
  have he : (fun t : ℝ => g (t • x)) =ᶠ[𝓝 1] (fun t => t • g x) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht
  have hd' : HasDerivAt (fun t : ℝ => t • g x) (g x) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (g x)
  exact hd.unique (hd'.congr_of_eventuallyEq he)

/-- Euler's degree-two identity for a scalar potential. -/
theorem fderiv_self_of_homogeneous_two {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hhom : ∀ t : ℝ, 0 < t → f (t • x) = t ^ 2 * f x) :
    fderiv ℝ f x x = 2 * f x := by
  have hp : HasDerivAt (fun t : ℝ => t • x) x 1 :=
    by simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hd : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f x x) 1 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) ((1 : ℝ) • x) := by simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt 1 hp
  have he : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] (fun t => t ^ 2 * f x) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht
  have hd' : HasDerivAt (fun t : ℝ => t ^ 2 * f x) (2 * f x) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (f x)
  exact hd.unique (hd'.congr_of_eventuallyEq he)

/-- The differential of a degree-two function scales with degree one. -/
theorem fderiv_apply_smul_of_homogeneous_two {f : E → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ 2 * f x)
    {t : ℝ} (ht : 0 < t) {x : E}
    (hx : DifferentiableAt ℝ f x) (htx : DifferentiableAt ℝ f (t • x)) (v : E) :
    fderiv ℝ f (t • x) v = t * fderiv ℝ f x v := by
  have hleft := htx.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have hright := hx.hasFDerivAt.const_mul (t ^ 2)
  have he : (fun y => f (t • y)) = fun y => t ^ 2 * f y := funext (hhom t ht)
  change HasFDerivAt (fun y => f (t • y)) _ x at hleft
  rw [he] at hleft
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L v) (hleft.unique hright)
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at heq
  nlinarith

/-- The differential of a degree-one homogeneous map has degree zero. -/
theorem fderiv_smul_of_homogeneous_one {g : E → F}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = t • g x)
    {t : ℝ} (ht : 0 < t) {x : E}
    (hx : DifferentiableAt ℝ g x) (htx : DifferentiableAt ℝ g (t • x)) :
    fderiv ℝ g (t • x) = fderiv ℝ g x := by
  have hleft := htx.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have hright := hx.hasFDerivAt.const_smul t
  have he : (fun y => g (t • y)) = fun y => t • g y := funext (hhom t ht)
  change HasFDerivAt (fun y => g (t • y)) _ x at hleft
  rw [he] at hleft
  ext v
  apply smul_right_injective F ht.ne'
  have heq := congrArg (fun L : E →L[ℝ] F => L v) (hleft.unique hright)
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] using heq

omit [NormedSpace ℝ F] in
/-- Compactness of the unit sphere bounds every continuous degree-zero map
on the whole punctured space. -/
theorem exists_bound_of_homogeneous_zero [ProperSpace E] {g : E → F}
    (hg : ∀ x ≠ 0, ContinuousAt g x)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = g x) :
    ∃ C > 0, ∀ x ≠ 0, ‖g x‖ ≤ C := by
  have hs : ContinuousOn g (Metric.sphere (0 : E) 1) := by
    intro x hx
    apply (hg x ?_).continuousWithinAt
    have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    intro h
    simp [h] at hn
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hs
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn.ne']
  have hb := hC _ hy
  rw [hhom _ (inv_pos.mpr hn)] at hb
  exact hb.trans (le_max_left _ _)

/-- The derivative of a smooth degree-one map is uniformly bounded off zero. -/
theorem exists_fderiv_bound_of_homogeneous_one [ProperSpace E] {g : E → F}
    (hg : ∀ x ≠ 0, ContDiffAt ℝ ∞ g x)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = t • g x) :
    ∃ C > 0, ∀ x ≠ 0, ‖fderiv ℝ g x‖ ≤ C := by
  apply exists_bound_of_homogeneous_zero
    (fun x hx => (hg x hx).continuousAt_fderiv (by simp))
  intro t ht x
  by_cases hx : x = 0
  · simp [hx]
  exact fderiv_smul_of_homogeneous_one hhom ht
    ((hg x hx).differentiableAt (by simp))
    ((hg _ (smul_ne_zero ht.ne' hx)).differentiableAt (by simp))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal coordinate gradient of a punctured smooth homogeneous
potential is itself homogeneous of degree one. -/
theorem coordinateGradient_smul_of_homogeneous_two {f : (ι → ℝ) → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ 2 * f x)
    (hfd : ∀ x ≠ 0, DifferentiableAt ℝ f x) {x : ι → ℝ} (hx : x ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    coordinateGradient f (t • x) = t • coordinateGradient f x := by
  ext j
  exact fderiv_apply_smul_of_homogeneous_two hhom ht (hfd x hx)
    (hfd _ (smul_ne_zero ht.ne' hx)) (Pi.single j 1)

/-- The radial vector is mapped by the coordinate Hessian to the gradient. -/
theorem coordinateHessian_apply_self_of_homogeneous_two {f : (ι → ℝ) → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ 2 * f x)
    (hfd : ∀ x ≠ 0, DifferentiableAt ℝ f x) {x : ι → ℝ} (hx : x ≠ 0)
    (hg : DifferentiableAt ℝ (coordinateGradient f) x) :
    fderiv ℝ (coordinateGradient f) x x = coordinateGradient f x :=
  fderiv_self_of_homogeneous_one hg
    (fun _ ht => coordinateGradient_smul_of_homogeneous_two hhom hfd hx ht)

end FsFltz
