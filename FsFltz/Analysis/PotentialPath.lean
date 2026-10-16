import FsFltz.Analysis.ConvexLegendre
import FsFltz.Analysis.HomogeneousPotential
import FsFltz.Analysis.CompatiblePotentialLegendre

/-!
# The fixed affine path of smooth potentials

Source: `geometric-part-fsf-proof.tex`, choice dependencies, lines 493–521.
The interpolation is the literal affine combination of the two potentials.
Its actual Hessian retains endpoint lower and upper bounds uniformly for
the prescribed parameter interval. Norms in those bounds are Euclidean.
-/

noncomputable section

open Set
open Filter
open scoped ContDiff Topology

namespace FsFltz

variable {E : Type*}

/-- The potential interpolation fixed before the large-radius choices. -/
def potentialPath (φ₀ φ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  (1 - t) * φ₀ x + t * φ x

@[simp] theorem potentialPath_zero (φ₀ φ : E → ℝ) : potentialPath φ₀ φ 0 = φ₀ := by
  ext x
  simp [potentialPath]

@[simp] theorem potentialPath_one (φ₀ φ : E → ℝ) : potentialPath φ₀ φ 1 = φ := by
  ext x
  simp [potentialPath]

/-- Pullback commutes literally with the prescribed interpolation. -/
theorem potentialPath_comp {F : Type*} (φ₀ φ : E → ℝ) (e : F → E) (t : ℝ) :
    potentialPath φ₀ φ t ∘ e = potentialPath (φ₀ ∘ e) (φ ∘ e) t := rfl

/-- Literal agreement of the final potentials gives agreement of the path
members at the same point and parameter. -/
theorem potentialPath_eq_of_eq_right {φ₀ φ φEnd : E → ℝ} {x : E}
    (h : φ x = φEnd x) (t : ℝ) :
    potentialPath φ₀ φ t x = potentialPath φ₀ φEnd t x := by
  simp only [potentialPath, h]

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed path extends smoothly in both its parameter and space variable. -/
theorem potentialPath_contDiff {φ₀ φ : E → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => potentialPath φ₀ φ p.1 p.2) := by
  exact ((contDiff_const.sub contDiff_fst).mul (hφ₀.comp contDiff_snd)).add
    (contDiff_fst.mul (hφ.comp contDiff_snd))

/-- Every fixed member of the path is smooth on the entire space. -/
theorem potentialPath_contDiff_space {φ₀ φ : E → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) (t : ℝ) :
    ContDiff ℝ ∞ (potentialPath φ₀ φ t) :=
  (contDiff_const.mul hφ₀).add (contDiff_const.mul hφ)

/-- Interpolation preserves degree-two homogeneity when it holds at both ends. -/
theorem potentialPath_homogeneous_two {φ₀ φ : E → ℝ}
    (hφ₀ : ∀ r : ℝ, 0 < r → ∀ x, φ₀ (r • x) = r ^ 2 * φ₀ x)
    (hφ : ∀ r : ℝ, 0 < r → ∀ x, φ (r • x) = r ^ 2 * φ x)
    (t r : ℝ) (hr : 0 < r) (x : E) :
    potentialPath φ₀ φ t (r • x) = r ^ 2 * potentialPath φ₀ φ t x := by
  simp only [potentialPath, hφ₀ r hr x, hφ r hr x]
  ring

end Normed

section InnerProduct

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz gradient of the affine path is the same affine combination
of the endpoint gradients. -/
theorem gradient_potentialPath {φ₀ φ : E → ℝ}
    (hφ₀ : Differentiable ℝ φ₀) (hφ : Differentiable ℝ φ) (t : ℝ) (x : E) :
    gradient (potentialPath φ₀ φ t) x =
      (1 - t) • gradient φ₀ x + t • gradient φ x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add, map_smul, toDual_gradient]
  exact ((hφ₀ x).hasFDerivAt.const_mul (1 - t)).fun_add
    ((hφ x).hasFDerivAt.const_mul t) |>.fderiv

/-- The actual derivative of the path gradient is its endpoint affine combination. -/
theorem fderiv_gradient_potentialPath {φ₀ φ : E → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : E) :
    fderiv ℝ (gradient (potentialPath φ₀ φ t)) x =
      (1 - t) • fderiv ℝ (gradient φ₀) x + t • fderiv ℝ (gradient φ) x := by
  have he : gradient (potentialPath φ₀ φ t) =
      fun y => (1 - t) • gradient φ₀ y + t • gradient φ y :=
    funext (gradient_potentialPath (hφ₀.differentiable (by simp))
      (hφ.differentiable (by simp)) t)
  rw [he]
  exact (((contDiff_gradient hφ₀).differentiable (by simp) x).hasFDerivAt.const_smul
    (1 - t)).fun_add
    (((contDiff_gradient hφ).differentiable (by simp) x).hasFDerivAt.const_smul t)
    |>.fderiv

/-- The associated Hessian quadratic form is the literal affine interpolation. -/
theorem hessian_potentialPath {φ₀ φ : E → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x v : E) :
    inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v =
      (1 - t) * inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v +
        t * inner ℝ ((fderiv ℝ (gradient φ) x) v) v := by
  rw [fderiv_gradient_potentialPath hφ₀ hφ]
  simp only [add_apply, smul_apply,
    inner_add_left, real_inner_smul_left]

/-- Positive definiteness is preserved for every prescribed path parameter. -/
theorem hessian_potentialPath_pos {φ₀ φ : E → ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ)
    (h₀ : ∀ x v : E, v ≠ 0 →
      0 < inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v)
    (h : ∀ x v : E, v ≠ 0 →
      0 < inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x v : E) (hv : v ≠ 0) :
    0 < inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v := by
  rw [hessian_potentialPath hφ₀ hφ]
  by_cases ht1 : t = 1
  · simpa [ht1] using h x v hv
  have hw : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
  exact (mul_pos hw (h₀ x v hv)).trans_le
    (le_add_of_nonneg_right (mul_nonneg ht.1 (h x v hv).le))

/-- Endpoint Hessian lower bounds interpolate with their actual affine weights. -/
theorem hessian_potentialPath_weighted_lowerBound {φ₀ φ : E → ℝ} {c₀ c : ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ)
    (h₀ : ∀ x v, c₀ * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v)
    (h : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x v : E) :
    ((1 - t) * c₀ + t * c) * ‖v‖ ^ 2 ≤
      inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v := by
  rw [hessian_potentialPath hφ₀ hφ]
  simpa only [add_mul, mul_assoc] using add_le_add
    (mul_le_mul_of_nonneg_left (h₀ x v) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (h x v) ht.1)

/-- One quantitative lower bound holds uniformly on the whole parameter interval. -/
theorem hessian_potentialPath_lowerBound {φ₀ φ : E → ℝ} {c₀ c : ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ)
    (h₀ : ∀ x v, c₀ * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v)
    (h : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x v : E) :
    min c₀ c * ‖v‖ ^ 2 ≤
      inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v := by
  have hmin : min c₀ c ≤ (1 - t) * c₀ + t * c := by
    have h₀' := mul_le_mul_of_nonneg_left (min_le_left c₀ c) (sub_nonneg.mpr ht.2)
    have h' := mul_le_mul_of_nonneg_left (min_le_right c₀ c) ht.1
    nlinarith
  exact (mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖v‖)).trans
    (hessian_potentialPath_weighted_lowerBound hφ₀ hφ h₀ h ht x v)

/-- One finite upper quadratic-form bound is likewise uniform along the path. -/
theorem hessian_potentialPath_upperBound {φ₀ φ : E → ℝ} {C₀ C : ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ)
    (h₀ : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v ≤ C₀ * ‖v‖ ^ 2)
    (h : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x v : E) :
    inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v ≤
      max C₀ C * ‖v‖ ^ 2 := by
  rw [hessian_potentialPath hφ₀ hφ]
  have h₀' := (h₀ x v).trans
    (mul_le_mul_of_nonneg_right (le_max_left C₀ C) (sq_nonneg ‖v‖))
  have h' := (h x v).trans
    (mul_le_mul_of_nonneg_right (le_max_right C₀ C) (sq_nonneg ‖v‖))
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left h₀' (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left h' ht.1)
  convert hsum using 1
  ring

/-- Positive endpoint lower bounds give a fixed positive lower bound and a
fixed finite upper bound for every member of the actual interpolation. -/
theorem potentialPath_uniform_hessian_bounds {φ₀ φ : E → ℝ} {c₀ c C₀ C : ℝ}
    (hφ₀ : ContDiff ℝ ∞ φ₀) (hφ : ContDiff ℝ ∞ φ)
    (hc₀ : 0 < c₀) (hc : 0 < c)
    (hl₀ : ∀ x v, c₀ * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v)
    (hl : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) x) v) v)
    (hu₀ : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ₀) x) v) v ≤ C₀ * ‖v‖ ^ 2)
    (hu : ∀ x v, inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2) :
    0 < min c₀ c ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x v : E,
      min c₀ c * ‖v‖ ^ 2 ≤
          inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v ∧
        inner ℝ ((fderiv ℝ (gradient (potentialPath φ₀ φ t)) x) v) v ≤
          max C₀ C * ‖v‖ ^ 2 := by
  refine ⟨lt_min hc₀ hc, fun t ht x v => ⟨?_, ?_⟩⟩
  · exact hessian_potentialPath_lowerBound hφ₀ hφ hl₀ hl ht x v
  · exact hessian_potentialPath_upperBound hφ₀ hφ hu₀ hu ht x v

/-- The Riesz gradient of a differentiable degree-two potential has degree one. -/
theorem gradient_smul_of_homogeneous_two {φ : E → ℝ}
    (hφ : Differentiable ℝ φ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φ (r • x) = r ^ 2 * φ x)
    {r : ℝ} (hr : 0 < r) (x : E) :
    gradient φ (r • x) = r • gradient φ x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  ext v
  simp only [map_smul, toDual_gradient, smul_apply, smul_eq_mul]
  exact fderiv_apply_smul_of_homogeneous_two hhom hr (hφ x) (hφ (r • x)) v

/-- A global smooth extension of a punctured smooth homogeneous potential has
a global finite actual Hessian operator bound. Compactness controls the inner
ball and the homogeneous Hessian controls the unchanged exterior. -/
theorem exists_hessian_norm_bound_of_homogeneous_end [ProperSpace E]
    {φ φEnd : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hφ : ContDiff ℝ ∞ φ) (hφEnd : ContDiff ℝ 1 φEnd)
    (hφEnds : ∀ x ≠ 0, ContDiffAt ℝ ∞ φEnd x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, φEnd (r • x) = r ^ 2 * φEnd x)
    (hend : ∀ x, R ≤ ‖x‖ → φ x = φEnd x) :
    ∃ C > 0, ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ C := by
  obtain ⟨C, hC, hCb⟩ := exists_fderiv_bound_of_homogeneous_one
    (fun x hx => contDiffAt_gradient (hφEnds x hx))
    (fun r hr x => gradient_smul_of_homogeneous_two
      (hφEnd.differentiable (by simp)) hhom hr x)
  have hcont : Continuous (fderiv ℝ (gradient φ)) :=
    (contDiff_gradient hφ).continuous_fderiv (by simp)
  obtain ⟨D, hDb⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C D, hC.trans_le (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : ‖x‖ ≤ R
  · exact (hDb x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)).trans
      (le_max_right _ _)
  have hRx : R < ‖x‖ := lt_of_not_ge hx
  have he : φ =ᶠ[𝓝 x] φEnd := by
    filter_upwards [continuous_const.continuousAt.eventually_lt
      continuous_norm.continuousAt hRx] with y hy
    exact hend y hy.le
  rw [he.gradient.fderiv_eq]
  exact (hCb x (by
    intro hx0
    simp only [hx0, norm_zero] at hRx
    linarith)).trans (le_max_left _ _)

/-- An operator bound on the actual Hessian gives the corresponding
quadratic-form upper bound. -/
theorem hessian_upperBound_of_norm_bound {φ : E → ℝ} {C : ℝ}
    (hbound : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ C) (x v : E) :
    inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤ C * ‖v‖ ^ 2 := by
  calc
    inner ℝ ((fderiv ℝ (gradient φ) x) v) v ≤
        ‖(fderiv ℝ (gradient φ) x) v‖ * ‖v‖ := by
      exact (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using
          norm_inner_le_norm (𝕜 := ℝ) ((fderiv ℝ (gradient φ) x) v) v)
    _ ≤ (C * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (((fderiv ℝ (gradient φ) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg v))) (norm_nonneg v)
    _ = C * ‖v‖ ^ 2 := by ring

/-- The prescribed initial quadratic potential has identity Riesz gradient. -/
theorem gradient_half_norm_sq (x : E) :
    gradient (fun y : E => ‖y‖ ^ 2 / 2) x = x := by
  have hd : HasFDerivAt (fun y : E => ‖y‖ ^ 2 / 2) (innerSL ℝ x) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
    · funext y
      ring
    · ext v
      simp [smul_apply]
  exact (show HasGradientAt (fun y : E => ‖y‖ ^ 2 / 2) x x from hd).gradient

/-- Its actual Hessian is the identity, in the fixed Euclidean norm. -/
theorem hessian_half_norm_sq (x v : E) :
    inner ℝ ((fderiv ℝ (gradient (fun y : E => ‖y‖ ^ 2 / 2)) x) v) v = ‖v‖ ^ 2 := by
  have he : gradient (fun y : E => ‖y‖ ^ 2 / 2) = id := funext gradient_half_norm_sq
  rw [he]
  simp

end InnerProduct

/-- The actual toric compatible potential admits the source's fixed smooth
interpolation from the prescribed quadratic potential, with positive lower
and finite upper Hessian constants uniform in the entire parameter interval.
The end is the actual strongly compatible homogeneous potential. -/
theorem ToricInput.exists_compatiblePotential_with_uniform_path {n : ℕ} (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧
      ContDiff ℝ ∞ φ ∧
      (∃ R > 0,
        (∀ x, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ → φ x = φEnd x) ∧
        (∀ t x, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ →
          potentialPath (fun u => realSquaredNorm u / 2) φ t x =
            potentialPath (fun u => realSquaredNorm u / 2) φEnd t x)) ∧
      (∀ t r : ℝ, 0 < r → ∀ x,
        potentialPath (fun u => realSquaredNorm u / 2) φEnd t (r • x) =
          r ^ 2 * potentialPath (fun u => realSquaredNorm u / 2) φEnd t x) ∧
      ContDiff ℝ ∞ (fun p : ℝ × RealSpace n =>
        potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ x v : EuclideanSpace ℝ (Fin n),
          c * ‖v‖ ^ 2 ≤ inner ℝ
              ((fderiv ℝ (gradient (potentialPath
                (fun u => realSquaredNorm u / 2) φ t ∘
                  EuclideanSpace.equiv (Fin n) ℝ)) x) v) v ∧
            inner ℝ
              ((fderiv ℝ (gradient (potentialPath
                (fun u => realSquaredNorm u / 2) φ t ∘
                  EuclideanSpace.equiv (Fin n) ℝ)) x) v) v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨φEnd, hstrong, hφEnd1, hφEnd0, δ, hδ, hconv, hlower, _⟩ :=
    I.exists_stronglyCompatibleEndPotential
  obtain ⟨φ, hφs, hφb, _, ⟨R, hR, hend⟩, _⟩ :=
    exists_native_smooth_extension_with_legendre hδ hφEnd1.continuous hφEnd0
      hstrong.smooth hconv hlower
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφEs : ContDiff ℝ ∞ (φ ∘ e) := hφs.comp e.contDiff
  have hφEndEs : ∀ x ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) x :=
    fun x hx => (hstrong.smooth (e x) (by simpa [e] using hx)).comp x e.contDiff.contDiffAt
  have hhom : ∀ r : ℝ, 0 < r → ∀ x, (φEnd ∘ e) (r • x) = r ^ 2 * (φEnd ∘ e) x := by
    intro r hr x
    simp only [Function.comp_apply, map_smul]
    exact hstrong.homogeneous r hr (e x)
  obtain ⟨C, hC, hCb⟩ := exists_hessian_norm_bound_of_homogeneous_end hR hφEs
    (hφEnd1.comp e.contDiff) hφEndEs hhom (fun x hx => by simpa [e] using hend (e x) hx)
  have hq : ContDiff ℝ ∞ (fun u : RealSpace n => realSquaredNorm u / 2) :=
    contDiff_realSquaredNorm.div_const 2
  have hqhom : ∀ r : ℝ, 0 < r → ∀ x : RealSpace n,
      realSquaredNorm (r • x) / 2 = r ^ 2 * (realSquaredNorm x / 2) := by
    intro r _ x
    rw [realSquaredNorm_smul]
    ring
  have hqE : (fun u : RealSpace n => realSquaredNorm u / 2) ∘ e =
      fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2 := by
    ext x
    simp [e]
  have hqEs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2) :=
    (contDiff_id.norm_sq ℝ).div_const 2
  have hqbl (x v : EuclideanSpace ℝ (Fin n)) :
      (1 : ℝ) * ‖v‖ ^ 2 ≤
        inner ℝ ((fderiv ℝ (gradient (fun y => ‖y‖ ^ 2 / 2)) x) v) v := by
    simp [hessian_half_norm_sq]
  have hqbu (x v : EuclideanSpace ℝ (Fin n)) :
      inner ℝ ((fderiv ℝ (gradient (fun y => ‖y‖ ^ 2 / 2)) x) v) v ≤
        (1 : ℝ) * ‖v‖ ^ 2 := by
    simp [hessian_half_norm_sq]
  refine ⟨φEnd, φ, hstrong, hφEnd1, hφs,
    ⟨R, hR, hend, fun t x hx => potentialPath_eq_of_eq_right (hend x hx) t⟩,
    fun t r hr x => potentialPath_homogeneous_two hqhom hstrong.homogeneous t r hr x,
    potentialPath_contDiff hq hφs, min 1 δ, max 1 C,
    lt_min zero_lt_one hδ, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro t ht x v
  rw [potentialPath_comp, hqE]
  exact ⟨hessian_potentialPath_lowerBound hqEs hφEs hqbl hφb ht x v,
    hessian_potentialPath_upperBound hqEs hφEs hqbu
      (hessian_upperBound_of_norm_bound hCb) ht x v⟩

end FsFltz
