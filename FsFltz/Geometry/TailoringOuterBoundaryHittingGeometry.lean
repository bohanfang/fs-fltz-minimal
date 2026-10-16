import FsFltz.Geometry.TailoringFiniteBandHittingRadial
import FsFltz.Analysis.TailoringExhaustionDomain

/-!
# The fixed outer potential level and the actual conormal section

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1784–1789.
A fixed radius constant enclosing the whole actual core is constructed
from finite support-height bounds and the native Hessian upper bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

private theorem outerBoundary_gradient_radius_pos {p : RealSpace n} (hp : p ≠ 0) :
    0 < Real.sqrt (realSquaredNorm p) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  rw [← e.apply_symm_apply p, realSquaredNorm_euclidean, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr (by simpa [e] using hp)

/-- Every point of the entire nonzero actual conic set lies on a positive
radial continuation of an actual core point. -/
theorem IsStronglyCompatibleEndPotential.eventually_conormal_eq_positive_core_ray
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, ∀ y ∈ tailoringLegendreConic I φEnd,
      ∃ z ∈ tailoringCoreSection I φEnd β, ∃ s : ℝ, 0 < s ∧ y = (s • z.1, z.2) := by
  filter_upwards [hEnd.eventually_coreSection_projection_surjOn Φ hΦeq hΦ₀] with β hsurj
  intro y hy
  obtain ⟨z, hz, hproj⟩ := hsurj (tailoringRadialProjection_mem_link hy)
  let a := Real.sqrt (realSquaredNorm (coordinateGradient φEnd y.1))
  let b := Real.sqrt (realSquaredNorm (coordinateGradient φEnd z.1))
  have ha : 0 < a := outerBoundary_gradient_radius_pos hy.1
  have hb : 0 < b := outerBoundary_gradient_radius_pos hz.1.1
  let s := a * b⁻¹
  have hs : 0 < s := mul_pos ha (inv_pos.mpr hb)
  have hgrad : coordinateGradient φEnd y.1 = s • coordinateGradient φEnd z.1 := by
    have h := congrArg (fun q : Cotangent n => a • q.2) hproj.symm
    simpa only [tailoringRadialProjection, a, b, s, smul_smul,
      mul_inv_cancel₀ ha.ne', one_smul] using h
  have hzne : z.1 ≠ 0 := by
    intro h
    apply hz.1.1
    rw [← hΦeq, h, hΦ₀]
  have hrad : y.1 = s • z.1 := by
    apply Φ.injective
    rw [hΦeq, hΦeq, coordinateGradient_smul_of_homogeneous_two hEnd.homogeneous
      (fun u hu => (hEnd.smooth u hu).differentiableAt (by simp)) hzne hs]
    exact hgrad
  have hangle : y.2 = z.2 := congrArg Prod.fst hproj.symm
  exact ⟨z, hz, s, hs, Prod.ext hrad hangle⟩

/-- One fixed radius constant, chosen before the large parameter, places
the whole actual core strictly below the outer potential boundary. -/
theorem tailoringEndpoint_exists_uniform_core_below_outer_level
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y ∈ tailoringCoreSection I φEnd β, φ y.1 < D ^ 2 * β ^ 2 / 2 := by
  obtain ⟨a, ha, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨Bc, hradial⟩ := eventually_atTop.mp hEnd.eventually_coreSection_eq_radial
  let D₀ : ℝ := (U + 1) / a
  let D : ℝ := D₀ + 1
  have hD₀ : 0 < D₀ := div_pos (by linarith) ha
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, max 1 (max Bc (Real.log (I.vertices.card : ℝ) + H * (R + 1))),
    zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβc : Bc ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : Real.log (I.vertices.card : ℝ) + H * (R + 1) ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hrad : tailoringRadialFunction I β y.1 = 1 := by
    rw [hradial β hβc] at hy
    exact hy.2
  have hh := tailoringRadialFunction_height_bounds I β hrad
  let r : ℝ := Real.sqrt (realSquaredNorm y.1)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hnorm : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ = r := by
    have hs : realSquaredNorm y.1 = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ ^ 2 := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        realSquaredNorm_euclidean ((EuclideanSpace.equiv (Fin n) ℝ).symm y.1)
    dsimp only [r]
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hlarge : R < r := by
    have hhup := (hheight y.1).2
    change supportHeight I y.1 ≤ H * r at hhup
    have : H * (R + 1) ≤ H * r := by linarith
    have hRr : R + 1 ≤ r := (mul_le_mul_iff_right₀ hH).mp this
    linarith
  have he := metricRadialSq_potential_eq_two_mul hEnd1 hEnd.smooth hEnd.homogeneous
    hc hlower hR heq y.1 (by
      change R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖
      rw [hnorm]
      exact hlarge)
  have hup : 2 * φ y.1 ≤ U * r ^ 2 := by
    rw [← he]
    change inner ℝ ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 y.1)) (WithLp.toLp 2 y.1)) (WithLp.toLp 2 y.1) ≤ _
    have hu := hupper (WithLp.toLp 2 y.1) (WithLp.toLp 2 y.1)
    change inner ℝ ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 y.1)) (WithLp.toLp 2 y.1)) (WithLp.toLp 2 y.1) ≤
        U * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ ^ 2 at hu
    simpa only [← hnorm] using hu
  have har : a * r ≤ β := (hheight y.1).1.trans hh.2
  have hbound : (U + 1) * r ≤ D₀ * β := by
    calc
      _ = D₀ * (a * r) := by dsimp only [D₀]; field_simp
      _ ≤ D₀ * β := mul_le_mul_of_nonneg_left har hD₀.le
  have hstrict : (U + 1) * r < D * β := by
    dsimp only [D]
    nlinarith
  have hsq : ((U + 1) * r) ^ 2 < (D * β) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hstrict
  have hUcmp : U ≤ (U + 1) ^ 2 := by nlinarith [sq_nonneg U]
  have hUr := mul_le_mul_of_nonneg_right hUcmp (sq_nonneg r)
  nlinarith

/-- The same fixed outer radius encloses the whole core, and every point
of the literal conic outer potential boundary is strictly beyond base one. -/
theorem tailoringEndpoint_exists_uniform_outer_conormal_base_gt_one
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D ≥ D₀, ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      (∀ z ∈ tailoringCoreSection I φEnd β, φ z.1 < D ^ 2 * β ^ 2 / 2) ∧
      ∀ y ∈ tailoringLegendreConic I φEnd, φ y.1 = D ^ 2 * β ^ 2 / 2 →
        1 < (tailoringFamily I β 1 y).re := by
  obtain ⟨D₀, hD₀, Bc, hBc, hcore₀⟩ := tailoringEndpoint_exists_uniform_core_below_outer_level
    I hc hU hlower hupper hEnd1 hEnd hR heq
  refine ⟨D₀, hD₀, ?_⟩
  intro D hDle
  have hD : 0 < D := hD₀.trans_le hDle
  have hcore : ∀ β ≥ Bc, ∀ z ∈ tailoringCoreSection I φEnd β,
      φ z.1 < D ^ 2 * β ^ 2 / 2 := by
    intro β hβ z hz
    have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD₀.le hDle 2) (sq_nonneg β)
    linarith [hcore₀ β hβ z hz]
  obtain ⟨Br, hpositiveRay⟩ := eventually_atTop.mp
    (hEnd.eventually_conormal_eq_positive_core_ray Φ hΦeq hΦ₀)
  obtain ⟨Bi, hincrease⟩ := eventually_atTop.mp hEnd.eventually_coreSection_outward_base_increasing
  obtain ⟨a, ha, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (R ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bv : ℝ := (2 * max V 0 + 1) / D
  let Bz : ℝ := Real.log (I.vertices.card : ℝ) + H * (R + 1)
  refine ⟨max Bc (max Br (max Bi (max Bv Bz))), hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβc : Bc ≤ β := (le_max_left _ _).trans hβ
  have hβr : Br ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβi : Bi ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβv : Bv ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hβz : Bz ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  refine ⟨hcore β hβc, ?_⟩
  intro y hy hlevel
  have hβpos : 0 < β := hBc.trans_le hβc
  have hApos : 0 < D ^ 2 * β ^ 2 / 2 := by positivity
  have hVA : V < D ^ 2 * β ^ 2 / 2 := by
    have hb : 2 * max V 0 + 1 ≤ D * β := by
      have h := (div_le_iff₀ hD).mp hβv
      simpa only [mul_comm] using h
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 1) hb 2
    nlinarith [le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  have hyfar : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ := by
    by_contra hn
    have hnorm := le_of_not_gt hn
    have hsq : realSquaredNorm y.1 ≤ R ^ 2 := by
      have hs : realSquaredNorm y.1 = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ ^ 2 := by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using
          realSquaredNorm_euclidean ((EuclideanSpace.equiv (Fin n) ℝ).symm y.1)
      rw [hs]
      exact (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hnorm
    have hb := hV (mem_image_of_mem (fun z : LGSpace n => φ z.1)
      (show y ∈ {z : LGSpace n | phi0 z ≤ R ^ 2 / 2} by
        change realSquaredNorm y.1 / 2 ≤ R ^ 2 / 2
        linarith))
    change φ y.1 ≤ V at hb
    rw [hlevel] at hb
    exact (not_le_of_gt hVA) hb
  obtain ⟨z, hz, s, hs, hpoint⟩ := hpositiveRay β hβr y hy
  have hzfar : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖ := by
    have hh := tailoringEndpoint_height_lower I β z hz.2
    have hhup := (hheight z.1).2
    have hnorm : Real.sqrt (realSquaredNorm z.1) = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖ := by
      have he : realSquaredNorm z.1 = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖ ^ 2 := by
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using
          realSquaredNorm_euclidean ((EuclideanSpace.equiv (Fin n) ℝ).symm z.1)
      rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm] at hhup
    dsimp only [Bz] at hβz
    have hhfar : H * (R + 1) ≤ H * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖ := by linarith
    have hr := (mul_le_mul_iff_right₀ hH).mp hhfar
    linarith
  have hφz : φ z.1 = φEnd z.1 := heq z.1 hzfar.le
  have hφy : φ y.1 = φEnd y.1 := heq y.1 hyfar.le
  have he : D ^ 2 * β ^ 2 / 2 = s ^ 2 * φ z.1 := by
    rw [← hlevel, hφy, hpoint]
    exact (hEnd.homogeneous s hs z.1).trans (congrArg (fun v => s ^ 2 * v) hφz.symm)
  have hzpos : 0 < φ z.1 := pos_of_mul_pos_right (he.symm ▸ hApos) (sq_nonneg s)
  have hsone : 1 < s := by
    by_contra hn
    have hsle : s ^ 2 ≤ 1 := by nlinarith [le_of_not_gt hn]
    have hb := mul_le_mul_of_nonneg_right hsle hzpos.le
    have hc := hcore β hβc z hz
    rw [← he] at hb
    linarith
  have hm := (hincrease β hβi z hz).1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hsone.le) hsone
  change (tailoringFamily I β 1 ((1 : ℝ) • z.1, z.2)).re <
    (tailoringFamily I β 1 (s • z.1, z.2)).re at hm
  have hfz : tailoringFamily I β 1 z = 1 := hz.2
  rw [one_smul, hfz, Complex.one_re] at hm
  simpa only [hpoint] using hm

end FsFltz
