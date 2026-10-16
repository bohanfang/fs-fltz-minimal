import FsFltz.Geometry.TailoringAmbientConormalFlow
import FsFltz.Geometry.TailoringAmbientBaseBand

/-!
# Every actual conormal superlevel point lies in the outward core band

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1587–1617,
and `prop:band`, lines 1784–1816. The radial section classifies the whole
norm-one and larger conormal region, not just the original rays of a flow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff

namespace FsFltz
variable {n : ℕ}

private theorem gradient_radius_pos {p : RealSpace n} (hp : p ≠ 0) :
    0 < Real.sqrt (realSquaredNorm p) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  rw [← e.apply_symm_apply p, realSquaredNorm_euclidean, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr (by simpa [e] using hp)

/-- The literal superlevel-one conic region is exactly the entire outward
radial continuation of the actual level-one section. -/
theorem IsStronglyCompatibleEndPotential.eventually_conormal_superlevel_eq_outward_ray
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, ∀ y : LGSpace n,
      y ∈ tailoringLegendreConic I φEnd ∧ 1 ≤ (tailoringFamily I β 1 y).re ↔
        ∃ z ∈ tailoringCoreSection I φEnd β, ∃ r : ℝ,
          1 ≤ r ∧ y = (r • z.1, z.2) := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  have hlog : Real.log (I.vertices.card : ℝ) ≤ L := Real.log_le_log hN (by linarith)
  filter_upwards [hEnd.eventually_coreSection_projection_surjOn Φ hΦ hΦ₀,
    hEnd.eventually_coreSection_eq_radial, hEnd.eventually_cone_family_eq_radial,
    hEnd.eventually_coreSection_outward_ray,
    tailoringRadialFunction_eventually_radial_positive I hL,
    eventually_ge_atTop (Real.log (I.vertices.card : ℝ) + 1)]
    with β hsurj heq hfamily hout hpositive hβ
  intro y
  constructor
  · rintro ⟨hy, hval⟩
    obtain ⟨z, hz, hproj⟩ := hsurj (tailoringRadialProjection_mem_link hy)
    let a := Real.sqrt (realSquaredNorm (coordinateGradient φEnd y.1))
    let b := Real.sqrt (realSquaredNorm (coordinateGradient φEnd z.1))
    have ha : 0 < a := gradient_radius_pos hy.1
    have hb : 0 < b := gradient_radius_pos hz.1.1
    let s := a * b⁻¹
    have hs : 0 < s := mul_pos ha (inv_pos.mpr hb)
    have hgrad : coordinateGradient φEnd y.1 = s • coordinateGradient φEnd z.1 := by
      have h := congrArg (fun q : Cotangent n => a • q.2) hproj.symm
      simpa only [tailoringRadialProjection, a, b, s, smul_smul,
        mul_inv_cancel₀ ha.ne', one_smul] using h
    have hzne : z.1 ≠ 0 := by
      intro h
      apply hz.1.1
      rw [← hΦ, h, hΦ₀]
    have hrad : y.1 = s • z.1 := by
      apply Φ.injective
      rw [hΦ, hΦ, coordinateGradient_smul_of_homogeneous_two hEnd.homogeneous
        (fun u hu => (hEnd.smooth u hu).differentiableAt (by simp)) hzne hs]
      exact hgrad
    have hangle : y.2 = z.2 := congrArg Prod.fst hproj.symm
    have hnorm : 1 ≤ ‖tailoringFamily I β 1 y‖ :=
      hval.trans (Complex.re_le_norm _)
    have hh := tailoringEndpoint_height_lower_of_norm_ge_one I β y hnorm
    obtain ⟨_, σ, hσ, _, hp, hθ⟩ := hy
    have hreal := hfamily σ hσ y hp hθ (by dsimp [L] at hlog; linarith)
    have hradval : 1 ≤ tailoringRadialFunction I β y.1 := by
      rw [hreal, Complex.ofReal_re] at hval
      exact hval
    have hzrad : tailoringRadialFunction I β z.1 = 1 := by
      rw [heq] at hz
      exact hz.2
    have hheightz : 0 < supportHeight I z.1 := by
      linarith [(tailoringRadialFunction_height_bounds I β hzrad).1]
    have hsone : 1 ≤ s := by
      by_contra hnot
      have hslt : s < 1 := lt_of_not_ge hnot
      let g : ℝ → ℝ := fun t => tailoringRadialFunction I β (t • z.1)
      have hg : Continuous g := (contDiff_tailoringRadialFunction I β).continuous.comp
        (continuous_id.smul continuous_const)
      have hmono : StrictMonoOn g (Ici s) := by
        apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici s) hg.continuousOn
          (fun t _ => (hasDerivAt_tailoringRadialFunction_ray I β z.1 t).hasDerivWithinAt)
        intro t ht
        have hst : s ≤ t := interior_subset ht
        have htpos : 0 < t := hs.trans_le hst
        have hhh : β - L ≤ supportHeight I (t • z.1) := by
          rw [I.supportHeight_smul_of_nonneg htpos.le]
          have hhh := hh
          rw [hrad, I.supportHeight_smul_of_nonneg hs.le] at hhh
          have hmul := mul_le_mul_of_nonneg_right hst hheightz.le
          linarith
        have hd := hpositive (t • z.1) hhh
        rw [map_smul, smul_eq_mul] at hd
        exact pos_of_mul_pos_right hd htpos.le
      have hglt := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hslt.le) hslt
      change tailoringRadialFunction I β (s • z.1) <
        tailoringRadialFunction I β ((1 : ℝ) • z.1) at hglt
      rw [← hrad, one_smul, hzrad] at hglt
      exact (not_lt_of_ge hradval) hglt
    exact ⟨z, hz, s, hsone, Prod.ext hrad hangle⟩
  · rintro ⟨z, hz, r, hr, rfl⟩
    obtain ⟨hc, hreal, _⟩ := hout z hz r hr
    have hzrad : tailoringRadialFunction I β z.1 = 1 := by
      rw [heq] at hz
      exact hz.2
    let g : ℝ → ℝ := fun t => tailoringRadialFunction I β (t • z.1)
    have hg : Differentiable ℝ g :=
      ((contDiff_tailoringRadialFunction I β).comp
        (contDiff_id.smul contDiff_const)).differentiable (by simp)
    have hheightz : 0 < supportHeight I z.1 := by
      linarith [(tailoringRadialFunction_height_bounds I β hzrad).1]
    have hmono : MonotoneOn g (Ici 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hg.continuous.continuousOn
        hg.differentiableOn
      intro t ht
      have htone : 1 ≤ t := interior_subset ht
      have htpos : 0 < t := zero_lt_one.trans_le htone
      have hhh : β - L ≤ supportHeight I (t • z.1) := by
        rw [I.supportHeight_smul_of_nonneg htpos.le]
        have hh := (tailoringRadialFunction_height_bounds I β hzrad).1
        have hm := mul_le_mul_of_nonneg_right htone hheightz.le
        simp only [one_mul] at hm
        linarith
      have hd := hpositive (t • z.1) hhh
      rw [map_smul, smul_eq_mul] at hd
      rw [(hasDerivAt_tailoringRadialFunction_ray I β z.1 t).deriv]
      exact (pos_of_mul_pos_right hd htpos.le).le
    refine ⟨hc, ?_⟩
    rw [hreal, Complex.ofReal_re]
    simpa only [g, one_smul, hzrad] using
      hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr) hr

open Geometry Geometry.SmoothManifold
open scoped Manifold

/-- A proved positive speed bound on the whole literal conormal band,
including points whose direction differs from the original core point. -/
theorem tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ tailoringLegendreConic I φEnd,
        1 ≤ (tailoringFamily I β 1 y).re → (tailoringFamily I β 1 y).re ≤ M →
        ∀ K : ℝ, 0 ≤ K → ε ≤
          (complexDifferential (lgManifold n) (tailoringFamily I β 1) y
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K) y)).re := by
  obtain ⟨Ba, hBa, hmargin⟩ := tailoringEndpoint_exists_uniform_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦ hΦ₀ hR heq
  obtain ⟨Br, hradial⟩ := eventually_atTop.mp
    (hEnd.eventually_conormal_superlevel_eq_outward_ray Φ hΦ hΦ₀)
  refine ⟨max Ba Br, hBa.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M
  obtain ⟨ε, hε, hm⟩ := hmargin β ((le_max_left _ _).trans hβ) M
  refine ⟨ε, hε, ?_⟩
  intro y hy hlow hhigh K hK
  obtain ⟨z, hz, r, hr, hpoint⟩ :=
    (hradial β ((le_max_right _ _).trans hβ) y).mp ⟨hy, hlow⟩
  subst y
  exact hm z hz r hr hhigh K hK

end FsFltz
