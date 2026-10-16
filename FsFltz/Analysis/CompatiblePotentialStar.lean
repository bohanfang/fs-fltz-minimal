import FsFltz.Analysis.CompatiblePotential
import FsFltz.Analysis.SupportMollificationGradient
import FsFltz.Analysis.PolarFacetGeometry
import FsFltz.Analysis.PolarFanGeometry

/-!
# Open-star compatibility of the actual smoothed gauge

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 595–620.
The finite common-face estimate and the strictly positive convolution weight
of every maximizing vertex are applied to the actual normalized gauge point.
-/

noncomputable section

open Set
open scoped BigOperators Topology ContDiff

namespace FsFltz

variable {n : ℕ}

/-- A small convolution error keeps the smoothed unit level uniformly
away from the origin, in the native product norm. -/
theorem norm_lower_bound_of_mollifiedSupportHeight_eq_one
    (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε ≤ 1 / 2)
    {y : RealSpace n} (hy : mollifiedSupportHeight I ε hε y = 1) :
    1 / 2 ≤ (supportHeightLipschitzConstant I : ℝ) * ‖y‖ := by
  have happrox := (abs_le.mp (mollifiedSupportHeight_approximation I ε hε y)).2
  have hnorm := I.supportHeight_lipschitz.norm_le_mul I.supportHeight_zero y
  rw [hy] at happrox
  have hheight := (le_abs_self (supportHeight I y)).trans hnorm
  linarith

/-- The coordinate gradient of the squared gauge points in exactly the
direction of the smoothed support normal. -/
theorem mollifiedSupportPrepotential_coordinateGradient
    (I : ToricInput n) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (supportHeightLipschitzConstant I : ℝ) * ε < 1)
    {x : RealSpace n} (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      coordinateGradient (mollifiedSupportPrepotential I ε hε) x =
        c • coordinateGradient (mollifiedSupportHeight I ε hε)
          ((mollifiedSupportGauge I ε hε x)⁻¹ • x) := by
  obtain ⟨c, hc, he⟩ := mollifiedSupportPrepotential_fderiv I ε hε hsmall hx
  refine ⟨c, hc, ?_⟩
  ext j
  simp only [coordinateGradient, he, smul_apply, Pi.smul_apply]

/-- All polar facets simultaneously satisfy the source's strict open-star
condition for one sufficiently small, actually constructed smoothing. -/
theorem ToricInput.exists_mollifiedSupportPrepotential_compatible (I : ToricInput n) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      (supportHeightLipschitzConstant I : ℝ) * ε < 1 ∧
      ∀ v ∈ I.vertices, MapsTo (coordinateGradient (mollifiedSupportPrepotential I ε hε))
        (polarFacet I v) (interior (rayStar I v)) := by
  obtain ⟨η, hη, hstar⟩ := I.uniform_subtype_sum_mem_interior_rayStar
  let C : ℝ := supportHeightLipschitzConstant I
  have hC : 0 < C := supportHeightLipschitzConstant_pos I
  let ε : ℝ := min (1 / (4 * C)) (η / (8 * C ^ 2))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have heC : C * ε ≤ 1 / 4 := by
    have he := min_le_left (1 / (4 * C)) (η / (8 * C ^ 2))
    have h := (le_div_iff₀ (show 0 < 4 * C by positivity)).mp he
    dsimp [ε]
    nlinarith
  have heη : 4 * C ^ 2 * ε ≤ η := by
    have he := min_le_right (1 / (4 * C)) (η / (8 * C ^ 2))
    have h := (le_div_iff₀ (show 0 < 8 * C ^ 2 by positivity)).mp he
    change 4 * C ^ 2 * min (1 / (4 * C)) (η / (8 * C ^ 2)) ≤ η
    nlinarith [mul_pos (sq_pos_of_pos hC) hε]
  have hsmall : C * ε < 1 := lt_of_le_of_lt heC (by norm_num)
  refine ⟨ε, hε, hsmall, ?_⟩
  intro v hv x hx
  have hx₀ := ne_zero_of_mem_polarFacet I v hx
  let y := (mollifiedSupportGauge I ε hε x)⁻¹ • x
  have hj := mollifiedSupportGauge_pos I ε hε hsmall hx₀
  have hy₀ : y ≠ 0 := smul_ne_zero (inv_ne_zero hj.ne') hx₀
  have hylevel : mollifiedSupportHeight I ε hε y = 1 :=
    mollifiedSupportGauge_normalization I ε hε hsmall hx₀
  have hynorm : 1 / 2 ≤ C * ‖y‖ :=
    norm_lower_bound_of_mollifiedSupportHeight_eq_one I ε hε (by linarith) hylevel
  have hvmax : pairing v y = supportHeight I y := by
    dsimp [y]
    rw [pairing_smul_real, I.supportHeight_smul_of_nonneg (inv_nonneg.mpr hj.le)]
    rw [pairing_eq_supportHeight_of_mem_polarFacet I hv hx]
  have hweight := supportMollifierVertexWeight_pos_of_maximizer I ε hε y ⟨v, hv⟩ hvmax
  have hgradient : coordinateGradient (mollifiedSupportHeight I ε hε) y ∈
      interior (rayStar I v) := by
    rw [mollifiedSupportHeight_coordinateGradient_eq_weighted_sum]
    apply hstar y hy₀ (supportMollifierVertexWeight I ε hε y)
      (supportMollifierVertexWeight_nonneg I ε hε y) ?_ ⟨v, hv⟩ hweight
    intro w hw
    have hgap := (supportMollifierVertexWeight_deficit_le I ε hε y w hw).2
    have hηnorm := mul_le_mul_of_nonneg_right heη (norm_nonneg y)
    have hscale := mul_le_mul_of_nonneg_left hynorm (show 0 ≤ 4 * C * ε by positivity)
    change supportHeight I y - pairing w.val y ≤ η * ‖y‖
    change supportHeight I y - pairing w.val y ≤ 2 * C * ε at hgap
    nlinarith
  obtain ⟨c, hc, he⟩ := mollifiedSupportPrepotential_coordinateGradient I ε hε hsmall hx₀
  rw [he]
  exact (I.smul_mem_interior_rayStar_iff v _ hc).mpr hgradient

end FsFltz
