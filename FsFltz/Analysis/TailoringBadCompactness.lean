import FsFltz.Analysis.TailoringSmallConormal

/-!
# Actual compact subsequences for small tailored conormal errors

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1401–1408.
The quantitative localization and actual retained-normal lower bound supply
compactness of all three normalized variables on one common subsequence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology BigOperators

variable {n : ℕ}

theorem tailoringEndpoint_extract_small_conormal_subsequence
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (t : ℕ → ℂ) (ε : ℕ → ℝ)
    (hβ : Tendsto β atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hy : ∀ᶠ j in atTop, tailoringFamily I (β j) 1 (y j) = 1)
    (he : ∀ᶠ j in atTop,
      ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤
          ε j * ‖coordinateGradient φ (y j).1‖) :
    (∃ C : ℝ, ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ C) ∧
    (∀ᶠ j in atTop, tailoringCutoff I (β j) 0 (y j).1 = 1) ∧
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ x : RealSpace n, x ≠ 0 ∧
      ∃ q : Lattice n → ℂ, ∃ τ : ℂ,
        Tendsto (fun j => (β (ρ j))⁻¹ • (y (ρ j)).1) atTop (𝓝 x) ∧
        (∀ v ∈ I.vertices, Tendsto
          (fun j => tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j))) atTop (𝓝 (q v))) ∧
        Tendsto (fun j => t (ρ j) / (β (ρ j) : ℂ)) atTop (𝓝 τ) := by
  classical
  obtain ⟨δ, hδ, M, hM, C, hC, d, hd, D, hD, B, hB, hloc⟩ :=
    tailoringEndpoint_exists_small_conormal_localization I hφ ha hlower
  obtain ⟨δ', hδ', T, hT, B', hB', ht⟩ :=
    tailoringEndpoint_exists_approximant_linear_bound I hφ ha hlower
  have hgood : ∀ᶠ j in atTop,
      0 < β j ∧ tailoringCutoff I (β j) 0 (y j).1 = 1 ∧
      tailoringMaxWeight I (β j) (y j).1 ≤ C ∧
      d ≤ ‖(β j)⁻¹ • (y j).1‖ ∧
      ‖(β j)⁻¹ • (y j).1‖ ≤ D ∧
      (∀ v ∈ I.vertices, ‖tailoringRetainedMonomial I (β j) v (y j)‖ ≤ M) ∧
      ‖t j / (β j : ℂ)‖ ≤ T := by
    filter_upwards [hy, he, hβ.eventually (eventually_ge_atTop B),
      hβ.eventually (eventually_ge_atTop B'), hε.eventually_lt_const hδ,
      hε.eventually_lt_const hδ'] with j hj hej hBj hBj' hδj hδj'
    have hp : 0 < β j := hB.trans_le hBj
    have herr : ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤ δ * ‖coordinateGradient φ (y j).1‖ :=
      hej.trans (mul_le_mul_of_nonneg_right hδj.le (norm_nonneg _))
    obtain ⟨_, hm, hz, hh, hl, hu⟩ := hloc (β j) hBj (y j) hj ⟨t j, herr⟩
    have htn := ht (β j) hBj' (y j) hj (t j)
      (hej.trans (mul_le_mul_of_nonneg_right hδj'.le (norm_nonneg _)))
    have hunorm : ‖(β j)⁻¹ • (y j).1‖ = ‖(y j).1‖ / β j := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hp, div_eq_inv_mul]
    refine ⟨hp, hz, ?_, ?_, ?_, ?_, ?_⟩
    · exact max_le hC.le (le_trans (le_abs_self _) hh)
    · rw [hunorm]
      exact (le_div_iff₀ hp).mpr hl
    · rw [hunorm]
      exact (div_le_iff₀ hp).mpr hu
    · intro v hv
      exact (norm_tailoringRetainedMonomial_le_max I (β j) v hv (y j)).trans hm
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact (div_le_iff₀ hp).mpr htn
  refine ⟨⟨C, hgood.mono (fun j hj => hj.2.2.1)⟩,
    hgood.mono (fun j hj => hj.2.1), ?_⟩
  let V := {v : Lattice n // v ∈ I.vertices}
  let X := RealSpace n × ((V → ℂ) × ℂ)
  let z : ℕ → X := fun j => ((β j)⁻¹ • (y j).1,
    ((fun v => tailoringRetainedMonomial I (β j) v.val (y j)), t j / (β j : ℂ)))
  let R := max D (max M T)
  have hz : ∀ᶠ j in atTop, z j ∈ Metric.closedBall (0 : X) R := by
    filter_upwards [hgood] with j hj
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_prod_le_iff.mpr
    refine ⟨hj.2.2.2.2.1.trans (le_max_left _ _), ?_⟩
    apply norm_prod_le_iff.mpr
    constructor
    · apply (pi_norm_le_iff_of_nonneg (hD.le.trans (le_max_left _ _))).mpr
      intro v
      exact (hj.2.2.2.2.2.1 v.val v.property).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact hj.2.2.2.2.2.2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨w, _, ρ, hρ, hw⟩ := (isCompact_closedBall (0 : X) R).tendsto_subseq' hz.frequently
  have hx : Tendsto (fun j => (β (ρ j))⁻¹ • (y (ρ j)).1) atTop (𝓝 w.1) := hw.fst_nhds
  have hxne : w.1 ≠ 0 := by
    have hl : d ≤ ‖w.1‖ := ge_of_tendsto hx.norm (by
      filter_upwards [hρ.tendsto_atTop.eventually hgood] with j hj
      exact hj.2.2.2.1)
    intro heq
    rw [heq, norm_zero] at hl
    exact (not_le_of_gt hd) hl
  let q : Lattice n → ℂ := fun v => if hv : v ∈ I.vertices then w.2.1 ⟨v, hv⟩ else 0
  refine ⟨ρ, hρ, w.1, hxne, q, w.2.2, hx, ?_, hw.snd_nhds.snd_nhds⟩
  intro v hv
  simpa only [q, dite_eq_left hv, Function.comp_def, z] using
    (continuous_apply (⟨v, hv⟩ : V)).tendsto w.2.1 |>.comp hw.snd_nhds.fst_nhds

end FsFltz
