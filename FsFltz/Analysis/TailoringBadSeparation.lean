import FsFltz.Analysis.TailoringBadLimits
import FsFltz.Analysis.TailoringBadCompactness
import FsFltz.Analysis.TailoringSmallConormalDistance

/-!
# Uniform conormal separation in the actual bad region

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1396–1426.
The bad region is the literal existence of a strictly intermediate cutoff
in the augmented exponent set. All constants follow from the native
potential and the actual endpoint equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- A uniform positive relative distance separates the actual compatible
gradient from every retained complex normal line in the transition region. -/
theorem tailoringEndpoint_exists_uniform_bad_conormal_separation
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ v ∈ tailoringExponents I,
        0 < tailoringCutoff I β v y.1 ∧ tailoringCutoff I β v y.1 < 1) →
      ∀ t : ℂ, δ * ‖coordinateGradient φ y.1‖ ≤
        ‖(fun k => (coordinateGradient φ y.1 k : ℂ)) - t • tailoringRetainedNormal I β y‖ := by
  classical
  by_contra! hno
  have hex (j : ℕ) : ∃ β ≥ (j : ℝ) + 1, ∃ y : LGSpace n,
      tailoringFamily I β 1 y = 1 ∧
      (∃ v ∈ tailoringExponents I,
        0 < tailoringCutoff I β v y.1 ∧ tailoringCutoff I β v y.1 < 1) ∧
      ∃ t : ℂ, ‖(fun k => (coordinateGradient φ y.1 k : ℂ)) -
        t • tailoringRetainedNormal I β y‖ <
          ((j : ℝ) + 1)⁻¹ * ‖coordinateGradient φ y.1‖ := by
    exact hno (((j : ℝ) + 1)⁻¹) (inv_pos.mpr (by positivity))
      ((j : ℝ) + 1) (by positivity)
  choose β hβj y hy hbad t herr using hex
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hindex : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by linarith) tendsto_natCast_atTop_atTop
  have hβ : Tendsto β atTop atTop := tendsto_atTop_mono hβj hindex
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hindex
  obtain ⟨⟨C, hC⟩, hzero, ρ, hρ, x, hx₀, q, τ, hx, hq, ht⟩ :=
    tailoringEndpoint_extract_small_conormal_subsequence I hφ ha hlower β y t ε hβ hε
      (Filter.Eventually.of_forall hy) (Filter.Eventually.of_forall fun j => (herr j).le)
  have hvertex : ∀ᶠ j in atTop, ∃ v ∈ I.vertices,
      0 < tailoringCutoff I (β (ρ j)) v (y (ρ j)).1 ∧
        tailoringCutoff I (β (ρ j)) v (y (ρ j)).1 < 1 := by
    filter_upwards [hρ.tendsto_atTop.eventually hzero] with j hj
    obtain ⟨v, hv, hp, hl⟩ := hbad (ρ j)
    refine ⟨v, ?_, hp, hl⟩
    have hv₀ : v ≠ 0 := by intro he; subst v; rw [hj] at hl; linarith
    exact (Finset.mem_insert.mp hv).resolve_left hv₀
  obtain ⟨v, hv, hvfreq⟩ := (I.vertices.frequently_exists).mp hvertex.frequently
  obtain ⟨s, hs, hstrans⟩ := subseq_forall_of_frequently
    (x := fun j : ℕ => j)
    (p := fun j => 0 < tailoringCutoff I (β (ρ j)) v (y (ρ j)).1 ∧
      tailoringCutoff I (β (ρ j)) v (y (ρ j)).1 < 1) tendsto_id hvfreq
  have hβ' : Tendsto (fun j => β (ρ (s j))) atTop atTop :=
    hβ.comp (hρ.tendsto_atTop.comp hs)
  have hC' : ∀ᶠ j in atTop, tailoringMaxWeight I (β (ρ (s j))) (y (ρ (s j))).1 ≤ C :=
    (hρ.tendsto_atTop.comp hs).eventually hC
  have ht' : Tendsto (fun j => ((β (ρ (s j)))⁻¹ : ℂ) * t (ρ (s j)))
      atTop (𝓝 τ) := by
    simpa only [div_eq_inv_mul, Function.comp_def] using ht.comp hs
  exact not_tailoring_transition_conormal_limit hφ
    (fun j => β (ρ (s j))) (fun j => y (ρ (s j))) hβ' C hC' v hv
    (Filter.Eventually.of_forall hstrans) x (hx.comp hs) q
    (fun v hv => (hq v hv).comp hs) (fun j => t (ρ (s j))) τ ht'
    (fun j => ε (ρ (s j))) (hε.comp (hρ.tendsto_atTop.comp hs))
    (Filter.Eventually.of_forall fun j => (herr (ρ (s j))).le)

/-- The manuscript's bad-region bound for the literal normalized Euclidean
distance to the retained complex normal line. -/
theorem tailoringEndpoint_exists_uniform_bad_conormalDistance_lower_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ v ∈ tailoringExponents I,
        0 < tailoringCutoff I β v y.1 ∧ tailoringCutoff I β v y.1 < 1) →
      ζ ≤ tailoringConormalDistance I φ β y := by
  obtain ⟨δ, hδ, B, hB, hsep⟩ :=
    tailoringEndpoint_exists_uniform_bad_conormal_separation I hφ ha hlower
  obtain ⟨_, _, B', hB', hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨_, _, hangle⟩ := hφ.exists_coordinateGradient_radial_angle ha hlower
  let A := 1 + ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖
  refine ⟨(δ / 2) / (2 * A), by dsimp [A]; positivity, max B B',
    hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy hbad
  have hp : coordinateGradient φ y.1 ≠ 0 :=
    (hangle y.1 (hrad β ((le_max_right _ _).trans hβ) y hy).1).1
  by_contra! hz
  obtain ⟨t, ht⟩ := exists_retained_normal_approximant_of_small_conormalDistance
    I φ β y (show 0 < δ / 2 by positivity) hp hz.le
  have hs := hsep β ((le_max_left _ _).trans hβ) y hy hbad t
  have hn := norm_pos_iff.mpr hp
  have hδn := mul_pos hδ hn
  nlinarith

end FsFltz
