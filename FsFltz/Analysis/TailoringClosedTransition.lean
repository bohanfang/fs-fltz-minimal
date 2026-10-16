import FsFltz.Analysis.TailoringBadSeparation

/-!
# Closed transition strips and strict cutoff plateaus

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1452–1461.
The existing transition exclusion is strengthened to include both plateau
boundaries. This supplies strict inequalities, rather than merely pointwise
cutoff values, for constructing actual open holomorphic neighborhoods.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- Even at the plateau boundaries, a weight in the closed transition strip
becomes active at every normalized position limit. -/
theorem pairing_limit_eq_one_of_tailoring_closed_strip
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (u : ℕ → RealSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (u j) ≤ B)
    (hstrip : ∀ᶠ j in atTop,
      tailoringMaxWeight I (β j) (u j) - Real.sqrt (β j) - 2 ≤
        tailoringWeight (β j) a (u j) ∧
      tailoringWeight (β j) a (u j) ≤
        tailoringMaxWeight I (β j) (u j) - Real.sqrt (β j))
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • u j) atTop (𝓝 x)) :
    pairing a x = 1 := by
  have hinv : Tendsto (fun j => (β j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hβ
  have hsqrt : Tendsto (fun j => Real.sqrt (β j) / β j) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hβ)
  have hlo : Tendsto (fun j => (-Real.sqrt (β j) - 2) / β j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, sub_mul, neg_mul, neg_zero, mul_zero, sub_zero]
      using hsqrt.neg.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
  have hhi : Tendsto (fun j => (B - Real.sqrt (β j)) / β j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, sub_mul, mul_zero, sub_zero]
      using ((tendsto_const_nhds (x := B)).mul hinv).sub hsqrt
  have hweight : Tendsto (fun j => tailoringWeight (β j) a (u j) / β j)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [hstrip, hβ.eventually (eventually_gt_atTop 0)] with j hj hp
      have hmax : 0 ≤ tailoringMaxWeight I (β j) (u j) := le_max_left _ _
      exact div_le_div_of_nonneg_right (by linarith [hj.1]) hp.le
    · filter_upwards [hB, hstrip, hβ.eventually (eventually_gt_atTop 0)] with j hj hs hp
      exact div_le_div_of_nonneg_right (by linarith [hs.2]) hp.le
  have hp : Tendsto (fun j => pairing a ((β j)⁻¹ • u j)) atTop (𝓝 1) := by
    have hw : Tendsto (fun j => 1 + tailoringWeight (β j) a (u j) / β j)
        atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hweight
    apply hw.congr'
    filter_upwards [hβ.eventually (eventually_gt_atTop 0)] with j hj
    rw [tailoringWeight_vertex I (β j) ⟨a, ha⟩, pairing_smul_real]
    field_simp [hj.ne']
    ring
  exact tendsto_nhds_unique (pairing_normalized_tendsto a β u x hx) hp

/-- The actual retained coefficient vanishes in every bounded-weight
closed-strip sequence, including at unchanged cutoff endpoints. -/
theorem tailoringRetainedMonomial_tendsto_zero_of_closed_strip
    (I : ToricInput n) (a : Lattice n) (ha : a ∈ I.vertices)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (hstrip : ∀ᶠ j in atTop, tailoringWeight (β j) a (y j).1 ≤
      tailoringMaxWeight I (β j) (y j).1 - Real.sqrt (β j)) :
    Tendsto (fun j => tailoringRetainedMonomial I (β j) a (y j)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun j => Real.exp B * Real.exp (-Real.sqrt (β j)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_sqrt_atTop.comp hβ))
  apply squeeze_zero_norm' _ hexp
  filter_upwards [hB, hstrip] with j hj hs
  calc
    ‖tailoringRetainedMonomial I (β j) a (y j)‖ ≤
        ‖monomial (Real.exp (-β j) : ℂ) a (y j)‖ := by
      rw [tailoringRetainedMonomial, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (tailoringCutoff_nonneg I (β j) a (y j).1)]
      exact mul_le_of_le_one_left (norm_nonneg _) (tailoringCutoff_le_one I (β j) a (y j).1)
    _ = Real.exp (tailoringWeight (β j) a (y j).1) :=
      norm_tailoring_monomial I (β j) ⟨a, ha⟩ (y j)
    _ ≤ Real.exp (B - Real.sqrt (β j)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]

/-- A closed-strip exponent cannot occur in an actual convergent sequence
whose relative conormal errors tend to zero. -/
theorem not_tailoring_closed_strip_conormal_limit
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (a : Lattice n) (ha : a ∈ I.vertices)
    (hstrip : ∀ᶠ j in atTop,
      tailoringMaxWeight I (β j) (y j).1 - Real.sqrt (β j) - 2 ≤
        tailoringWeight (β j) a (y j).1 ∧
      tailoringWeight (β j) a (y j).1 ≤
        tailoringMaxWeight I (β j) (y j).1 - Real.sqrt (β j))
    (x : RealSpace n) (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (q : Lattice n → ℂ)
    (hq : ∀ v ∈ I.vertices, Tendsto (fun j => tailoringRetainedMonomial I (β j) v (y j))
      atTop (𝓝 (q v)))
    (t : ℕ → ℂ) (τ : ℂ)
    (ht : Tendsto (fun j => ((β j)⁻¹ : ℂ) * t j) atTop (𝓝 τ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ᶠ j in atTop,
      ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤
          δ j * ‖coordinateGradient φ (y j).1‖) : False := by
  have hax := pairing_limit_eq_one_of_tailoring_closed_strip I a ha β
    (fun j => (y j).1) hβ B hB hstrip x hx
  have hxP : x ∈ polarPolytope I := (mem_polarPolytope_iff I x).mpr
    (fun v hv => pairing_limit_le_one_of_bounded_tailoringMaxWeight I v hv β
      (fun j => (y j).1) hβ B hB x hx)
  have hx₀ := ne_zero_of_mem_polarFacet I a ⟨hxP, hax⟩
  have hxlevel := supportHeight_eq_one_of_mem_polarFacet I ha ⟨hxP, hax⟩
  have hqoff : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0 := by
    intro v hv hvlt
    exact tendsto_nhds_unique (hq v hv)
      (tailoringRetainedMonomial_tendsto_zero_of_pairing_limit_lt_one I v hv β y hβ x hx hvlt)
  have hp := tailoring_conormal_equation_of_normalized_limits hφ β y hβ
    x hx₀ hx q hq t τ ht δ hδ herr
  have hqane := hφ.active_complex_conormal_coefficient_ne_zero hxP hxlevel q τ hqoff hp ha hax
  have hqazero : q a = 0 := tendsto_nhds_unique (hq a ha)
    (tailoringRetainedMonomial_tendsto_zero_of_closed_strip I a ha β y hβ B hB
      (hstrip.mono fun _ h => h.2))
  exact hqane hqazero

/-- Uniform positive conormal separation holds on the full closed strip,
including points where the cutoff has already reached zero or one. -/
theorem tailoringEndpoint_exists_uniform_closed_strip_conormal_separation
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ v ∈ tailoringExponents I,
        tailoringMaxWeight I β y.1 - Real.sqrt β - 2 ≤ tailoringWeight β v y.1 ∧
        tailoringWeight β v y.1 ≤ tailoringMaxWeight I β y.1 - Real.sqrt β) →
      ∀ t : ℂ, δ * ‖coordinateGradient φ y.1‖ ≤
        ‖(fun k => (coordinateGradient φ y.1 k : ℂ)) - t • tailoringRetainedNormal I β y‖ := by
  classical
  by_contra! hno
  have hex (j : ℕ) : ∃ β ≥ (j : ℝ) + 1, ∃ y : LGSpace n,
      tailoringFamily I β 1 y = 1 ∧
      (∃ v ∈ tailoringExponents I,
        tailoringMaxWeight I β y.1 - Real.sqrt β - 2 ≤ tailoringWeight β v y.1 ∧
        tailoringWeight β v y.1 ≤ tailoringMaxWeight I β y.1 - Real.sqrt β) ∧
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
  obtain ⟨⟨C, hC⟩, _, ρ, hρ, x, _, q, τ, hx, hq, ht⟩ :=
    tailoringEndpoint_extract_small_conormal_subsequence I hφ ha hlower β y t ε hβ hε
      (Filter.Eventually.of_forall hy) (Filter.Eventually.of_forall fun j => (herr j).le)
  have hvertex : ∀ᶠ j in atTop, ∃ v ∈ I.vertices,
      tailoringMaxWeight I (β (ρ j)) (y (ρ j)).1 - Real.sqrt (β (ρ j)) - 2 ≤
        tailoringWeight (β (ρ j)) v (y (ρ j)).1 ∧
      tailoringWeight (β (ρ j)) v (y (ρ j)).1 ≤
        tailoringMaxWeight I (β (ρ j)) (y (ρ j)).1 - Real.sqrt (β (ρ j)) := by
    filter_upwards [hρ.tendsto_atTop.eventually hC,
      (Real.tendsto_sqrt_atTop.comp (hβ.comp hρ.tendsto_atTop)).eventually
        (eventually_gt_atTop C)] with j hj hsqrt
    change C < Real.sqrt (β (ρ j)) at hsqrt
    obtain ⟨v, hv, hlo, hhi⟩ := hbad (ρ j)
    refine ⟨v, ?_, hlo, hhi⟩
    have hv₀ : v ≠ 0 := by
      intro he
      subst v
      rw [tailoringWeight_zero] at hhi
      linarith
    exact (Finset.mem_insert.mp hv).resolve_left hv₀
  obtain ⟨v, hv, hvfreq⟩ := (I.vertices.frequently_exists).mp hvertex.frequently
  obtain ⟨s, hs, hstrans⟩ := subseq_forall_of_frequently
    (x := fun j : ℕ => j)
    (p := fun j =>
      tailoringMaxWeight I (β (ρ j)) (y (ρ j)).1 - Real.sqrt (β (ρ j)) - 2 ≤
        tailoringWeight (β (ρ j)) v (y (ρ j)).1 ∧
      tailoringWeight (β (ρ j)) v (y (ρ j)).1 ≤
        tailoringMaxWeight I (β (ρ j)) (y (ρ j)).1 - Real.sqrt (β (ρ j)))
    tendsto_id hvfreq
  have hβ' : Tendsto (fun j => β (ρ (s j))) atTop atTop :=
    hβ.comp (hρ.tendsto_atTop.comp hs)
  have hC' : ∀ᶠ j in atTop, tailoringMaxWeight I (β (ρ (s j))) (y (ρ (s j))).1 ≤ C :=
    (hρ.tendsto_atTop.comp hs).eventually hC
  have ht' : Tendsto (fun j => ((β (ρ (s j)))⁻¹ : ℂ) * t (ρ (s j)))
      atTop (𝓝 τ) := by
    simpa only [div_eq_inv_mul, Function.comp_def] using ht.comp hs
  exact not_tailoring_closed_strip_conormal_limit hφ
    (fun j => β (ρ (s j))) (fun j => y (ρ (s j))) hβ' C hC' v hv
    (Filter.Eventually.of_forall hstrans) x (hx.comp hs) q
    (fun v hv => (hq v hv).comp hs) (fun j => t (ρ (s j))) τ ht'
    (fun j => ε (ρ (s j))) (hε.comp (hρ.tendsto_atTop.comp hs))
    (Filter.Eventually.of_forall fun j => (herr (ρ (s j))).le)

end FsFltz
