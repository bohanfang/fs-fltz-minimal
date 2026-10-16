import FsFltz.Analysis.TailoringCoreRadialEstimates
import FsFltz.Analysis.AngularExclusionGap
import FsFltz.Analysis.TailoringCriticalDifferential
import FsFltz.Analysis.CompatiblePotentialLegendre
import FsFltz.ToricFaceTorus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The actual compact radial section of the tailored fiber

Sources: `geoemtric-part-fsf.tex`, `eq:link`, lines 99–109, and
`geometric-part-fsf-proof.tex`, `lem:radial`, lines 1587–1623.
The section uses the actual endpoint fiber and the native homogeneous
Legendre gradient. All radial estimates are proved from the finite input.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

theorem hasDerivAt_tailoringRadialFunction_ray (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => tailoringRadialFunction I β (r • u))
      (fderiv ℝ (tailoringRadialFunction I β) (t • u) u) t := by
  convert (((contDiff_tailoringRadialFunction I β).differentiable (by simp)
    (t • u)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const u)) using 1 <;>
    simp
  rfl

theorem tailoringRadialFunction_eventually_unique_ray (I : ToricInput n) :
    ∀ᶠ β in atTop, ∀ u : RealSpace n, supportHeight I u = 1 →
      ∃! t : ℝ, 0 < t ∧ tailoringRadialFunction I β (t • u) = 1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  filter_upwards [tailoringRadialFunction_eventually_radial_positive I hL,
    eventually_ge_atTop (L + 1), Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop L)]
    with β hpos hβ hsqrt
  intro u hu
  let f : ℝ → ℝ := fun t => tailoringRadialFunction I β (t • u)
  have hheight {t : ℝ} (ht : 0 ≤ t) : supportHeight I (t • u) = t := by
    rw [I.supportHeight_smul_of_nonneg ht, hu, mul_one]
  have hlo : 0 < β - L := by linarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : β - L ≤ β + Real.log 2 := by linarith
  have hlow : f (β - L) ≤ 1 / 2 := by
    have hb := tailoringRadialFunction_le_of_height_le I β ((β - L) • u)
      (by rw [hheight hlo.le]; linarith)
    rw [hheight hlo.le] at hb
    have he : Real.exp ((β - L) - β) = (2 * (I.vertices.card : ℝ))⁻¹ := by
      rw [show (β - L) - β = -L by ring, Real.exp_neg, Real.exp_log (by positivity)]
    rw [he] at hb
    convert hb using 1
    field_simp
  have hhigh : 2 ≤ f (β + Real.log 2) := by
    have hb := tailoringRadialFunction_max_term_lower I β ((β + Real.log 2) • u)
      (by rw [hheight (by linarith)]; linarith [Real.sqrt_nonneg β])
    rw [hheight (by linarith), add_sub_cancel_left, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hb
    exact hb
  have hf : Continuous f := (contDiff_tailoringRadialFunction I β).continuous.comp
    (continuous_id.smul continuous_const)
  have hmono : StrictMonoOn f (Ici (β - L)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _) hf.continuousOn
      (fun t _ => (hasDerivAt_tailoringRadialFunction_ray I β u t).hasDerivWithinAt)
    intro t ht
    have ht' : β - L ≤ t := interior_subset ht
    have htpos : 0 < t := hlo.trans_le ht'
    have h := hpos (t • u) (by rw [hheight htpos.le]; exact ht')
    rw [map_smul, smul_eq_mul] at h
    exact pos_of_mul_pos_right h htpos.le
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hupper hf.continuousOn
    (show (1 : ℝ) ∈ Icc (f (β - L)) (f (β + Real.log 2)) by constructor <;> linarith)
  refine ⟨t, ⟨hlo.trans_le ht.1, hft⟩, ?_⟩
  intro r hr
  have hrlo : β - L ≤ r := by
    by_contra! hrlow
    have hb := tailoringRadialFunction_le_of_height_le I β (r • u)
      (by rw [hheight hr.1.le]; linarith)
    rw [hheight hr.1.le, hr.2] at hb
    have hexp : Real.exp (r - β) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
    have he : (I.vertices.card : ℝ) * Real.exp (-L) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have := mul_le_mul_of_nonneg_left hexp hN.le
    rw [he] at this
    linarith
  exact hmono.injOn hrlo ht.1 (hr.2.trans hft.symm)

theorem tailoringRadialFunction_height_bounds (I : ToricInput n) (β : ℝ)
    {u : RealSpace n} (hu : tailoringRadialFunction I β u = 1) :
    β - Real.log (I.vertices.card : ℝ) ≤ supportHeight I u ∧ supportHeight I u ≤ β := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hupper : supportHeight I u ≤ β := by
    by_contra! hh
    have hb := tailoringRadialFunction_max_term_lower I β u
      (by linarith [Real.sqrt_nonneg β])
    rw [hu] at hb
    have := Real.exp_le_one_iff.mp hb
    linarith
  refine ⟨?_, hupper⟩
  have hb := tailoringRadialFunction_le_of_height_le I β u hupper
  rw [hu] at hb
  have he : Real.exp (-(Real.log (I.vertices.card : ℝ))) ≤
      Real.exp (supportHeight I u - β) := by
    rw [Real.exp_neg, Real.exp_log hN]
    rw [← one_div]
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hb
  have := Real.exp_le_exp.mp he
  linarith

theorem tailoringRadialFunction_compact_level (I : ToricInput n) (β : ℝ) :
    IsCompact {u : RealSpace n | tailoringRadialFunction I β u = 1} := by
  obtain ⟨c, hc, H, hH, hh⟩ := I.exists_supportHeight_linear_bounds
  have hclosed : IsClosed {u : RealSpace n | tailoringRadialFunction I β u = 1} :=
    isClosed_eq (contDiff_tailoringRadialFunction I β).continuous continuous_const
  apply (isCompact_closedBall (0 : RealSpace n) (max 0 (β / c))).of_isClosed_subset hclosed
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖u‖ ≤ Real.sqrt (realSquaredNorm u) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr
    simpa only [sq_abs] using Finset.single_le_sum (fun k _ => sq_nonneg (u k))
      (Finset.mem_univ j)
  have hb : Real.sqrt (realSquaredNorm u) ≤ β / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      Real.sqrt (realSquaredNorm u) * c = c * Real.sqrt (realSquaredNorm u) := mul_comm _ _
      _ ≤ supportHeight I u := (hh u).1
      _ ≤ β := (tailoringRadialFunction_height_bounds I β hu).2
  exact hnorm.trans (hb.trans (le_max_right _ _))

/-- An outside exponent is exactly absent whenever its deficit exceeds
the fixed retention width. -/
theorem tailoringCutoff_eq_zero_of_large_deficit (I : ToricInput n) (β : ℝ)
    {v : Lattice n} (hv : v ∈ I.vertices) (u : RealSpace n)
    (hgap : Real.sqrt β + 2 ≤ supportHeight I u - pairing v u) :
    tailoringCutoff I β v u = 0 := by
  by_contra hc
  have hret : 0 < tailoringCutoff I β v u :=
    lt_of_le_of_ne (tailoringCutoff_nonneg I β v u) (Ne.symm hc)
  obtain ⟨a, ha⟩ := I.supportHeight_attained u
  have hr := tailoringCutoff_retained_gap I β v u hret a.val
    (Finset.mem_insert_of_mem a.property)
  rw [tailoringWeight_vertex I β ⟨v, hv⟩, tailoringWeight_vertex I β a, ha] at hr
  linarith

/-- The strong angular gap removes all off-cone terms uniformly on the
entire outward radial region. -/
theorem IsStronglyCompatibleEndPotential.eventually_offCone_cutoff_zero
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (L : ℝ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ u : RealSpace n,
      coordinateGradient φ u ∈ σ → β - L ≤ supportHeight I u →
      ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v u = 0 := by
  obtain ⟨δ, hδ, hgap⟩ := hφ.uniform_angularExclusionGap
  obtain ⟨c, hc, H, hH, hh⟩ := I.exists_supportHeight_linear_bounds
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 * H / δ)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (δ * L / H + 3))]
    with β hβ hβδ hβL
  intro σ hσ u hgrad hu v hv hvσ
  apply tailoringCutoff_eq_zero_of_large_deficit I β hv u
  have hsquare := Real.sq_sqrt hβ
  have h₁ : 2 * H ≤ δ * Real.sqrt β := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hβδ
  have h₂ : δ * L + 3 * H ≤ H * Real.sqrt β := by
    have := mul_le_mul_of_nonneg_left hβL hH.le
    field_simp at this
    nlinarith
  have h₃ := mul_le_mul_of_nonneg_right h₁ (Real.sqrt_nonneg β)
  have h₄ := mul_le_mul_of_nonneg_left hu hδ.le
  have h₅ := mul_le_mul_of_nonneg_left (hh u).2 hδ.le
  have h₆ := mul_le_mul_of_nonneg_left (hgap σ hσ u hgrad v hv hvσ) hH.le
  nlinarith

theorem tailoringEndpoint_height_lower (I : ToricInput n) (β : ℝ)
    (y : LGSpace n) (hy : tailoringFamily I β 1 y = 1) :
    β - Real.log (I.vertices.card : ℝ) ≤ supportHeight I y.1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hb := tailoringEndpoint_max_monomial_lower I β y hy
  have hlog := (Real.log_le_iff_le_exp (one_div_pos.mpr hN)).mpr hb
  rw [Real.log_div (by norm_num) hN.ne', Real.log_one, zero_sub] at hlog
  linarith

theorem tailoringEquation_eq_radial_of_offCone (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (y : LGSpace n) (hθ : y.2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v y.1 = 0) :
    tailoringEquation I β y = (tailoringRadialFunction I β y.1 - 1 : ℝ) := by
  have hs : (∑ v ∈ I.vertices, (tailoringCutoff I β v y.1 : ℂ) *
      monomial (Real.exp (-β) : ℂ) v y) =
      ((∑ v ∈ I.vertices, tailoringCutoff I β v y.1 * Real.exp (pairing v y.1 - β) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs : latticeReal v ∈ σ
    · have hc : (character v y.2 : ℂ) = 1 := by simp [character, hθ v hvs]
      simp only [monomial, hc, mul_one, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring
    · simp [hoff v hv hvs]
  simp only [tailoringEquation, tailoringRadialFunction, hs, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_one]
  ring

/-- Equality with the real radial equation holds on the actual conic set,
uniformly from the inner radius to infinity. -/
theorem IsStronglyCompatibleEndPotential.eventually_cone_equation
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ y : LGSpace n,
      coordinateGradient φ y.1 ∈ σ → y.2 ∈ coneTorus σ →
      β - Real.log (2 * (I.vertices.card : ℝ)) ≤ supportHeight I y.1 →
      tailoringEquation I β y = (tailoringRadialFunction I β y.1 - 1 : ℝ) := by
  filter_upwards [hφ.eventually_offCone_cutoff_zero (Real.log (2 * (I.vertices.card : ℝ)))]
    with β hβ
  intro σ hσ y hp hθ hh
  exact tailoringEquation_eq_radial_of_offCone I β σ y hθ (hβ σ hσ y.1 hp hh)

/-- The positive Legendre conic FLTZ set, in the source's `(u,θ)` order. -/
def tailoringLegendreConic (I : ToricInput n) (φ : RealSpace n → ℝ) : Set (LGSpace n) :=
  {y | coordinateGradient φ y.1 ≠ 0 ∧ ∃ σ ∈ faceFan I, σ ≠ {0} ∧
    coordinateGradient φ y.1 ∈ σ ∧ y.2 ∈ coneTorus σ}

/-- The section is the actual endpoint fiber intersected with that conic set. -/
def tailoringCoreSection (I : ToricInput n) (φ : RealSpace n → ℝ) (β : ℝ) : Set (LGSpace n) :=
  tailoringLegendreConic I φ ∩ {y | tailoringFamily I β 1 y = 1}

theorem IsStronglyCompatibleEndPotential.eventually_coreSection_eq_radial
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, tailoringCoreSection I φ β =
      tailoringLegendreConic I φ ∩ {y | tailoringRadialFunction I β y.1 = 1} := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hlog : Real.log (I.vertices.card : ℝ) ≤ Real.log (2 * (I.vertices.card : ℝ)) :=
    Real.log_le_log hN (by linarith)
  filter_upwards [hφ.eventually_cone_equation] with β hβ
  ext y
  constructor
  · intro ⟨hy, hf⟩
    change tailoringFamily I β 1 y = 1 at hf
    rcases hy.2 with ⟨σ, hσ, hσ₀, hp, hθ⟩
    have hh := tailoringEndpoint_height_lower I β y hf
    have he := hβ σ hσ y hp hθ (by linarith)
    have hz : tailoringEquation I β y = 0 := by
      change y ∈ {y | tailoringEquation I β y = 0}
      rw [← tailoringFamily_one_fiber]
      exact hf
    rw [he] at hz
    exact ⟨hy, by exact_mod_cast sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hz)⟩
  · intro ⟨hy, hf⟩
    change tailoringRadialFunction I β y.1 = 1 at hf
    rcases hy.2 with ⟨σ, hσ, hσ₀, hp, hθ⟩
    have hh := (tailoringRadialFunction_height_bounds I β hf).1
    have he := hβ σ hσ y hp hθ (by linarith)
    refine ⟨hy, ?_⟩
    rw [tailoringFamily_one_fiber]
    change tailoringEquation I β y = 0
    rw [he, hf]
    simp

theorem IsStronglyCompatibleEndPotential.eventually_coreSection_compact
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, IsCompact (tailoringCoreSection I φ β) := by
  filter_upwards [hφ.eventually_coreSection_eq_radial,
    eventually_ge_atTop (Real.log (I.vertices.card : ℝ) + 1)] with β hβ hlarge
  rw [hβ]
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  let K : Set (LGSpace n) := {u | tailoringRadialFunction I β u = 1} ×ˢ univ
  have hK : IsCompact K := (tailoringRadialFunction_compact_level I β).prod isCompact_univ
  let U : Set (LGSpace n) := ⋃ σ ∈ faceFan I,
    {y | σ ≠ {0} ∧ Φ y.1 ∈ σ ∧ y.2 ∈ coneTorus σ}
  have hU : IsClosed U := I.finite_faceFan.isClosed_biUnion (fun σ hσ => by
    by_cases hσ₀ : σ = {0}
    · simp only [hσ₀, ne_eq, not_true_eq_false, false_and, ofPred_false]
      exact isClosed_empty
    · simpa only [hσ₀, ne_eq, not_false_eq_true, true_and, preimage, inter_def,
        Function.comp_apply, mem_ofPred_eq] using
        ((I.isClosed_of_mem_faceFan hσ).preimage (Φ.continuous.comp continuous_fst)).inter
          ((isClosed_coneTorus σ).preimage continuous_snd))
  have he : tailoringLegendreConic I φ ∩ {y | tailoringRadialFunction I β y.1 = 1} =
      K ∩ U := by
    ext y
    constructor
    · rintro ⟨⟨hne, σ, hσ, hσ₀, hp, hθ⟩, hf⟩
      refine ⟨⟨hf, mem_univ _⟩, ?_⟩
      simp only [U, mem_iUnion, mem_ofPred_eq]
      exact ⟨σ, hσ, hσ₀, (hΦ y.1).symm ▸ hp, hθ⟩
    · rintro ⟨⟨hf, _⟩, hy⟩
      simp only [U, mem_iUnion, mem_ofPred_eq] at hy
      rcases hy with ⟨σ, hσ, hσ₀, hp, hθ⟩
      have hu : y.1 ≠ 0 := by
        have hh := (tailoringRadialFunction_height_bounds I β hf).1
        intro hz
        rw [hz, I.supportHeight_zero] at hh
        linarith
      have hne : coordinateGradient φ y.1 ≠ 0 := by
        rw [← hΦ, ← hΦ₀]
        exact fun h => hu (Φ.injective h)
      exact ⟨⟨hne, σ, hσ, hσ₀, hΦ y.1 ▸ hp, hθ⟩, hf⟩
  rw [he]
  exact hK.inter_right hU

private theorem radius_pos_of_ne_zero {u : RealSpace n} (hu : u ≠ 0) :
    0 < Real.sqrt (realSquaredNorm u) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  rw [← e.apply_symm_apply u, realSquaredNorm_euclidean, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr (by simpa [e] using hu)

/-- The literal Euclidean radial projection of the native Legendre image. -/
def tailoringRadialProjection (φ : RealSpace n → ℝ) (y : LGSpace n) : Cotangent n :=
  (y.2, (Real.sqrt (realSquaredNorm (coordinateGradient φ y.1)))⁻¹ •
    coordinateGradient φ y.1)

theorem tailoringRadialProjection_mem_link {I : ToricInput n} {φ : RealSpace n → ℝ}
    {y : LGSpace n} (hy : y ∈ tailoringLegendreConic I φ) :
    tailoringRadialProjection φ y ∈ fltzLink I := by
  rcases hy with ⟨hne, σ, hσ, hσ₀, hp, hθ⟩
  let r := Real.sqrt (realSquaredNorm (coordinateGradient φ y.1))
  have hr : 0 < r := radius_pos_of_ne_zero hne
  have hrsq : r ^ 2 = realSquaredNorm (coordinateGradient φ y.1) :=
    Real.sq_sqrt (realSquaredNorm_nonneg _)
  refine ⟨?_, σ, hσ, hσ₀, hθ, I.smul_mem_of_mem_faceFan hσ hp (inv_pos.mpr hr).le⟩
  change realSquaredNorm (r⁻¹ • coordinateGradient φ y.1) = 1
  rw [realSquaredNorm_smul, ← hrsq]
  field_simp

theorem tailoringRadialFunction_eventually_same_ray_unique (I : ToricInput n) :
    ∀ᶠ β in atTop, ∀ u v : RealSpace n,
      tailoringRadialFunction I β u = 1 → tailoringRadialFunction I β v = 1 →
      ∀ s : ℝ, 0 < s → u = s • v → u = v := by
  filter_upwards [tailoringRadialFunction_eventually_unique_ray I,
    eventually_ge_atTop (Real.log (I.vertices.card : ℝ) + 1)] with β hβ hlarge
  intro u v hu hv s hs huv
  let h := supportHeight I v
  have hh : 0 < h := by
    have := (tailoringRadialFunction_height_bounds I β hv).1
    dsimp [h]
    linarith
  let w := h⁻¹ • v
  have hw : supportHeight I w = 1 := by
    rw [I.supportHeight_smul_of_nonneg (inv_pos.mpr hh).le]
    exact inv_mul_cancel₀ hh.ne'
  obtain ⟨t, ht, huniq⟩ := hβ w hw
  have hvw : h • w = v := by simp [w, smul_smul, hh.ne']
  have huw : (s * h) • w = u := by rw [mul_smul, hvw, ← huv]
  have h₁ := huniq h ⟨hh, by rwa [hvw]⟩
  have h₂ := huniq (s * h) ⟨mul_pos hs hh, by rwa [huw]⟩
  rw [← huw, ← hvw, h₂.trans h₁.symm]

/-- Every point of the entire literal FLTZ link has a section representative. -/
theorem IsStronglyCompatibleEndPotential.eventually_coreSection_projection_surjOn
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, SurjOn (tailoringRadialProjection φ) (tailoringCoreSection I φ β)
      (fltzLink I) := by
  filter_upwards [hφ.eventually_coreSection_eq_radial,
    tailoringRadialFunction_eventually_unique_ray I] with β hβ hroot
  intro z hz
  rcases hz with ⟨hzunit, σ, hσ, hσ₀, hθ, hp⟩
  have hpunit : realSquaredNorm z.2 = 1 := hzunit
  have hpne : z.2 ≠ 0 := by
    intro h
    simp [h, realSquaredNorm] at hpunit
  let x := Φ.symm z.2
  have hx : coordinateGradient φ x = z.2 := by rw [← hΦ]; exact Φ.apply_symm_apply _
  have hxne : x ≠ 0 := by
    intro h
    have he : z.2 = 0 := by rw [← hx, ← hΦ, h, hΦ₀]
    exact hpne he
  obtain ⟨c, hc, H, hH, hh⟩ := I.exists_supportHeight_linear_bounds
  let h := supportHeight I x
  have hhpos : 0 < h := lt_of_lt_of_le (mul_pos hc (radius_pos_of_ne_zero hxne)) (hh x).1
  let u := h⁻¹ • x
  have hu : supportHeight I u = 1 := by
    rw [I.supportHeight_smul_of_nonneg (inv_pos.mpr hhpos).le]
    exact inv_mul_cancel₀ hhpos.ne'
  obtain ⟨t, ht, _⟩ := hroot u hu
  let s := t * h⁻¹
  have hs : 0 < s := mul_pos ht.1 (inv_pos.mpr hhpos)
  have hpoint : t • u = s • x := by simp only [u, s, smul_smul]
  have hgrad : coordinateGradient φ (t • u) = s • z.2 := by
    rw [hpoint, coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun v hv => (hφ.smooth v hv).differentiableAt (by simp)) hxne hs, hx]
  let y : LGSpace n := (t • u, z.1)
  have hycone : y ∈ tailoringLegendreConic I φ := by
    refine ⟨?_, σ, hσ, hσ₀, ?_, hθ⟩
    · rw [hgrad]
      exact smul_ne_zero hs.ne' hpne
    · rw [hgrad]
      exact I.smul_mem_of_mem_faceFan hσ hp hs.le
  refine ⟨y, ?_, ?_⟩
  · rw [hβ]
    exact ⟨hycone, ht.2⟩
  · apply Prod.ext
    · rfl
    · change (Real.sqrt (realSquaredNorm (coordinateGradient φ (t • u))))⁻¹ •
        coordinateGradient φ (t • u) = z.2
      rw [hgrad, realSquaredNorm_smul, hpunit, mul_one, Real.sqrt_sq hs.le,
        smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem IsStronglyCompatibleEndPotential.eventually_coreSection_projection_bijOn
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, BijOn (tailoringRadialProjection φ) (tailoringCoreSection I φ β)
      (fltzLink I) := by
  filter_upwards [hφ.eventually_coreSection_eq_radial,
    tailoringRadialFunction_eventually_same_ray_unique I,
    hφ.eventually_coreSection_projection_surjOn Φ hΦ hΦ₀] with β hβ huniq hsurj
  refine ⟨fun y hy => tailoringRadialProjection_mem_link hy.1, ?_, hsurj⟩
  intro x hx y hy heq
  have hxne := hx.1.1
  have hyne := hy.1.1
  let a := Real.sqrt (realSquaredNorm (coordinateGradient φ x.1))
  let b := Real.sqrt (realSquaredNorm (coordinateGradient φ y.1))
  have ha : 0 < a := radius_pos_of_ne_zero hxne
  have hb : 0 < b := radius_pos_of_ne_zero hyne
  have hgrad : coordinateGradient φ x.1 = (a * b⁻¹) • coordinateGradient φ y.1 := by
    have h := congrArg (fun z : Cotangent n => a • z.2) heq
    change a • (a⁻¹ • coordinateGradient φ x.1) =
      a • (b⁻¹ • coordinateGradient φ y.1) at h
    simpa only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul] using h
  have hs : 0 < a * b⁻¹ := mul_pos ha (inv_pos.mpr hb)
  have hys : y.1 ≠ 0 := by
    intro h
    apply hyne
    rw [← hΦ, h, hΦ₀]
  have hrad : x.1 = (a * b⁻¹) • y.1 := by
    apply Φ.injective
    rw [hΦ, hΦ, coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun v hv => (hφ.smooth v hv).differentiableAt (by simp)) hys hs]
    exact hgrad
  rw [hβ] at hx hy
  exact Prod.ext (huniq x.1 y.1 hx.2 hy.2 _ hs hrad)
    (congrArg Prod.fst heq)

/-- Literal equality of embedded subsets in the fixed cotangent boundary. -/
theorem IsStronglyCompatibleEndPotential.eventually_coreSection_projection_image
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, tailoringRadialProjection φ '' tailoringCoreSection I φ β = fltzLink I := by
  filter_upwards [hφ.eventually_coreSection_projection_bijOn Φ hΦ hΦ₀] with β hβ
  exact hβ.image_eq

theorem tailoringEta_eq_one_of_radial_height (I : ToricInput n) (β : ℝ)
    (y : LGSpace n)
    (hh : β - Real.log (2 * (I.vertices.card : ℝ)) ≤ supportHeight I y.1) :
    tailoringEta I β y = 1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  apply (tailoringEta_eq_one_iff I β y).mpr
  obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
  have hmax : Real.exp (supportHeight I y.1 - β) ≤ tailoringMonomialSize I β y := by
    have hb := norm_monomial_le_tailoringMonomialSize I β v.property y
    rw [norm_tailoring_monomial I β v y, tailoringWeight_vertex I β v, hv] at hb
    exact hb
  have he : 1 / (2 * (I.vertices.card : ℝ)) ≤ Real.exp (supportHeight I y.1 - β) := by
    rw [← Real.exp_log (by positivity : 0 < 1 / (2 * (I.vertices.card : ℝ))),
      Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs : 2 * tailoringSmallConstant I ≤ 1 / (2 * (I.vertices.card : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (I.vertices.card : ℝ))).mpr
    nlinarith [tailoringSmallConstant_size I]
  exact hs.trans (he.trans hmax)

/-- On the whole outward conic region the actual endpoint is the real
radial function, including the prescribed small-monomial cutoff. -/
theorem IsStronglyCompatibleEndPotential.eventually_cone_family_eq_radial
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ y : LGSpace n,
      coordinateGradient φ y.1 ∈ σ → y.2 ∈ coneTorus σ →
      β - Real.log (2 * (I.vertices.card : ℝ)) ≤ supportHeight I y.1 →
      tailoringFamily I β 1 y = (tailoringRadialFunction I β y.1 : ℝ) := by
  filter_upwards [hφ.eventually_cone_equation] with β hβ
  intro σ hσ y hp hθ hh
  have he := tailoringFamily_one_sub_one_of_eta_eq_one I β y
    (tailoringEta_eq_one_of_radial_height I β y hh)
  rw [hβ σ hσ y hp hθ hh, Complex.ofReal_sub, Complex.ofReal_one] at he
  linear_combination he

/-- A scalar-ray derivative of the actual endpoint, with positive real
value, on every outward continuation of the section. -/
theorem IsStronglyCompatibleEndPotential.eventually_cone_ray_derivative_positive
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ y : LGSpace n, y.1 ≠ 0 →
      coordinateGradient φ y.1 ∈ σ → y.2 ∈ coneTorus σ →
      β - Real.log (2 * (I.vertices.card : ℝ)) < supportHeight I y.1 →
      ∃ d : ℝ, 0 < d ∧ 0 < (tailoringFamily I β 1 y).re ∧
        HasDerivAt (fun t : ℝ => tailoringFamily I β 1 (t • y.1, y.2)) (d : ℂ) 1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  filter_upwards [hφ.eventually_cone_family_eq_radial,
    tailoringRadialFunction_eventually_radial_positive I hL,
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop L)] with β hβ hpos hsqrt
  intro σ hσ y hy hp hθ hh
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, 0 < t ∧ β - L < supportHeight I (t • y.1) := by
    have hc : Continuous (fun t : ℝ => supportHeight I (t • y.1)) :=
      I.supportHeight_continuous.comp (continuous_id.smul continuous_const)
    have h := (hc.tendsto 1).eventually (lt_mem_nhds (by simpa only [one_smul] using hh))
    filter_upwards [h, lt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht htpos
    exact ⟨htpos, ht⟩
  have he : (fun t : ℝ => tailoringFamily I β 1 (t • y.1, y.2)) =ᶠ[𝓝 1]
      (fun t : ℝ => (tailoringRadialFunction I β (t • y.1) : ℂ)) := by
    filter_upwards [hnear] with t ht
    apply hβ σ hσ (t • y.1, y.2) _ hθ ht.2.le
    rw [coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun v hv => (hφ.smooth v hv).differentiableAt (by simp)) hy ht.1]
    exact I.smul_mem_of_mem_faceFan hσ hp ht.1.le
  let d := fderiv ℝ (tailoringRadialFunction I β) y.1 y.1
  have hd : 0 < d := hpos y.1 hh.le
  refine ⟨d, hd, ?_, ?_⟩
  · rw [hβ σ hσ y hp hθ hh.le, Complex.ofReal_re]
    exact lt_of_lt_of_le (Real.exp_pos _) (tailoringRadialFunction_max_term_lower I β y.1
      (by dsimp [L] at hsqrt; linarith))
  · have hf := hasDerivAt_tailoringRadialFunction_ray I β y.1 1
    simp only [one_smul] at hf
    have hg := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 hf
    exact hg.congr_of_eventuallyEq he

/-- A compact bijective radial section is produced from the original finite
input and the proved compatible-potential construction. -/
theorem ToricInput.exists_compact_tailoring_radialSection (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ∃ Φ : RealSpace n ≃ₜ RealSpace n, (∀ u, Φ u = coordinateGradient φ u) ∧
        Φ 0 = 0 ∧ ∀ᶠ β in atTop,
          IsCompact (tailoringCoreSection I φ β) ∧
          BijOn (tailoringRadialProjection φ) (tailoringCoreSection I φ β) (fltzLink I) := by
  obtain ⟨φEnd, φ, hstrong, hφ1, hφ0, hφs, hpos, hnear, hagree,
    ΦEnd, Φ, hΦEnd, hΦEnd₀, hΦEnds, hΦEndInv, hΦ, hΦs, hΦInv⟩ :=
    I.exists_compatiblePotential_with_legendre
  refine ⟨φEnd, hstrong, ΦEnd, hΦEnd, hΦEnd₀, ?_⟩
  filter_upwards [hstrong.eventually_coreSection_compact ΦEnd hΦEnd hΦEnd₀,
    hstrong.eventually_coreSection_projection_bijOn ΦEnd hΦEnd hΦEnd₀] with β hc hb
  exact ⟨hc, hb⟩

end FsFltz
