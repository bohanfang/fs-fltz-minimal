import FsFltz.Geometry.TailoringConormalLiouville
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth radial extensions of actual conormal fiber pieces

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1616–1617,
and `lem:invariance`, lines 1625–1632. Ambient cutoff germs let the
scalar implicit-function construction extend across the full face span.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

/-- An actual smooth radial graph, before restricting to any cone or face. -/
theorem tailoringRadialFunction_exists_smooth_radialGraph
    (I : ToricInput n) (β : ℝ) (u : RealSpace n)
    (hu : tailoringRadialFunction I β u = 1)
    (hd : 0 < fderiv ℝ (tailoringRadialFunction I β) u u) :
    ∃ r : RealSpace n → ℝ, ContDiffAt ℝ ∞ r u ∧ r u = 1 ∧
      ∀ᶠ w in 𝓝 u, 0 < r w ∧ tailoringRadialFunction I β (r w • w) = 1 := by
  let f : RealSpace n × ℝ → ℝ := fun z => tailoringRadialFunction I β (z.2 • z.1)
  have hc : ContDiff ℝ ∞ f :=
    (contDiff_tailoringRadialFunction I β).comp (contDiff_snd.smul contDiff_fst)
  let d := fderiv ℝ (tailoringRadialFunction I β) u u
  have he : fderiv ℝ f (u, 1) ∘L ContinuousLinearMap.inr ℝ (RealSpace n) ℝ =
      d • ContinuousLinearMap.id ℝ ℝ := by
    have hr := (hc.differentiable (by simp) (u, 1)).hasFDerivAt.comp 1
      ((hasFDerivAt_const u (1 : ℝ)).prodMk (hasFDerivAt_id (1 : ℝ)))
    have hr' := (hasDerivAt_tailoringRadialFunction_ray I β u 1).hasFDerivAt
    have hu' : (fun t : ℝ => f (u, t)) = fun t => tailoringRadialFunction I β (t • u) := rfl
    have hder := hr.unique (by simpa only [Function.comp_def, hu', one_smul] using hr')
    convert hder using 1
    · congr 1
    · ext
      simp [d, mul_comm]
  have hi : (fderiv ℝ f (u, 1) ∘L ContinuousLinearMap.inr ℝ (RealSpace n) ℝ).IsInvertible := by
    rw [he]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [smul_smul, ne_of_gt hd, d]
    · ext
      simp [smul_smul, ne_of_gt hd, d]
  let r := hc.contDiffAt.implicitFunction (by simp) hi
  have hr : ContDiffAt ℝ ∞ r u := hc.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hru : r u = 1 := hc.contDiffAt.implicitFunction_apply_self (by simp) hi
  refine ⟨r, hr, hru, ?_⟩
  have hpos : ∀ᶠ w in 𝓝 u, 0 < r w :=
    hr.continuousAt (lt_mem_nhds (by rw [hru]; norm_num))
  filter_upwards [hpos, hc.contDiffAt.eventually_apply_implicitFunction (by simp) hi] with w hw hf
  refine ⟨hw, ?_⟩
  simpa only [f, one_smul, hu] using hf

/-- The actual endpoint equation extends across the ambient neighborhood,
uniformly for every angle in the fixed face torus. -/
theorem IsStronglyCompatibleEndPotential.eventually_conormal_family_germ
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ y : LGSpace n,
      coordinateGradient φ y.1 ∈ σ → y.2 ∈ coneTorus σ →
      tailoringFamily I β 1 y = 1 →
      ∀ᶠ w in 𝓝 y.1, ∀ θ ∈ coneTorus σ,
        tailoringFamily I β 1 (w, θ) = (tailoringRadialFunction I β w : ℝ) := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hlog : Real.log (I.vertices.card : ℝ) < L := Real.log_lt_log hN (by linarith)
  filter_upwards [hφ.eventually_offCone_cutoff_germ L] with β hβ
  intro σ hσ y hp _ hf
  have hh : β - L < supportHeight I y.1 := by
    have := tailoringEndpoint_height_lower I β y hf
    linarith
  have hheight := (I.supportHeight_continuous.tendsto y.1).eventually (lt_mem_nhds hh)
  filter_upwards [hheight, hβ σ hσ y.1 hp hh.le] with w hw hoff
  intro θ hθ
  have he := tailoringFamily_one_sub_one_of_eta_eq_one I β (w, θ)
    (tailoringEta_eq_one_of_radial_height I β (w, θ) hw.le)
  rw [tailoringEquation_eq_radial_of_offCone I β σ (w, θ) hθ hoff,
    Complex.ofReal_sub, Complex.ofReal_one] at he
  linear_combination he

/-- Smooth radial extension of every actual conormal section point.
The graph is defined in an ambient neighborhood, including directions
whose Legendre momenta lie outside the closed cone. -/
theorem IsStronglyCompatibleEndPotential.eventually_conormal_smooth_radialGraph
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ y : LGSpace n,
      coordinateGradient φ y.1 ∈ σ → y.2 ∈ coneTorus σ →
      tailoringFamily I β 1 y = 1 →
      ∃ r : RealSpace n → ℝ, ContDiffAt ℝ ∞ r y.1 ∧ r y.1 = 1 ∧
        ∀ᶠ w in 𝓝 y.1, 0 < r w ∧ ∀ θ ∈ coneTorus σ,
          tailoringFamily I β 1 (r w • w, θ) = 1 := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  have hlog : Real.log (I.vertices.card : ℝ) ≤ L := Real.log_le_log hN (by linarith)
  filter_upwards [hφ.eventually_conormal_family_germ,
    hφ.eventually_cone_family_eq_radial,
    tailoringRadialFunction_eventually_radial_positive I hL] with β hgerm hradial hpositive
  intro σ hσ y hp hθ hf
  have hh : β - L ≤ supportHeight I y.1 := by
    have := tailoringEndpoint_height_lower I β y hf
    linarith
  have hu : tailoringRadialFunction I β y.1 = 1 := by
    have he := hradial σ hσ y hp hθ hh
    rw [hf] at he
    exact_mod_cast he.symm
  obtain ⟨r, hr, hru, hgraph⟩ := tailoringRadialFunction_exists_smooth_radialGraph
    I β y.1 hu (hpositive y.1 hh)
  refine ⟨r, hr, hru, ?_⟩
  have ht : Tendsto (fun w => r w • w) (𝓝 y.1) (𝓝 y.1) := by
    have hc : ContinuousAt (fun w => r w • w) y.1 := hr.continuousAt.smul continuousAt_id
    simpa only [ContinuousAt, hru, one_smul] using hc
  filter_upwards [hgraph, ht.eventually (hgerm σ hσ y hp hθ hf)] with w hw he
  refine ⟨hw.1, fun θ hθ' => ?_⟩
  rw [he θ hθ', hw.2, Complex.ofReal_one]

end FsFltz
