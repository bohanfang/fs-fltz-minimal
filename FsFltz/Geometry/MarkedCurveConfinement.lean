import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-!
# Confinement of horizontal curves in a marked parameter slab

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 985–994.
Open equation preservation and a boundary collar imply that an actual curve
cannot escape a truncated fiber while its affine parameter stays in the
prescribed interval. This is the continuation input for compact horizontal
transport, in both time directions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology Metric

namespace FsFltz.Geometry

/-- A derivative that vanishes on a neighborhood makes the function constant
on a smaller neighborhood of the specified point. -/
theorem eventually_eq_of_eventually_hasFDerivAt_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a : ℝ} (hf : ∀ᶠ t in 𝓝 a, HasFDerivAt (𝕜 := ℝ) f 0 t) :
    ∀ᶠ t in 𝓝 a, f t = f a := by
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hf
  filter_upwards [Metric.ball_mem_nhds a hε] with t ht
  exact (convex_ball a ε).is_const_of_fderivWithin_eq_zero
    (fun z hz => (he hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (he hz).hasFDerivWithinAt.fderivWithin
      (isOpen_ball.uniqueDiffWithinAt hz)) ht (mem_ball_self hε)

/-- A continuous scalar function cannot leave a level on a connected time
set if its derivative vanishes on a neighborhood of each time on that level.
This retains the actual truncation boundary during horizontal transport. -/
theorem eqOn_level_of_eventually_hasDerivAt_zero
    {g : ℝ → ℝ} (hg : Continuous g) (J : Set ℝ) (hJ : IsPreconnected J)
    {t₀ A : ℝ} (ht₀ : t₀ ∈ J) (hstart : g t₀ = A)
    (hd : ∀ t ∈ J, g t = A → ∀ᶠ u in 𝓝 t, HasDerivAt g 0 u) :
    ∀ t ∈ J, g t = A := by
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hJ
  let P : Set J := {t | g t = A}
  have hP : IsClopen P := by
    refine ⟨isClosed_eq (hg.comp continuous_subtype_val) continuous_const,
      isOpen_iff_mem_nhds.mpr ?_⟩
    intro t ht
    have hz : ∀ᶠ u in 𝓝 (t : ℝ), HasFDerivAt (𝕜 := ℝ) g 0 u :=
      (hd t t.property ht).mono (fun u hu => by simpa using hu.hasFDerivAt)
    have he := eventually_eq_of_eventually_hasFDerivAt_zero hz
    have hp : {u : ℝ | g u = A} ∈ 𝓝 (t : ℝ) := he.mono (fun u hu => hu.trans ht)
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hp
  have hall := hP.eq_univ (show P.Nonempty from ⟨⟨t₀, ht₀⟩, hstart⟩)
  intro t ht
  have hmem : (⟨t, ht⟩ : J) ∈ P := by rw [hall]; trivial
  exact hmem

/-- A horizontal curve remains in the full marked truncation throughout
any connected time set on which its affine parameter remains in `[0,1]`.
The derivative conditions hold on neighborhoods; confinement itself is
proved and is not an assumption. Negative time intervals are allowed. -/
theorem marked_curve_stays_in_parameter_slab
    {Q F : Type*} [TopologicalSpace Q]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (γ : ℝ → Q) (hγ : Continuous γ)
    (τ ρ : Q → ℝ) (f : Q → F)
    (hτ : Continuous τ) (hρ : Continuous ρ) (hf : Continuous f)
    (w : F) (A v : ℝ) (O B : Set Q) (hO : IsOpen O) (hB : IsOpen B)
    (hCO : {q | τ q ∈ Icc (0 : ℝ) 1 ∧ f q = w ∧ ρ q ≤ A} ⊆ O)
    (hCB : {q | τ q ∈ Icc (0 : ℝ) 1 ∧ f q = w ∧ ρ q = A} ⊆ B)
    (hτd : ∀ t, γ t ∈ O → HasDerivAt (τ ∘ γ) v t)
    (hfd : ∀ t, γ t ∈ O → HasFDerivAt (𝕜 := ℝ) (f ∘ γ) 0 t)
    (hρd : ∀ t, γ t ∈ O ∩ B → HasDerivAt (ρ ∘ γ) 0 t)
    (J : Set ℝ) (hJ : IsPreconnected J) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (hstart : f (γ t₀) = w ∧ ρ (γ t₀) ≤ A)
    (htime : ∀ t ∈ J, τ (γ t₀) + v * (t - t₀) ∈ Icc (0 : ℝ) 1) :
    ∀ t ∈ J, τ (γ t) = τ (γ t₀) + v * (t - t₀) ∧
      f (γ t) = w ∧ ρ (γ t) ≤ A := by
  let P : Set ℝ := {t | τ (γ t) = τ (γ t₀) + v * (t - t₀) ∧
    f (γ t) = w ∧ ρ (γ t) ≤ A}
  have hPc : IsClosed P :=
    (isClosed_eq (hτ.comp hγ)
      (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const)))).inter
      ((isClosed_eq (hf.comp hγ) continuous_const).inter
        (isClosed_le (hρ.comp hγ) continuous_const))
  have hlocal : ∀ t ∈ J, t ∈ P → P ∈ 𝓝 t := by
    intro t ht hp
    have hct : τ (γ t) ∈ Icc (0 : ℝ) 1 := hp.1 ▸ htime t ht
    have hmem : γ t ∈ O := hCO ⟨hct, hp.2⟩
    have hOn : ∀ᶠ u in 𝓝 t, γ u ∈ O := hγ.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
    have hτzero : ∀ᶠ u in 𝓝 t, HasFDerivAt (𝕜 := ℝ) (fun r => τ (γ r) - v * r) 0 u := by
      filter_upwards [hOn] with u hu
      have hd := (hτd u hu).sub ((hasDerivAt_id u).const_mul v)
      convert hd.hasFDerivAt using 1 <;> simp
      rfl
    have hτeq := eventually_eq_of_eventually_hasFDerivAt_zero hτzero
    have hfeq := eventually_eq_of_eventually_hasFDerivAt_zero (hOn.mono (fun u hu => hfd u hu))
    have hρle : ∀ᶠ u in 𝓝 t, ρ (γ u) ≤ A := by
      rcases hp.2.2.lt_or_eq with hlt | heq
      · exact (hρ.comp hγ).continuousAt.eventually (gt_mem_nhds hlt) |>.mono (fun _ h => le_of_lt h)
      · have hbt : γ t ∈ B := hCB ⟨hct, hp.2.1, heq⟩
        have hBn : ∀ᶠ u in 𝓝 t, γ u ∈ B :=
          hγ.continuousAt.preimage_mem_nhds (hB.mem_nhds hbt)
        have hz : ∀ᶠ u in 𝓝 t, HasFDerivAt (𝕜 := ℝ) (ρ ∘ γ) 0 u := by
          filter_upwards [hOn, hBn] with u hu hb
          simpa using (hρd u ⟨hu, hb⟩).hasFDerivAt
        exact (eventually_eq_of_eventually_hasFDerivAt_zero hz).mono
          (fun u hu => by simpa only [Function.comp_def, heq] using hu.le)
    filter_upwards [hτeq, hfeq, hρle] with u hu hf' hr
    refine ⟨?_, hf'.trans hp.2.1, hr⟩
    have he := hp.1
    nlinarith
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hJ
  have hclopen : IsClopen (Subtype.val ⁻¹' P : Set J) := by
    refine ⟨hPc.preimage continuous_subtype_val, isOpen_iff_mem_nhds.mpr ?_⟩
    intro t ht
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds (hlocal t t.property ht)
  have hall := hclopen.eq_univ (show (Subtype.val ⁻¹' P : Set J).Nonempty from
    ⟨⟨t₀, ht₀⟩, by change t₀ ∈ P; exact ⟨by simp, hstart⟩⟩)
  intro t ht
  have hmem : (⟨t, ht⟩ : J) ∈ (Subtype.val ⁻¹' P : Set J) := by rw [hall]; trivial
  exact hmem

end FsFltz.Geometry
