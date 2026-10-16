import FsFltz.Analysis.TailoringBadGeometry
import FsFltz.Analysis.TailoringLimitFace
import FsFltz.Analysis.TailoringSmallConormalRadial

/-!
# The conormal equation in normalized limits

Source: `geometric-part-fsf-proof.tex`, `lem:bad`, lines 1401–1426.
These lemmas take literal convergent subsequences of the actual coefficients,
not a limiting conormal equation supplied as a geometric hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology BigOperators

variable {n : ℕ}

/-- Homogeneity converts convergence of normalized positions into convergence
of the normalized actual gradients. -/
theorem coordinateGradient_normalized_tendsto
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (β : ℕ → ℝ) (u : ℕ → RealSpace n) (hβ : Tendsto β atTop atTop)
    (x : RealSpace n) (hx₀ : x ≠ 0)
    (hx : Tendsto (fun j => (β j)⁻¹ • u j) atTop (𝓝 x)) :
    Tendsto (fun j => (β j)⁻¹ • coordinateGradient φ (u j))
      atTop (𝓝 (coordinateGradient φ x)) := by
  have hg := (continuousAt_coordinateGradient (hφ.smooth x hx₀)).tendsto.comp hx
  apply hg.congr'
  filter_upwards [hβ.eventually (eventually_gt_atTop 0), hx.eventually_ne hx₀] with j hj hju
  exact coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
    (fun u hu => (hφ.smooth u hu).differentiableAt (by simp))
    (fun he => hju (by simp [he])) (inv_pos.mpr hj)

/-- A vanishing relative error in the actual retained-normal equation
produces the literal limiting complex conormal equation. -/
theorem tailoring_conormal_equation_of_normalized_limits
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (x : RealSpace n) (hx₀ : x ≠ 0)
    (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (q : Lattice n → ℂ)
    (hq : ∀ v ∈ I.vertices, Tendsto (fun j => tailoringRetainedMonomial I (β j) v (y j))
      atTop (𝓝 (q v)))
    (t : ℕ → ℂ) (τ : ℂ)
    (ht : Tendsto (fun j => ((β j)⁻¹ : ℂ) * t j) atTop (𝓝 τ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ᶠ j in atTop,
      ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤
          δ j * ‖coordinateGradient φ (y j).1‖) :
    (fun k => (coordinateGradient φ x k : ℂ)) =
      τ • ∑ v ∈ I.vertices, q v • latticeComplex v := by
  let p : ℕ → RealSpace n := fun j => (β j)⁻¹ • coordinateGradient φ (y j).1
  have hp : Tendsto p atTop (𝓝 (coordinateGradient φ x)) :=
    coordinateGradient_normalized_tendsto hφ β (fun j => (y j).1) hβ x hx₀ hx
  have hpℂ : Tendsto (fun j => fun k => (p j k : ℂ)) atTop
      (𝓝 (fun k => (coordinateGradient φ x k : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_pi_nhds.mp hp) k)
  have hG : Tendsto (fun j => tailoringRetainedNormal I (β j) (y j)) atTop
      (𝓝 (∑ v ∈ I.vertices, q v • latticeComplex v)) := by
    exact tendsto_finsetSum I.vertices (fun v hv => (hq v hv).smul_const _)
  let e : ℕ → Fin n → ℂ := fun j => (fun k => (p j k : ℂ)) -
    (((β j)⁻¹ : ℂ) * t j) • tailoringRetainedNormal I (β j) (y j)
  have heNorm : Tendsto (fun j => ‖e j‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using hδ.mul hp.norm)
    filter_upwards [herr, hβ.eventually (eventually_gt_atTop 0)] with j hj hjβ
    have he : e j = ((β j)⁻¹ : ℂ) •
        ((fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
          t j • tailoringRetainedNormal I (β j) (y j)) := by
      ext k
      simp [e, p, mul_sub, mul_assoc]
    rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hjβ.le]
    have hb := mul_le_mul_of_nonneg_left hj (inv_pos.mpr hjβ).le
    simpa [p, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hjβ).le, mul_assoc,
      mul_left_comm] using hb
  have he : Tendsto e atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr heNorm
  have he' : Tendsto e atTop
      (𝓝 ((fun k => (coordinateGradient φ x k : ℂ)) -
        τ • ∑ v ∈ I.vertices, q v • latticeComplex v)) := hpℂ.sub (ht.smul hG)
  exact sub_eq_zero.mp (tendsto_nhds_unique he' he)

/-- A fixed actual transition exponent rules out convergent approximate
critical conormals with errors tending to zero. -/
theorem not_tailoring_transition_conormal_limit
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (a : Lattice n) (ha : a ∈ I.vertices)
    (htransition : ∀ᶠ j in atTop,
      0 < tailoringCutoff I (β j) a (y j).1 ∧ tailoringCutoff I (β j) a (y j).1 < 1)
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
  have hax := pairing_limit_eq_one_of_tailoring_transition I a ha β
    (fun j => (y j).1) hβ B hB htransition x hx
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
    (tailoringRetainedMonomial_tendsto_zero_of_transition I a ha β y hβ B hB
      (htransition.mono fun _ h => h.2))
  exact hqane hqazero

end FsFltz
