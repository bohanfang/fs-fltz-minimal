import FsFltz.Analysis.TailoringCoreRadial
import FsFltz.Analysis.TailoringCriticalTangent
import FsFltz.Analysis.TailoringFiberProjection

/-!
# Genuine conormal germs and actual endpoint differential blocks

Sources: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1600–1605,
and `lem:invariance`, lines 1629–1647. These results use the actual cutoffs
and endpoint function, without an invariance or core hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Topology

variable {n : ℕ}

/-- Outside terms vanish on genuine ambient neighborhoods, rather than
only on the cone or at the chosen point. -/
theorem IsStronglyCompatibleEndPotential.eventually_offCone_cutoff_germ
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (L : ℝ) :
    ∀ᶠ β in atTop, ∀ σ ∈ faceFan I, ∀ u : RealSpace n,
      coordinateGradient φ u ∈ σ → β - L ≤ supportHeight I u →
      ∀ᶠ w in 𝓝 u, ∀ v ∈ I.vertices, latticeReal v ∉ σ →
        tailoringCutoff I β v w = 0 := by
  obtain ⟨δ, hδ, hgap⟩ := hφ.uniform_angularExclusionGap
  obtain ⟨c, hc, H, hH, hh⟩ := I.exists_supportHeight_linear_bounds
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 * H / δ)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (δ * L / H + 4))]
    with β hβ hβδ hβL
  intro σ hσ u hgrad hu
  apply (eventually_all_finset I.vertices).mpr
  intro v hv
  by_cases hvs : latticeReal v ∈ σ
  · exact Eventually.of_forall fun _ hout => (hout hvs).elim
  have hstrict : Real.sqrt β + 2 < supportHeight I u - pairing v u := by
    have hsquare := Real.sq_sqrt hβ
    have h₁ : 2 * H ≤ δ * Real.sqrt β := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp hβδ
    have h₂ : δ * L + 4 * H ≤ H * Real.sqrt β := by
      have := mul_le_mul_of_nonneg_left hβL hH.le
      field_simp at this
      nlinarith
    have h₃ := mul_le_mul_of_nonneg_right h₁ (Real.sqrt_nonneg β)
    have h₄ := mul_le_mul_of_nonneg_left hu hδ.le
    have h₅ := mul_le_mul_of_nonneg_left (hh u).2 hδ.le
    have h₆ := mul_le_mul_of_nonneg_left (hgap σ hσ u hgrad v hv hvs) hH.le
    nlinarith
  have hcont : Continuous (fun w => supportHeight I w - pairing v w) :=
    I.supportHeight_continuous.sub (by unfold pairing; fun_prop)
  filter_upwards [(hcont.tendsto u).eventually (lt_mem_nhds hstrict)] with w hw
  exact fun _ => tailoringCutoff_eq_zero_of_large_deficit I β hv w hw.le

/-- The real angular conormal of the literal retained monomials. -/
def tailoringConormalVector (I : ToricInput n) (β : ℝ) (u : RealSpace n) : RealSpace n :=
  ∑ v ∈ I.vertices, (tailoringCutoff I β v u * Real.exp (pairing v u - β)) • latticeReal v

theorem monomial_eq_real_of_coneTorus (β : ℝ) (σ : Set (RealSpace n))
    (y : LGSpace n) (hθ : y.2 ∈ coneTorus σ) (v : Lattice n)
    (hv : latticeReal v ∈ σ) :
    monomial (Real.exp (-β) : ℂ) v y = (Real.exp (pairing v y.1 - β) : ℝ) := by
  have hc : (character v y.2 : ℂ) = 1 := by simp [character, hθ v hv]
  simp only [monomial, hc, mul_one, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

theorem tailoringRetainedNormal_eq_conormalVector (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (y : LGSpace n) (hθ : y.2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v y.1 = 0) :
    tailoringRetainedNormal I β y = fun j => (tailoringConormalVector I β y.1 j : ℂ) := by
  ext j
  simp only [tailoringRetainedNormal, tailoringConormalVector, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvs : latticeReal v ∈ σ
  · simp only [tailoringRetainedMonomial,
      monomial_eq_real_of_coneTorus β σ y hθ v hvs, latticeComplex, latticeReal]
    push_cast
    ring
  · simp [tailoringRetainedMonomial, hoff v hv hvs]

theorem tailoringConormalVector_mem_span (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (u : RealSpace n)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v u = 0) :
    tailoringConormalVector I β u ∈ Submodule.span ℝ σ := by
  apply Submodule.sum_mem
  intro v hv
  by_cases hvs : latticeReal v ∈ σ
  · exact Submodule.smul_mem _ _ (Submodule.subset_span hvs)
  · simp [hoff v hv hvs]

theorem tailoringConormalVector_pairing (I : ToricInput n) (β : ℝ)
    (u w : RealSpace n) :
    ∑ j, tailoringConormalVector I β u j * w j =
      ∑ v ∈ I.vertices, tailoringCutoff I β v u *
        Real.exp (pairing v u - β) * pairing v w := by
  simp only [tailoringConormalVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, pairing, latticeReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fderiv_tailoringRadialFunction_apply (I : ToricInput n) (β : ℝ)
    (u w : RealSpace n) :
    fderiv ℝ (tailoringRadialFunction I β) u w =
      (∑ v ∈ I.vertices, tailoringCutoff I β v u *
        Real.exp (pairing v u - β) * pairing v w) +
      (-(fderiv ℝ (tailoringCutoff I β 0) u w) +
        ∑ v ∈ I.vertices, (fderiv ℝ (tailoringCutoff I β v) u w) *
          Real.exp (pairing v u - β)) := by
  have hd (v : Lattice n) : HasFDerivAt (fun x : RealSpace n =>
      Real.exp (pairing v x - β)) (Real.exp (pairing v u - β) • pairingCLM v) u :=
    (Real.hasDerivAt_exp _).comp_hasFDerivAt u
      (by simpa only [pairingCLM_apply] using (pairingCLM v).hasFDerivAt.sub_const β)
  have he := (((tailoringCutoff_contDiff I β 0).differentiable (by simp) u).hasFDerivAt.const_sub 1).add
    (HasFDerivAt.fun_sum (u := I.vertices) fun v _ =>
      ((tailoringCutoff_contDiff I β v).differentiable (by simp) u).hasFDerivAt.mul (hd v))
  rw [show fderiv ℝ (tailoringRadialFunction I β) u = _ from he.fderiv]
  simp only [add_apply, sum_apply, smul_apply, neg_apply, smul_eq_mul, pairingCLM_apply]
  rw [Finset.sum_add_distrib]
  have h₁ : (∑ v ∈ I.vertices, tailoringCutoff I β v u *
      (Real.exp (pairing v u - β) * pairing v w)) =
      ∑ v ∈ I.vertices, tailoringCutoff I β v u * Real.exp (pairing v u - β) * pairing v w :=
    Finset.sum_congr rfl fun _ _ => by ring
  have h₂ : (∑ v ∈ I.vertices, Real.exp (pairing v u - β) *
      fderiv ℝ (tailoringCutoff I β v) u w) =
      ∑ v ∈ I.vertices, fderiv ℝ (tailoringCutoff I β v) u w * Real.exp (pairing v u - β) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [h₁, h₂]
  ring

private theorem fderiv_cutoff_zero_of_zero (I : ToricInput n) (β : ℝ)
    (v : Lattice n) (u : RealSpace n) (h : tailoringCutoff I β v u = 0) :
    fderiv ℝ (tailoringCutoff I β v) u = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Eventually.of_forall fun w => by
    rw [h]
    exact tailoringCutoff_nonneg I β v w

theorem tailoringRadialError_conormal_apply (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (y : LGSpace n) (hθ : y.2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v y.1 = 0)
    (w : RealSpace n) :
    tailoringRadialError I β y w =
      ((-(fderiv ℝ (tailoringCutoff I β 0) y.1 w) +
        ∑ v ∈ I.vertices, fderiv ℝ (tailoringCutoff I β v) y.1 w *
          Real.exp (pairing v y.1 - β) : ℝ) : ℂ) := by
  simp only [tailoringRadialError, sub_apply, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul]
  have hs : (∑ v ∈ I.vertices, monomial (Real.exp (-β) : ℂ) v y *
      (fderiv ℝ (tailoringCutoff I β v) y.1 w : ℂ)) =
      ∑ v ∈ I.vertices, (fderiv ℝ (tailoringCutoff I β v) y.1 w : ℂ) *
        (Real.exp (pairing v y.1 - β) : ℂ) := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs : latticeReal v ∈ σ
    · rw [monomial_eq_real_of_coneTorus β σ y hθ v hvs, mul_comm]
    · simp [fderiv_cutoff_zero_of_zero I β v y.1 (hoff v hv hvs)]
  rw [hs]
  ring

/-- This is the actual endpoint differential, with all transition-cutoff
terms retained in its real radial block. -/
theorem fderiv_tailoringFamily_one_conormal (I : ToricInput n) (β : ℝ)
    (σ : Set (RealSpace n)) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hθ : (lgCover x).2 ∈ coneTorus σ)
    (hoff : ∀ v ∈ I.vertices, latticeReal v ∉ σ → tailoringCutoff I β v x.1 = 0)
    (w : TangentCoordinates n) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x w =
      (fderiv ℝ (tailoringRadialFunction I β) x.1 w.1 : ℂ) +
        Complex.I * ((∑ j, tailoringConormalVector I β x.1 j * w.2 j : ℝ) : ℂ) := by
  rw [fderiv_tailoringFamily_one_eq_equation_of_fiber I β x hx,
    fderiv_tailoringEquation_cover, add_apply, ContinuousLinearMap.comp_apply]
  change tailoringLeadingDifferential I β (lgCover x) w +
    tailoringRadialError I β (lgCover x) w.1 = _
  rw [tailoringLeadingDifferential_apply_eq_normal,
    tailoringRetainedNormal_eq_conormalVector I β σ (lgCover x) hθ hoff,
    tailoringRadialError_conormal_apply I β σ (lgCover x) hθ hoff,
    fderiv_tailoringRadialFunction_apply]
  simp only [lgCover, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hs : (∑ j, (tailoringConormalVector I β x.1 j : ℂ) * (w.1 j : ℂ)) =
      ((∑ v ∈ I.vertices, tailoringCutoff I β v x.1 *
        Real.exp (pairing v x.1 - β) * pairing v w.1 : ℝ) : ℂ) := by
    norm_cast
    exact tailoringConormalVector_pairing I β x.1 w.1
  rw [hs]
  have hi : (∑ j, (tailoringConormalVector I β x.1 j : ℂ) *
      (Complex.I * (w.2 j : ℂ))) =
      ∑ j, Complex.I * ((tailoringConormalVector I β x.1 j : ℂ) * (w.2 j : ℂ)) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hi]
  push_cast
  ring

end FsFltz
