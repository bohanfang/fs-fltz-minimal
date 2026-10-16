import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The normalized reduced critical-point implicit equation

Source: `geometric-part-fsf-proof.tex`, `eq:criticalIFT` and
`prop:morsebott`, lines 1518–1527. This constructs the local branch from
a smooth reduced coefficient map. Constructing that map from the actual
affine constrained minima is a separate producer, not assumed in the
finite toric input or the target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology BigOperators ContDiff

variable {ι : Type*} [Fintype ι]

/-- The sum constraint as a continuous linear functional. -/
def criticalCoordinateSum : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

@[simp]
theorem criticalCoordinateSum_apply (q : ι → ℝ) :
    criticalCoordinateSum q = ∑ i, q i := by
  simp [criticalCoordinateSum]

/-- The derivative in the normalized unknowns at parameter zero. -/
def criticalReducedLinearization (μ : ℝ) (q : ι → ℝ) :
    ((ι → ℝ) × ℝ) →L[ℝ] ((ι → ℝ) × ℝ) :=
  ((-μ) • ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ -
    (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).smulRight q).prod
      (criticalCoordinateSum.comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ))

@[simp]
theorem criticalReducedLinearization_apply (μ : ℝ) (q : ι → ℝ)
    (p : (ι → ℝ) × ℝ) :
    criticalReducedLinearization μ q p = (-μ • p.1 - p.2 • q, ∑ i, p.1 i) := by
  simp [criticalReducedLinearization]

/-- The explicit inverse of the base derivative, using the sum-one condition. -/
def criticalReducedLinearizationInverse (μ : ℝ) (q : ι → ℝ) :
    ((ι → ℝ) × ℝ) →L[ℝ] ((ι → ℝ) × ℝ) :=
  let t := criticalCoordinateSum.comp (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ) +
    μ • ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ
  (μ⁻¹ • (t.smulRight q - ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)).prod (-t)

@[simp]
theorem criticalReducedLinearizationInverse_apply (μ : ℝ) (q : ι → ℝ)
    (p : (ι → ℝ) × ℝ) :
    criticalReducedLinearizationInverse μ q p =
      (μ⁻¹ • ((∑ i, p.1 i + μ * p.2) • q - p.1), -(∑ i, p.1 i + μ * p.2)) := by
  simp [criticalReducedLinearizationInverse]

/-- The source's square normalization derivative is actually invertible;
the proof constructs its inverse rather than using a dimension count. -/
theorem criticalReducedLinearization_isInvertible {μ : ℝ} (hμ : μ ≠ 0)
    {q : ι → ℝ} (hq : ∑ i, q i = 1) :
    (criticalReducedLinearization μ q).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := criticalReducedLinearizationInverse μ q)
  · apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · ext i
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        criticalReducedLinearization_apply, criticalReducedLinearizationInverse_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hμ]
      ring
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        criticalReducedLinearization_apply, criticalReducedLinearizationInverse_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hq, mul_one]
      field_simp [hμ]
      ring
  · apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · ext i
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        criticalReducedLinearization_apply, criticalReducedLinearizationInverse_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hq, mul_one]
      field_simp [hμ]
      ring
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        criticalReducedLinearization_apply, criticalReducedLinearizationInverse_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hq, mul_one]
      ring

/-- The literal reduced equation from the critical-torus proof. The second
component imposes normalization and no unknown is supplied as input. -/
def criticalReducedEquation (a : (ι → ℝ) → (ι → ℝ))
    (p : ℝ × ((ι → ℝ) × ℝ)) : (ι → ℝ) × ℝ :=
  (a (p.1 • (fun i => Real.log (p.2.1 i))) - p.2.2 • p.2.1,
    (∑ i, p.2.1 i) - 1)

/-- Smoothness of the literal reduced equation at every positive weight
vector over parameter zero follows from smoothness of its coefficient map. -/
theorem contDiffAt_criticalReducedEquation
    {a : (ι → ℝ) → (ι → ℝ)} (ha : ContDiffAt ℝ ∞ a 0)
    {q : ι → ℝ} (hq : ∀ i, 0 < q i) (μ : ℝ) :
    ContDiffAt ℝ ∞ (criticalReducedEquation a) (0, (q, μ)) := by
  have hlog : ContDiffAt ℝ ∞
      (fun p : ℝ × ((ι → ℝ) × ℝ) => fun i => Real.log (p.2.1 i)) (0, (q, μ)) := by
    apply contDiffAt_pi.mpr
    intro i
    exact (by fun_prop : ContDiffAt ℝ ∞
      (fun p : ℝ × ((ι → ℝ) × ℝ) => p.2.1 i) (0, (q, μ))).log (hq i).ne'
  have harg : ContDiffAt ℝ ∞
      (fun p : ℝ × ((ι → ℝ) × ℝ) => p.1 • (fun i => Real.log (p.2.1 i)))
      (0, (q, μ)) := contDiffAt_fst.smul hlog
  have hac : ContDiffAt ℝ ∞
      (fun p : ℝ × ((ι → ℝ) × ℝ) => a (p.1 • (fun i => Real.log (p.2.1 i))))
      (0, (q, μ)) := by
    apply ContDiffAt.comp (0, (q, μ)) _ harg
    simpa using ha
  unfold criticalReducedEquation
  exact (hac.sub (by fun_prop)).prodMk (by fun_prop)

/-- The unknown-variable derivative is the explicit normalization map.
The coefficient map contributes zero at parameter zero, exactly as in
the source's critical equations. -/
theorem fderiv_criticalReducedEquation_unknowns
    {a : (ι → ℝ) → (ι → ℝ)} (ha : ContDiffAt ℝ ∞ a 0)
    {q : ι → ℝ} (hq : ∀ i, 0 < q i) (μ : ℝ) :
    (fderiv ℝ (criticalReducedEquation a) (0, (q, μ))).comp
      (ContinuousLinearMap.inr ℝ ℝ ((ι → ℝ) × ℝ)) =
        criticalReducedLinearization μ q := by
  have htotal := (contDiffAt_criticalReducedEquation ha hq μ).differentiableAt (by simp)
  have hin : HasFDerivAt (fun p : (ι → ℝ) × ℝ => ((0 : ℝ), p))
      (ContinuousLinearMap.inr ℝ ℝ ((ι → ℝ) × ℝ)) (q, μ) := by
    exact (ContinuousLinearMap.inr ℝ ℝ ((ι → ℝ) × ℝ)).hasFDerivAt
  have hchain := htotal.hasFDerivAt.comp (q, μ) hin
  have hfirst := (hasFDerivAt_const (a 0) (q, μ)).fun_sub
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := (q, μ))).fun_smul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (q, μ))))
  have hsecond := HasFDerivAt.sub_const 1 ((criticalCoordinateSum.comp
    (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ)).hasFDerivAt (x := (q, μ)))
  have hmodel := hfirst.prodMk hsecond
  simp only [ContinuousLinearMap.comp_apply, criticalCoordinateSum_apply] at hmodel
  change HasFDerivAt (fun p : (ι → ℝ) × ℝ => criticalReducedEquation a (0, p)) _ _ at hchain
  simp only [criticalReducedEquation, zero_smul] at hchain
  have he := hchain.unique hmodel
  rw [he]
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext
  · ext i
    simp [criticalReducedLinearization]
    ring
  · rfl

/-- The reduced equation has a locally unique smooth positive branch.
Smoothness of `a` is an explicit analytical hypothesis; no existence of
an actual critical torus or any target conclusion is assumed. -/
theorem exists_positive_criticalReduced_branch
    {a : (ι → ℝ) → (ι → ℝ)} (ha : ContDiffAt ℝ ∞ a 0)
    {q₀ : ι → ℝ} {μ₀ : ℝ} (hq₀ : ∀ i, 0 < q₀ i) (hμ₀ : 0 < μ₀)
    (hsum : ∑ i, q₀ i = 1) (hbase : a 0 = μ₀ • q₀) :
    ∃ z : ℝ → ((ι → ℝ) × ℝ), z 0 = (q₀, μ₀) ∧ ContDiffAt ℝ ∞ z 0 ∧
      (∀ᶠ ε : ℝ in 𝓝 0,
        (∀ i, 0 < (z ε).1 i) ∧ 0 < (z ε).2 ∧
        a (ε • (fun i => Real.log ((z ε).1 i))) = (z ε).2 • (z ε).1 ∧
        (∑ i, (z ε).1 i) = 1) ∧
      ∀ᶠ p : ℝ × ((ι → ℝ) × ℝ) in 𝓝 (0, (q₀, μ₀)),
        criticalReducedEquation a p = 0 ↔ z p.1 = p.2 := by
  have hs := contDiffAt_criticalReducedEquation ha hq₀ μ₀
  have hinv : ((fderiv ℝ (criticalReducedEquation a) (0, (q₀, μ₀))).comp
      (ContinuousLinearMap.inr ℝ ℝ ((ι → ℝ) × ℝ))).IsInvertible := by
    rw [fderiv_criticalReducedEquation_unknowns ha hq₀ μ₀]
    exact criticalReducedLinearization_isInvertible hμ₀.ne' hsum
  let z := hs.implicitFunction (by simp) hinv
  have hz : z 0 = (q₀, μ₀) := hs.implicitFunction_apply_self (by simp) hinv
  have hzs : ContDiffAt ℝ ∞ z 0 := hs.contDiffAt_implicitFunction (by simp) hinv
  have heq : criticalReducedEquation a (0, (q₀, μ₀)) = 0 := by
    simp [criticalReducedEquation, hbase, hsum]
  have hsolution : ∀ᶠ ε : ℝ in 𝓝 0, criticalReducedEquation a (ε, z ε) = 0 := by
    simpa only [heq] using hs.eventually_apply_implicitFunction (by simp) hinv
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, 0 < (z ε).1 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun ε : ℝ => (z ε).1 i) 0 := by
      have := hzs.continuousAt
      fun_prop
    exact hc.eventually (eventually_gt_nhds (by simpa only [hz] using hq₀ i))
  have hμpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (z ε).2 := by
    have hc : ContinuousAt (fun ε : ℝ => (z ε).2) 0 := hzs.continuousAt.snd
    exact hc.eventually (eventually_gt_nhds (by simpa only [hz] using hμ₀))
  refine ⟨z, hz, hzs, ?_, ?_⟩
  · filter_upwards [hsolution, hpos, hμpos] with ε hε hq hμ
    exact ⟨hq, hμ, sub_eq_zero.mp (congrArg Prod.fst hε),
      sub_eq_zero.mp (congrArg Prod.snd hε)⟩
  · simpa only [heq] using hs.eventually_apply_eq_iff_implicitFunction (by simp) hinv

/-- The base solution is constructed from the positive face coefficients:
`μ₀ = ∑ aᵢ(0)` and `q₀ᵢ = aᵢ(0) / μ₀`, with no chosen solution premise. -/
theorem exists_normalized_positive_criticalReduced_branch [Nonempty ι]
    {a : (ι → ℝ) → (ι → ℝ)} (ha : ContDiffAt ℝ ∞ a 0)
    (hpositive : ∀ i, 0 < a 0 i) :
    ∃ z : ℝ → ((ι → ℝ) × ℝ),
      z 0 = ((fun i => a 0 i / (∑ j, a 0 j)), ∑ j, a 0 j) ∧
      ContDiffAt ℝ ∞ z 0 ∧
      (∀ᶠ ε : ℝ in 𝓝 0,
        (∀ i, 0 < (z ε).1 i) ∧ 0 < (z ε).2 ∧
        a (ε • (fun i => Real.log ((z ε).1 i))) = (z ε).2 • (z ε).1 ∧
        (∑ i, (z ε).1 i) = 1) ∧
      ∀ᶠ p : ℝ × ((ι → ℝ) × ℝ) in
          𝓝 (0, ((fun i => a 0 i / (∑ j, a 0 j)), ∑ j, a 0 j)),
        criticalReducedEquation a p = 0 ↔ z p.1 = p.2 := by
  classical
  have hμ : 0 < ∑ i, a 0 i := Finset.sum_pos (fun i _ => hpositive i) Finset.univ_nonempty
  have hsum : ∑ i, a 0 i / (∑ j, a 0 j) = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hμ.ne']
  have hbase : a 0 = (∑ i, a 0 i) • (fun i => a 0 i / (∑ j, a 0 j)) := by
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hμ.ne']
  exact exists_positive_criticalReduced_branch ha (fun i => div_pos (hpositive i) hμ)
    hμ hsum hbase

end FsFltz
