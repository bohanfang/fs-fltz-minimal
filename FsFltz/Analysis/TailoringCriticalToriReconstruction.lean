import FsFltz.Analysis.TailoringCriticalToriCutoffs

/-!
# Reconstruction of points of the actual tailored fiber

Source: `geometric-part-fsf-proof.tex`, `eq:criticalIFT` and
`prop:morsebott`, lines 1518–1528. The shifted affine equations and
normalization reconstruct actual quotient monomials and points of the
full endpoint fiber. No fiber membership is assumed.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped Topology BigOperators

variable {n : ℕ}

/-- The logarithmic affine constraint reconstructs the literal normalized
Laurent monomial on every angle with trivial face character. -/
theorem monomial_eq_weight_of_shifted_face_level
    {β q : ℝ} (hβ : β ≠ 0) (hq : 0 < q)
    {v : Lattice n} {x : RealSpace n} {θ : Torus n}
    (hlevel : pairing v x = 1 + β⁻¹ * Real.log q)
    (hθ : (character v θ : ℂ) = 1) :
    monomial (Real.exp (-β) : ℂ) v (β • x, θ) = (q : ℂ) := by
  have hp : pairing v (β • x) = β * pairing v x := by
    simpa only [pairingCLM_apply, smul_eq_mul] using (pairingCLM v).map_smul β x
  have he : -β + pairing v (β • x) = Real.log q := by
    rw [hp, hlevel]
    field_simp
    ring
  rw [monomial, hθ, mul_one, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Real.exp_add, he, Real.exp_log hq]

/-- Exact face plateaus and normalized face weights put the reconstructed
point on the literal full tailored fiber, including its small-monomial cutoff. -/
theorem tailoringFamily_eq_one_of_shifted_face_levels
    (I : ToricInput n) {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    {β : ℝ} (hβ : β ≠ 0) {x : RealSpace n} {θ : Torus n}
    (q : s → ℝ) (hq : ∀ v, 0 < q v) (hsum : ∑ v, q v = 1)
    (hlevel : ∀ v : s, pairing v.val x = 1 + β⁻¹ * Real.log (q v))
    (hθ : ∀ v : s, (character v.val θ : ℂ) = 1)
    (hcut : ∀ a ∈ tailoringExponents I,
      tailoringCutoff I β a (β • x) = if a = 0 ∨ a ∈ s then 1 else 0) :
    tailoringFamily I β 1 (β • x, θ) = 1 := by
  classical
  have hzero : tailoringCutoff I β 0 (β • x) = 1 := by
    simpa using hcut 0 (Finset.mem_insert_self _ _)
  have hmon (v : s) : monomial (Real.exp (-β) : ℂ) v.val (β • x, θ) = (q v : ℂ) :=
    monomial_eq_weight_of_shifted_face_level hβ (hq v) (hlevel v) (hθ v)
  have hsum' : (∑ v ∈ I.vertices, (tailoringCutoff I β v (β • x) : ℂ) *
      monomial (Real.exp (-β) : ℂ) v (β • x, θ)) = 1 := by
    calc
      _ = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v (β • x, θ) := by
        rw [← Finset.sum_subset hsub]
        · apply Finset.sum_congr rfl
          intro v hv
          rw [hcut v (Finset.mem_insert_of_mem (hsub hv))]
          simp [hv]
        · intro v hv hvs
          have hv0 : v ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ hv)
          rw [hcut v (Finset.mem_insert_of_mem hv)]
          simp [hv0, hvs]
      _ = ∑ v : s, (q v : ℂ) := by
        rw [← Finset.sum_attach]
        exact Finset.sum_congr rfl (fun v _ => hmon v)
      _ = 1 := by exact_mod_cast hsum
  have heq : tailoringEquation I β (β • x, θ) = 0 := by
    simp only [tailoringEquation, hzero, Complex.ofReal_one, hsum', neg_add_cancel]
  exact (Set.ext_iff.mp (tailoringFamily_one_fiber I β) _).mpr heq

/-- The positive normalized branch and actual shifted-level equations
construct points of the whole endpoint fiber at all face-torus angles. -/
theorem critical_reduced_branch_eventually_mem_fullFiber
    (I : ToricInput n) {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    {x : (s → ℝ) → RealSpace n} (hx : DifferentiableAt ℝ x 0)
    (hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1)
    (hlevel : ∀ᶠ y : s → ℝ in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v)
    {q : ℝ → (s → ℝ)} (hq : DifferentiableAt ℝ q 0)
    (hpositive : ∀ v, 0 < q 0 v)
    (hsum : ∀ᶠ ε : ℝ in 𝓝 0, ∑ v, q ε v = 1) :
    ∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
      (∀ v : s, (character v.val θ : ℂ) = 1) →
      tailoringFamily I β 1
        (β • x (β⁻¹ • (fun v => Real.log (q β⁻¹ v))), θ) = 1 := by
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v => Real.log (q β⁻¹ v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter hq hpositive).continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, ∀ v, 0 < q ε v := by
    apply Filter.eventually_all.mpr
    intro v
    exact (differentiableAt_pi.mp hq v).continuousAt.eventually
      (eventually_gt_nhds (hpositive v))
  filter_upwards [critical_reduced_branch_eventually_face_plateaus I hx hface hq hpositive,
    hparam.eventually hlevel, tendsto_inv_atTop_zero.eventually hsum,
    tendsto_inv_atTop_zero.eventually hpos, eventually_gt_atTop (0 : ℝ)]
    with β hcut hl hs hp hβ θ hθ
  obtain ⟨U, _, hu, hc⟩ := hcut
  exact tailoringFamily_eq_one_of_shifted_face_levels I hsub hβ.ne' (q β⁻¹) hp hs
    hl hθ (hc _ hu)

end FsFltz
