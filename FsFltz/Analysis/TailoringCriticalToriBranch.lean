import FsFltz.Analysis.TailoringCriticalToriSchur
import FsFltz.Analysis.TailoringCriticalToriReconstruction

/-!
# The actual reduced critical branch on the full tailored fiber

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott` and
`eq:criticalIFT`, lines 1512–1529. The coefficient is constructed as the
literal differential of the actual constrained minimum. The radial branch
has the exact prescribed face levels and lies on the full endpoint fiber
at every angle with trivial face characters. This does not yet assert the
full Morse–Bott classification or exclude other critical points.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped Topology BigOperators ContDiff

variable {n : ℕ}

/-- The source's reconstructed radial branch `u = β x(β⁻¹ log q)`. -/
def faceCriticalRadius {s : Finset (Lattice n)}
    (x : (s → ℝ) → RealSpace n) (z : ℝ → ((s → ℝ) × ℝ)) (β : ℝ) : RealSpace n :=
  β • x (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))

/-- Homogeneity converts the actual reduced normal equation into the
source's ambient gradient equation at the reconstructed radial point. -/
theorem faceCriticalRadius_eventually_normal_equation
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {s : Finset (Lattice n)}
    {x : (s → ℝ) → RealSpace n} {z : ℝ → ((s → ℝ) × ℝ)}
    (hxs : ContDiffAt ℝ ∞ x 0) (hzs : ContDiffAt ℝ ∞ z 0)
    (hxne : x 0 ≠ 0) (hpositive : ∀ v, 0 < (z 0).1 v)
    (hnormal : ∀ᶠ y in 𝓝 0,
      coordinateGradient φ (x y) = faceNormalMap s (faceReducedCoefficient φ x y))
    (hcritical : ∀ᶠ ε : ℝ in 𝓝 0,
      faceReducedCoefficient φ x (ε • (fun v => Real.log ((z ε).1 v))) =
        (z ε).2 • (z ε).1) :
    ∀ᶠ β : ℝ in atTop,
      coordinateGradient φ (faceCriticalRadius x z β) =
        (β * (z β⁻¹).2) • faceNormalMap s ((z β⁻¹).1) := by
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter
        (hzs.fst.differentiableAt (by simp)) hpositive).continuousAt.tendsto.comp
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hne : ∀ᶠ y : s → ℝ in 𝓝 0, x y ≠ 0 :=
    hxs.continuousAt.eventually (eventually_ne_nhds hxne)
  filter_upwards [hparam.eventually hnormal, hparam.eventually hne,
    tendsto_inv_atTop_zero.eventually hcritical, eventually_gt_atTop (0 : ℝ)]
    with β hn hnx hc hβ
  rw [faceCriticalRadius,
    coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun x hx => (hφ.smooth x hx).differentiableAt (by simp)) hnx hβ,
    hn, hc, map_smul, smul_smul]

/-- The actual homogeneous face potential constructs its positive reduced
branch and points on the literal whole tailored fiber, without a smooth
coefficient premise or assumed fiber membership. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_positive_faceReduced_branch
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φ (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧
      ContDiffAt ℝ ∞ (faceReducedCoefficient φ x) 0 ∧
      (∀ v, 0 < faceReducedCoefficient φ x 0 v) ∧
      z 0 = ((fun v => faceReducedCoefficient φ x 0 v /
        (∑ w, faceReducedCoefficient φ x 0 w)), ∑ w, faceReducedCoefficient φ x 0 w) ∧
      ContDiffAt ℝ ∞ z 0 ∧
      (∀ᶠ y in 𝓝 0,
        x y ∈ faceCoordinateSlice s y ∧
        coordinateGradient φ (x y) = faceNormalMap s (faceReducedCoefficient φ x y) ∧
        IsMinOn φ (faceCoordinateSlice s y) (x y) ∧
        (∀ b ∈ faceCoordinateSlice s y,
          IsMinOn φ (faceCoordinateSlice s y) b → b = x y) ∧
        ∀ h : s → ℝ, h ≠ 0 →
          0 < ∑ v, fderiv ℝ (faceReducedCoefficient φ x) y h v * h v) ∧
      (∀ᶠ ε : ℝ in 𝓝 0,
        (∀ v, 0 < (z ε).1 v) ∧ 0 < (z ε).2 ∧
        faceReducedCoefficient φ x (ε • (fun v => Real.log ((z ε).1 v))) =
          (z ε).2 • (z ε).1 ∧ (∑ v, (z ε).1 v) = 1) ∧
      (∀ᶠ p in 𝓝 (0, z 0),
        criticalReducedEquation (faceReducedCoefficient φ x) p = 0 ↔ z p.1 = p.2) ∧
      (∀ᶠ β : ℝ in atTop,
        coordinateGradient φ (faceCriticalRadius x z β) =
          (β * (z β⁻¹).2) • faceNormalMap s ((z β⁻¹).1)) ∧
      (∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
        (∀ v : s, (character v.val θ : ℂ) = 1) →
          tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1) := by
  classical
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  obtain ⟨x, hx₀, hm₀, hxs, _, has, hpos, hsol⟩ :=
    hφ.exists_actual_faceReducedCoefficient_pos_hessian hφ1 hc hconv hs hsne hsproper
  obtain ⟨z, hz, hzs, hzsol, hunique⟩ :=
    exists_normalized_positive_criticalReduced_branch has hpos
  have hstrict := hφ.strict_of_polarFace_minimum hs hsne hsproper hx₀ hm₀
  have hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1 := by
    intro v hv
    split_ifs with hvs
    · exact hx₀.2 v hvs
    · exact hstrict v hv hvs
  have hlevel : ∀ᶠ y in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v := by
    filter_upwards [hsol] with y hy v
    simpa only [faceLevelMap_apply] using
      congrFun ((mem_faceCoordinateSlice_iff s y (x y)).mp hy.1) v
  have hμpos : 0 < ∑ v, faceReducedCoefficient φ x 0 v :=
    Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hqpos : ∀ v, 0 < (z 0).1 v := by
    intro v
    rw [hz]
    exact div_pos (hpos v) hμpos
  have hfiber := critical_reduced_branch_eventually_mem_fullFiber I hs.1
    (hxs.differentiableAt (by simp)) hface hlevel
    (hzs.fst.differentiableAt (by simp)) hqpos
    (hzsol.mono fun ε hε => hε.2.2.2)
  have hxne : x 0 ≠ 0 := ne_zero_of_mem_polarFacet I hsne.choose
    ⟨hx₀.1, hx₀.2 hsne.choose hsne.choose_spec⟩
  have hradial := faceCriticalRadius_eventually_normal_equation hφ hxs hzs hxne hqpos
    (hsol.mono fun y hy => hy.2.1) (hzsol.mono fun ε hε => hε.2.2.1)
  refine ⟨x, z, hx₀, hm₀, hxs, has, hpos, hz, hzs, hsol, hzsol, ?_, hradial, hfiber⟩
  simpa only [hz] using hunique

/-- The coefficient and its normalized face branch are obtained from the
original finite toric input through the proved potential construction. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential_with_actual_faceReduced_branches
    (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∀ s, IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
        x 0 ∈ polarFace I s ∧ ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
        ContDiffAt ℝ ∞ (faceReducedCoefficient φ x) 0 ∧
        (∀ v, 0 < faceReducedCoefficient φ x 0 v) ∧
        (∀ᶠ ε : ℝ in 𝓝 0,
          (∀ v, 0 < (z ε).1 v) ∧ 0 < (z ε).2 ∧
          faceReducedCoefficient φ x (ε • (fun v => Real.log ((z ε).1 v))) =
            (z ε).2 • (z ε).1 ∧ (∑ v, (z ε).1 v) = 1) ∧
        (∀ᶠ β : ℝ in atTop,
          coordinateGradient φ (faceCriticalRadius x z β) =
            (β * (z β⁻¹).2) • faceNormalMap s ((z β⁻¹).1)) ∧
        (∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
          (∀ v : s, (character v.val θ : ℂ) = 1) →
            tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1) := by
  obtain ⟨φ, hφ, hφ1, hφ0, c, hc, hconv, _, _⟩ := I.exists_stronglyCompatibleEndPotential
  refine ⟨φ, hφ, hφ1, hφ0, ?_⟩
  intro s hs hsne hsproper
  obtain ⟨x, z, hx, _, hxs, has, hpos, _, hzs, _, hsol, _, hradial, hfiber⟩ :=
    hφ.exists_actual_positive_faceReduced_branch hφ1 hc hconv hs hsne hsproper
  exact ⟨x, z, hx, hxs, hzs, has, hpos, hsol, hradial, hfiber⟩

end FsFltz
