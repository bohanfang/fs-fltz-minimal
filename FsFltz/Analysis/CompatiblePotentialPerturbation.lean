import FsFltz.Analysis.CompatiblePotential
import FsFltz.Analysis.CoordinateLegendre
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Quadratic perturbation preserving finitely many open gradient conditions

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 620–624.
Compactness gives one positive quadratic coefficient preserving every open
star condition. The coordinate gradient is the native derivative in the
fixed basis; no new gradient representation is introduced.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace FsFltz

variable {n : ℕ}

theorem contDiff_realSquaredNorm : ContDiff ℝ ∞ (realSquaredNorm (n := n)) := by
  unfold realSquaredNorm
  fun_prop

theorem hasFDerivAt_realSquaredNorm (x : RealSpace n) :
    HasFDerivAt realSquaredNorm
      (∑ j : Fin n, (2 * x j) • (ContinuousLinearMap.proj j : RealSpace n →L[ℝ] ℝ)) x := by
  convert HasFDerivAt.sum (u := Finset.univ)
    (fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j x).pow 2) using 1
  · ext y
    simp [realSquaredNorm]
  · simp

theorem coordinateGradient_realSquaredNorm (x : RealSpace n) :
    coordinateGradient realSquaredNorm x = (2 : ℝ) • x := by
  ext j
  simp [coordinateGradient, (hasFDerivAt_realSquaredNorm x).fderiv,
    sum_apply, Pi.single_apply]

theorem continuousAt_coordinateGradient {φ : RealSpace n → ℝ} {x : RealSpace n}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContinuousAt (coordinateGradient φ) x := by
  apply continuousAt_pi.mpr
  intro j
  exact (hφ.continuousAt_fderiv (by simp)).clm_apply continuousAt_const

/-- Addition of the literal based Euclidean quadratic. -/
def quadraticPerturbation (φ : RealSpace n → ℝ) (δ : ℝ) (x : RealSpace n) : ℝ :=
  φ x + δ * realSquaredNorm x

theorem coordinateGradient_quadraticPerturbation {φ : RealSpace n → ℝ}
    {x : RealSpace n} (hφ : DifferentiableAt ℝ φ x) (δ : ℝ) :
    coordinateGradient (quadraticPerturbation φ δ) x = coordinateGradient φ x +
      (2 * δ) • x := by
  ext j
  have hnorm := (contDiff_realSquaredNorm (n := n)).differentiable (by simp) x
  change fderiv ℝ (fun y => φ y + δ * realSquaredNorm y) x (Pi.single j 1) = _
  simp only [coordinateGradient,
    fderiv_fun_add hφ (hnorm.const_mul δ), fderiv_const_mul hnorm,
    add_apply, smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he := congrFun (coordinateGradient_realSquaredNorm x) j
  change fderiv ℝ φ x (Pi.single j 1) + δ * fderiv ℝ realSquaredNorm x (Pi.single j 1) = _
  change fderiv ℝ realSquaredNorm x (Pi.single j 1) = 2 * x j at he
  rw [he]
  ring

/-- One compact set retains an open image condition under sufficiently small
linear perturbations. Pointwise regularity is enough near the compact set. -/
theorem eventually_compact_add_smul_mem_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) {f : E → E}
    (hf : ∀ x ∈ K, ContinuousAt f x) (hmem : MapsTo f K U) :
    ∀ᶠ δ : ℝ in 𝓝 0, ∀ x ∈ K, f x + (2 * δ) • x ∈ U := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hcont : ContinuousAt (fun z : ℝ × E => f z.2 + (2 * z.1) • z.2) (0, x) :=
    ((hf x hx).comp continuousAt_snd).add
      ((continuousAt_const.mul continuousAt_fst).smul continuousAt_snd)
  apply hcont.eventually
  exact hU.mem_nhds (by simpa using hmem hx)

/-- A single strictly positive quadratic coefficient preserves every member
of a finite collection of compact open gradient conditions. -/
theorem exists_quadraticPerturbation_gradient_mem
    {ι : Type*} [Finite ι] {K U : ι → Set (RealSpace n)}
    (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    {φ : RealSpace n → ℝ} (hφ : ∀ i x, x ∈ K i → ContDiffAt ℝ ∞ φ x)
    (hmem : ∀ i, MapsTo (coordinateGradient φ) (K i) (U i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      MapsTo (coordinateGradient (quadraticPerturbation φ δ)) (K i) (U i) := by
  have hev : ∀ i, ∀ᶠ δ : ℝ in 𝓝 0, ∀ x ∈ K i,
      coordinateGradient φ x + (2 * δ) • x ∈ U i := fun i =>
    eventually_compact_add_smul_mem_open (hK i) (hU i)
      (fun x hx => continuousAt_coordinateGradient (hφ i x hx)) (hmem i)
  have hall : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i x, x ∈ K i →
      coordinateGradient φ x + (2 * δ) • x ∈ U i := (eventually_all.mpr hev)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r / 2, by positivity, ?_⟩
  intro i x hx
  rw [coordinateGradient_quadraticPerturbation ((hφ i x hx).differentiableAt (by simp))]
  exact hball (by simpa [Real.dist_eq, abs_of_pos hr] using half_lt_self hr) i x hx

end FsFltz
