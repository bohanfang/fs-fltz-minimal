import FsFltz.Geometry.PotentialPathRoundedMotionFiber
import FsFltz.Analysis.OriginalFiberDomain
import FsFltz.Analysis.OriginalRatioBounds
import FsFltz.Analysis.CompatiblePotentialPerturbation

/-!
# Native initial carriers for the holomorphic ribbon

Source: `geometric-part-fsf-proof.tex`, matching truncations, lines
1010–1049, and assembly, lines 2127–2147. The actual original full fiber
and its complete intrinsic flow construct nonempty regular truncations at
the logarithmic levels needed by the simultaneous pair transport.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance initialRibbonLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- The quadratic potential gives the literal original primitive. -/
theorem lambdaPotentialForm_quadratic :
    lambdaPotentialForm (fun u : RealSpace n => realSquaredNorm u / 2) = lambda0Form n := by
  have hg (u : RealSpace n) :
      coordinateGradient (fun x => realSquaredNorm x / 2) u = u := by
    funext j
    have hd := ((hasFDerivAt_realSquaredNorm u).const_mul (1 / 2 : ℝ)).fderiv
    have hgrad := congrFun (coordinateGradient_realSquaredNorm u) j
    change fderiv ℝ realSquaredNorm u (Pi.single j 1) = 2 * u j at hgrad
    change fderiv ℝ (fun x => realSquaredNorm x / 2) u (Pi.single j 1) = u j
    have hd' : fderiv ℝ (fun x => realSquaredNorm x / 2) u =
        (1 / 2 : ℝ) • fderiv ℝ realSquaredNorm u := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm,
        (hasFDerivAt_realSquaredNorm u).fderiv] using hd
    rw [hd']
    simp [hgrad]
  simp only [lambdaPotentialForm, lambda0Form, hg]

/-- Finite potential hypotheses construct a nonempty native carrier with
literal entire initial fiber and frontier images. No component or carrier
is supplied in the hypotheses, including in rank one. -/
theorem ToricInput.coefficientPath_potentialPath_exists_uniform_initialRibbon_carrier
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus →
      ∃ (D : CompactDomain (2 * n - 2))
        (j : D.extension.SmoothEmbedding (lgManifold n)),
        D.carrier.Nonempty ∧
        (∀ x, W I (j.map x) = (Real.exp β : ℂ)) ∧
        D.carrier = {x | phi0 (j.map x) ≤ Aminus} ∧
        frontier D.carrier = {x | phi0 (j.map x) = Aminus} ∧
        j.map '' D.carrier = {y | W I y = (Real.exp β : ℂ) ∧ phi0 y ≤ Aminus} := by
  classical
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφE := hφ.comp e.contDiff
  have hEndE := hEnd1.comp e.contDiff
  have hEndsE : ∀ u ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) u := by
    intro u hu
    apply (hEnd (e u) (by
      intro hz
      apply hu
      apply e.injective
      simpa only [map_zero] using hz)).comp u e.contDiff.contDiffAt
  have hhomE : ∀ r : ℝ, 0 < r → ∀ u, (φEnd ∘ e) (r • u) = r ^ 2 * (φEnd ∘ e) u := by
    intro r hr u
    simpa only [Function.comp_apply, map_smul] using hhom r hr (e u)
  have hendE : ∀ u, L ≤ ‖u‖ → (φ ∘ e) u = (φEnd ∘ e) u := by
    intro u hu
    exact hend (e u) hu
  obtain ⟨Aamb, R₀, hamb, hR₀, _⟩ := I.exists_initial_analytic_bounds
  obtain ⟨F, hF, B, hB, hbound⟩ :=
    I.coefficientPath_potentialPath_intrinsic_fiber_outward
      hφE hEndE hEndsE hhomE hc hlower hupper hL hendE Aamb
  have hR₀pos : 0 < R₀ := zero_lt_one.trans ((le_max_left _ _).trans_lt hR₀)
  refine ⟨F, hF, max B (Real.log R₀), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ Aminus hAminus
  have hR : max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β := by
    have he := Real.exp_le_exp.mpr ((le_max_right _ _).trans hβ)
    rw [Real.exp_log hR₀pos] at he
    exact hR₀.trans_le he
  let fiber := originalFullFiberModel I hamb hR
  let N := fiber.ambient.manifold
  let j := fiber.embedding
  let η : N.Point → ℝ := phi0 ∘ j.map
  have hη : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ η :=
    contMDiff_originalFullFiber_phi0 I hamb hR
  have hcompact (a : ℝ) : IsCompact {x : N.Point | η x ≤ a} :=
    isCompact_originalFullFiber_phi0_sublevel_all I hamb hR a
  have hbase (x : N.Point) : W I (j.map x) = (Real.exp β : ℂ) := by
    have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
    rwa [fiber.image] at hx
  have hψeq : potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) 0 ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm =
      (fun u => realSquaredNorm u / 2) := by
    funext u
    simp [e, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hpos (x : N.Point) (hx : Aminus ≤ η x) :
      0 < N.scalarDerivative η x (N.liouvilleVector fiber.ambient.primitive x) := by
    have hker := original_farFiber_embedding_tangent_range I hamb hR j fiber.image x
    have hout := (hbound β ((le_max_left _ _).trans hβ)).2 0 hzero 0 hzero
      (2 * n - 2) N j x (by simpa using hker)
      (by rw [hψeq]; exact hAminus.trans hx)
      (by rw [I.alongCoefficientPath_zero, hbase, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos β)])
    rw [hψeq, lambdaPotentialForm_quadratic] at hout
    rw [← fiber.primitive]
    exact hout.2
  let ρ : N.Point → ℝ := fun x => η x - Aminus
  have hρ := hη.sub_const Aminus
  have hρcompact : IsCompact {x : N.Point | ρ x ≤ 0} := by
    simpa only [ρ, sub_nonpos] using hcompact Aminus
  have hder (x : N.Point) (v : N.Tangent x) :
      N.scalarDerivative ρ x v = N.scalarDerivative η x v := by
    unfold scalarDerivative
    change mfderiv _ _ (η - fun _ => Aminus) x v = _
    rw [mfderiv_sub (hη.mdifferentiable (by simp) x) mdifferentiableAt_const,
      mfderiv_const, sub_zero]
    rfl
  have hreg := regular_zero_of_scalarDerivative_pos N ρ
    (N.liouvilleVector fiber.ambient.primitive) (by
      intro x hx
      rw [hder]
      exact hpos x (by have he := sub_eq_zero.mp hx; exact he.ge))
  let D := regularSublevelCompactDomain N ρ hρ hρcompact hreg
  have hDcarrier : D.carrier = {x | η x ≤ Aminus} := by
    ext x
    change η x - Aminus ≤ 0 ↔ η x ≤ Aminus
    exact sub_nonpos
  have hDfront : frontier D.carrier = {x | η x = Aminus} := by
    simpa only [ρ, sub_eq_zero] using
      regularSublevelCompactDomain_frontier N ρ hρ hρcompact hreg
  have hDne : D.carrier.Nonempty := by
    obtain ⟨y, hy⟩ := I.fullFiber_nonempty (Real.exp β)
    rw [← fiber.image] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨T, _, hentry⟩ := fiber.ambient.completeFlow.exists_nonneg_time_scalar_le η hη
      fiber.ambient.smooth_field hcompact Aminus (by
        intro z hz
        rw [fiber.ambient.field_eq_liouvilleVector]
        exact hpos z hz) x
    exact ⟨fiber.ambient.completeFlow.flow (-T) x, by rwa [hDcarrier]⟩
  refine ⟨D, j, hDne, hbase, hDcarrier, hDfront, ?_⟩
  rw [hDcarrier]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hbase x, hx⟩
  · rintro ⟨hy, hηy⟩
    have hyj : y ∈ range j.map := by rw [fiber.image]; exact hy
    obtain ⟨x, rfl⟩ := hyj
    exact ⟨x, hηy, rfl⟩

end FsFltz.Geometry
