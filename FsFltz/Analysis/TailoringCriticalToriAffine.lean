import FsFltz.Analysis.FacePotentialMinima
import FsFltz.Analysis.TailoringCriticalConormalNative

/-!
# Affine constrained minima for the critical-torus equations

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1512–1517.
The shifted equations are the literal equations `A_F x = 1 + y`.
Existence, uniqueness, and stationarity are proved from continuity,
quadratic growth, and quantitative convexity. Smooth dependence on the
shift and the reduced implicit-function construction remain separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology BigOperators ContDiff

variable {n : ℕ}

/-- The actual affine equations with prescribed levels at the face normals. -/
def faceAffineLevel (s : Finset (Lattice n)) (b : Lattice n → ℝ) : Set (RealSpace n) :=
  {x | ∀ v ∈ s, pairing v x = b v}

@[simp]
theorem faceAffineLevel_one (s : Finset (Lattice n)) :
    faceAffineLevel s (fun _ => 1) = (polarFaceAffine s : Set (RealSpace n)) := rfl

theorem isClosed_faceAffineLevel (s : Finset (Lattice n)) (b : Lattice n → ℝ) :
    IsClosed (faceAffineLevel s b) := by
  unfold faceAffineLevel
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (by unfold pairing; fun_prop) continuous_const

theorem convex_faceAffineLevel (s : Finset (Lattice n)) (b : Lattice n → ℝ) :
    Convex ℝ (faceAffineLevel s b) := by
  intro x hx y hy a c _ _ hac v hv
  have h := (pairingCLM v).map_add (a • x) (c • y)
  simpa [hx v hv, hy v hv, ← add_mul, hac] using h

/-- The integral facet basis realizes every prescribed real level on a
nonempty proper face, including arbitrary shifts of the original levels. -/
theorem ToricInput.nonempty_faceAffineLevel (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (a : Lattice n → ℝ) :
    (faceAffineLevel s a).Nonempty := by
  classical
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hsne hsproper
  let L : Lattice n →ₗ[ℤ] ℝ := b.constr ℝ fun v => a v.val
  let R := realExtension L
  let x : RealSpace n := fun j => R ((Pi.basisFun ℝ (Fin n)) j)
  refine ⟨x, fun v hv => ?_⟩
  have hpair : pairing v x = R (latticeReal v) := by
    rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (latticeReal v)]
    simp [x, pairing, latticeReal, smul_eq_mul]
  rw [hpair, realExtension_latticeReal]
  simpa only [L, hb] using b.constr_basis ℝ (fun w => a w.val) ⟨v, hst hv⟩

/-- Quadratic growth produces a minimum on the actual closed affine slice;
the slice need not be compact. -/
theorem exists_faceAffineLevel_minimum {φ : RealSpace n → ℝ}
    (hφ : Continuous φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u : EuclideanSpace ℝ (Fin n),
      c * ‖u‖ ^ 2 ≤ φ ((EuclideanSpace.equiv (Fin n) ℝ) u))
    (s : Finset (Lattice n)) (b : Lattice n → ℝ)
    (hne : (faceAffineLevel s b).Nonempty) :
    ∃ x ∈ faceAffineLevel s b, IsMinOn φ (faceAffineLevel s b) x := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨x₀, hx₀⟩ := hne
  have hclosed : IsClosed (e ⁻¹' faceAffineLevel s b) :=
    (isClosed_faceAffineLevel s b).preimage e.continuous
  have hcoercive : ∀ᶠ u : EuclideanSpace ℝ (Fin n) in cocompact _,
      φ x₀ ≤ φ (e u) := by
    rw [← Metric.cobounded_eq_cocompact]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually
      (eventually_ge_atTop (max 1 (|φ x₀| / c)))] with u hu
    have hn : 1 ≤ ‖u‖ := (le_max_left _ _).trans hu
    have hr : |φ x₀| / c ≤ ‖u‖ := (le_max_right _ _).trans hu
    have hm : |φ x₀| ≤ c * ‖u‖ := by
      simpa [mul_comm] using (div_le_iff₀ hc).mp hr
    have hmn := mul_le_mul_of_nonneg_right hm (norm_nonneg u)
    have habs := mul_le_mul_of_nonneg_left hn (abs_nonneg (φ x₀))
    have hl := hlower u
    change c * ‖u‖ ^ 2 ≤ φ (e u) at hl
    nlinarith [le_abs_self (φ x₀)]
  obtain ⟨u, hu, hmin⟩ := (hφ.comp e.continuous).continuousOn.exists_isMinOn'
    hclosed (show e.symm x₀ ∈ e ⁻¹' faceAffineLevel s b by simpa using hx₀)
    (by simpa using hcoercive.filter_mono inf_le_left)
  refine ⟨e u, hu, fun y hy => ?_⟩
  simpa using hmin (show e.symm y ∈ e ⁻¹' faceAffineLevel s b by simpa using hy)

/-- At an affine constrained minimum every direction in the actual kernel
of the face-normal map annihilates the derivative. -/
theorem fderiv_eq_zero_of_faceAffineLevel_minimum {φ : RealSpace n → ℝ}
    {s : Finset (Lattice n)} {b : Lattice n → ℝ} {x d : RealSpace n}
    (hx : x ∈ faceAffineLevel s b) (hm : IsMinOn φ (faceAffineLevel s b) x)
    (hφ : DifferentiableAt ℝ φ x) (hd : ∀ v ∈ s, pairing v d = 0) :
    fderiv ℝ φ x d = 0 := by
  have hline (t : ℝ) : x + t • d ∈ faceAffineLevel s b := by
    intro v hv
    have h := (pairingCLM v).map_add x (t • d)
    simpa [hx v hv, hd v hv] using h
  have hlocal : IsLocalMin (fun t : ℝ => φ (x + t • d)) 0 :=
    Filter.Eventually.of_forall fun t => by simpa using hm (hline t)
  have hDline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hD : HasDerivAt (fun t : ℝ => φ (x + t • d)) (fderiv ℝ φ x d) 0 := by
    have hf : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • d) := by
      simpa only [zero_smul, add_zero] using hφ.hasFDerivAt
    exact hf.comp_hasDerivAt 0 hDline
  exact hD.deriv.symm.trans hlocal.deriv_eq_zero

/-- A derivative annihilating the face kernel is sufficient for a true
global constrained minimum of a differentiable convex potential. -/
theorem isMinOn_faceAffineLevel_of_kernel_stationary {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) (hconv : ConvexOn ℝ univ φ)
    {s : Finset (Lattice n)} {b : Lattice n → ℝ} {x : RealSpace n}
    (hx : x ∈ faceAffineLevel s b)
    (hstationary : ∀ d : RealSpace n, (∀ v ∈ s, pairing v d = 0) →
      fderiv ℝ φ x d = 0) :
    IsMinOn φ (faceAffineLevel s b) x := by
  intro y hy
  have hD : fderiv ℝ φ x (y - x) = 0 := hstationary _ fun v hv => by
    simpa [hx v hv, hy v hv] using (pairingCLM v).map_sub y x
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hconvE : ConvexOn ℝ univ (φ ∘ e) := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a c ha hc hac
    simpa only [Function.comp_apply, map_add, map_smul] using
      hconv.2 (mem_univ (e u)) (mem_univ (e v)) ha hc hac
  have hineq := fderiv_le_sub_of_convex hconvE (hd.comp e.differentiable)
    (e.symm x) (e.symm y)
  rw [fderiv_comp _ (hd _) e.differentiableAt, e.fderiv] at hineq
  change fderiv ℝ φ (e (e.symm x)) (e (e.symm y - e.symm x)) ≤ _ at hineq
  simp only [map_sub, e.apply_symm_apply, Function.comp_apply, hD] at hineq
  exact sub_nonneg.mp hineq

/-- The actual normal critical equation implies affine constrained
minimality, for arbitrary levels and without a sign assumption on its multiplier. -/
theorem isMinOn_faceAffineLevel_of_normal_equation {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) (hconv : ConvexOn ℝ univ φ)
    {s : Finset (Lattice n)} {b : Lattice n → ℝ} {x : RealSpace n}
    (hx : x ∈ faceAffineLevel s b) {a : Lattice n → ℝ}
    (hp : coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v) :
    IsMinOn φ (faceAffineLevel s b) x := by
  apply isMinOn_faceAffineLevel_of_kernel_stationary hd hconv hx
  intro d hdker
  rw [fderiv_eq_coordinateGradient_pairing, hp]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v hv
  rw [← Finset.mul_sum]
  change a v * pairing v d = 0
  rw [hdker v hv, mul_zero]

/-- Quantitative convexity makes the affine constrained minimum unique. -/
theorem eq_of_faceAffineLevel_minima {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} {b : Lattice n → ℝ} {x y : RealSpace n}
    (hx : x ∈ faceAffineLevel s b) (hy : y ∈ faceAffineLevel s b)
    (hmx : IsMinOn φ (faceAffineLevel s b) x)
    (hmy : IsMinOn φ (faceAffineLevel s b) y) : x = y := by
  have hpair : ∀ v ∈ s, pairing v (y - x) = 0 := by
    intro v hv
    simpa [hx v hv, hy v hv] using (pairingCLM v).map_sub y x
  have hDx := fderiv_eq_zero_of_faceAffineLevel_minimum hx hmx
    (hφ.differentiable (by simp) x) hpair
  have hDy := fderiv_eq_zero_of_faceAffineLevel_minimum hy hmy
    (hφ.differentiable (by simp) y) hpair
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hfd (z d : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (φ ∘ e) z d = fderiv ℝ φ (e z) (e d) := by
    rw [fderiv_comp z (hφ.differentiable (by simp) _) e.differentiableAt, e.fderiv]
    rfl
  have hinner : inner ℝ (gradient (φ ∘ e) (e.symm y) -
      gradient (φ ∘ e) (e.symm x)) (e.symm y - e.symm x) = 0 := by
    rw [inner_sub_left, inner_gradient_left, inner_gradient_left, hfd, hfd]
    simp only [map_sub, e.apply_symm_apply, hDx, hDy, sub_self]
  have hbound := mul_norm_sq_le_inner_gradient_sub_of_convex_quadratic
    ((hφ.comp e.contDiff).differentiable (by simp)) hconv (e.symm x) (e.symm y)
  rw [hinner] at hbound
  have hzero : e.symm y - e.symm x = 0 := by
    apply norm_eq_zero.mp
    have hsq : ‖e.symm y - e.symm x‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).mp
        (by simpa only [mul_zero, zero_mul, mul_comm] using hbound)
    nlinarith [norm_nonneg (e.symm y - e.symm x)]
  exact e.symm.injective (sub_eq_zero.mp hzero).symm

/-- Every shift of a proper face has exactly one actual constrained minimum
for the quantitative potential contracts already furnished by the finite input. -/
theorem ToricInput.exists_unique_faceAffineLevel_minimum (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ 1 φ) {c a : ℝ}
    (hc : 0 < c) (ha : 0 < a)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    (hlower : ∀ u : EuclideanSpace ℝ (Fin n),
      a * ‖u‖ ^ 2 ≤ φ ((EuclideanSpace.equiv (Fin n) ℝ) u))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (y : Lattice n → ℝ) :
    ∃ x ∈ faceAffineLevel s (fun v => 1 + y v),
      IsMinOn φ (faceAffineLevel s (fun v => 1 + y v)) x ∧
      ∀ z ∈ faceAffineLevel s (fun v => 1 + y v),
        IsMinOn φ (faceAffineLevel s (fun v => 1 + y v)) z → z = x := by
  obtain ⟨x, hx, hm⟩ := exists_faceAffineLevel_minimum hφ.continuous ha hlower s
    (fun v => 1 + y v) (I.nonempty_faceAffineLevel hs hsne hsproper _)
  exact ⟨x, hx, hm, fun z hz hmz => eq_of_faceAffineLevel_minima hφ hc hconv hz hx hmz hm⟩

end FsFltz
