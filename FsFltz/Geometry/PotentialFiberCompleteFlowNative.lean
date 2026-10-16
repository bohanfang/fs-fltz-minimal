import FsFltz.Geometry.PotentialFiberRegular

/-!
# Complete native intrinsic flow of an actual potential fiber

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 803–818.
The actual shifted potential is a proper exhaustion on the literal closed
fiber. Cauchy–Schwarz controls its native derivative on the homogeneous
end; smoothness controls the compact remainder. The proper-exhaustion ODE
theorem constructs an actual complete intrinsic Liouville flow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

section Fiber

variable {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (I : ToricInput n) (w : ℂ) (ha : ∀ y, W I y = w → 0 < a I y)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | W I y = w})

include hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend ha himage

/-- On the actual homogeneous end, the native intrinsic exhaustion
derivative lies between zero and twice the actual potential. -/
theorem scalarDerivative_potential_W_level_end_bounds (x : N.Point)
    (hx : L < ‖(WithLp.toLp 2 (j.map x).1 : EuclideanSpace ℝ (Fin n))‖) :
    0 ≤ N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) ∧
      N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) ≤
          2 * φ (j.map x).1 := by
  obtain ⟨z, hz⟩ := lgCover_surjective n (j.map x)
  have hval : W I (j.map x) = w := by
    have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
    rwa [himage] at hx
  have hzfst : z.1 = (j.map x).1 := congrArg Prod.fst hz
  have hxz : L < ‖(WithLp.toLp 2 z.1 : EuclideanSpace ℝ (Fin n))‖ := by rwa [hzfst]
  have he := coordinateHessian_apply_self_on_homogeneous_end hφ hEnds hhom hL hend hxz
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)
  have hapos : 0 < toricInverseMetricSq H I (j.map x) := by
    dsimp [H]
    rw [hzfst]
    exact toricInverseMetricSq_potentialHessian_pos hφ hc hU hlower hupper I _ (ha _ hval)
  have hid := scalarDerivative_potential_W_fiberLiouville hφ I z H (fun _ => rfl) he
    N j x hz.symm (potential_W_levelEmbedding_tangent_range I w ha j himage x) hapos
  rw [hid]
  have hs : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
    inner_fderiv_gradient_symmetric (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
  have hp : ∀ v, 0 ≤ inner ℝ (H v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg ‖v‖)).trans (hlower _ v)
  obtain ⟨hlo, hhi⟩ := potentialMetricFiberDefect_bounds H hs hp I (j.map x) hapos
  refine ⟨hlo, hhi.trans ?_⟩
  dsimp [H]
  rw [hzfst, metricRadialSq_potential_eq_two_mul hEnd1 hEnds hhom hc hlower hL hend _ hx]

omit hU hupper ha in
/-- The full literal fiber is closed, so actual ambient potential sublevels
pull back to compact intrinsic sublevels. -/
theorem isCompact_potential_W_level_sublevel (A : ℝ) :
    IsCompact {x : N.Point | φ (j.map x).1 ≤ A} := by
  have hclosed : IsClosed (range j.map) := by
    rw [himage]
    exact isClosed_eq (continuous_W I) continuous_const
  have hj : Topology.IsClosedEmbedding j.map := ⟨j.embedding, hclosed⟩
  exact hj.isCompact_preimage (isCompact_potential_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend A)

/-- The actual intrinsic Liouville field of the literal regular potential
fiber has a constructed jointly smooth all-real flow. The potential and
fiber realization remain the given ones throughout the construction. -/
theorem exists_potential_W_levelCompleteLiouvilleFlow :
    Nonempty (CompleteLiouvilleFlow N
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))) := by
  let μ := N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)
  let Z := N.liouvilleVector μ
  have hμ := N.isSmoothForm_pullback_one (lgManifold n) j.map _
    (isSmoothForm_lambdaPotentialForm hφ)
  have hsymp := isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage
  have hZ : N.IsSmoothVectorField Z := N.isSmoothVectorField_liouvilleVector μ hμ
    (fun x => hsymp.2.2 x (mem_univ _))
  obtain ⟨D, hD, hnonneg⟩ := exists_nonnegative_potential_shift hφ hEnd1 hEnds hhom hc hlower hL hend
  let ρ₀ : N.Point → ℝ := (fun y => φ y.1) ∘ j.map
  let ρ : N.Point → ℝ := fun x => ρ₀ x + D
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hρ₀ : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ ρ₀ :=
    (contMDiff_potentialValue hφ).comp j.map.contMDiff
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ ρ :=
    hρ₀.add contMDiff_const
  have hρnonneg : ∀ x, 0 ≤ ρ x := fun x => hnonneg (j.map x).1
  have hderiv : ∀ x v, N.scalarDerivative ρ x v = N.scalarDerivative ρ₀ x v := by
    intro x v
    have hd := mfderiv_add (hρ₀.mdifferentiable (by simp) x)
      (mdifferentiableAt_const (c := D) : MDifferentiableAt
        𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) (fun _ : N.Point => D) x)
    have he := congrArg (fun f : N.Tangent x →L[ℝ] ℝ => f v) hd
    simp only [Pi.add_def, mfderiv_const, add_zero] at he
    exact he
  have hclosed : IsClosed (range j.map) := by
    rw [himage]
    exact isClosed_eq (continuous_W I) continuous_const
  have hj : Topology.IsClosedEmbedding j.map := ⟨j.embedding, hclosed⟩
  have hcompactInner : IsCompact {x : N.Point | phi0 (j.map x) ≤ L ^ 2 / 2} :=
    hj.isCompact_preimage (isCompact_phi0_sublevel _ (by positivity))
  obtain ⟨B, hB⟩ := hcompactInner.exists_bound_of_continuousOn
    (N.continuous_scalarDerivative_vectorField hZ ρ hρ).continuousOn
  let C : ℝ := max B 2
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right B 2)
  have hbound : ∀ x, |N.scalarDerivative ρ x (Z x)| ≤ C * (1 + ρ x) := by
    intro x
    by_cases hout : L < ‖(WithLp.toLp 2 (j.map x).1 : EuclideanSpace ℝ (Fin n))‖
    · obtain ⟨hlo, hhi⟩ := scalarDerivative_potential_W_level_end_bounds hφ hEnd1 hEnds hhom
        hc hU hlower hupper hL hend I w ha j himage x hout
      rw [hderiv]
      change |N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)| ≤ _
      rw [abs_of_nonneg hlo]
      calc
        _ ≤ 2 * φ (j.map x).1 := hhi
        _ ≤ 2 * (1 + ρ x) := by dsimp [ρ, ρ₀]; linarith
        _ ≤ C * (1 + ρ x) := mul_le_mul_of_nonneg_right (le_max_right B 2) (by linarith [hρnonneg x])
    · have hx : x ∈ {x : N.Point | phi0 (j.map x) ≤ L ^ 2 / 2} := by
        have hr := le_of_not_gt hout
        have hs := (sq_le_sq₀ (norm_nonneg _) hL.le).mpr hr
        have hs' : realSquaredNorm (j.map x).1 ≤ L ^ 2 := by
          simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using hs
        change realSquaredNorm (j.map x).1 / 2 ≤ L ^ 2 / 2
        linarith
      have hb : |N.scalarDerivative ρ x (Z x)| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB x hx
      exact hb.trans ((le_max_left B 2).trans
        (le_mul_of_one_le_right hC.le (by linarith [hρnonneg x])))
  apply N.exists_completeFlow_of_proper_exhaustion Z hZ ρ hρ hρnonneg _ hC hbound
  intro A _
  have hset : {x : N.Point | ρ x ≤ A} = {x : N.Point | φ (j.map x).1 ≤ A - D} := by
    ext x
    change φ (j.map x).1 + D ≤ A ↔ φ (j.map x).1 ≤ A - D
    constructor <;> intro h <;> linarith
  rw [hset]
  exact isCompact_potential_W_level_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend I w j himage (A - D)

/-- A complete primitive on the given whole native regular fiber. Every
field and flow is constructed from the literal restricted primitive. -/
def potential_W_levelCompletePrimitive :
    CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) where
  smooth_primitive := N.isSmoothForm_pullback_one (lgManifold n) j.map _
    (isSmoothForm_lambdaPotentialForm hφ)
  symplectic := isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage
  smooth_field := N.isSmoothVectorField_liouvilleVector _
    (N.isSmoothForm_pullback_one (lgManifold n) j.map _ (isSmoothForm_lambdaPotentialForm hφ))
    (fun x => (isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage).2.2 x (mem_univ _))
  contraction := fun x => N.liouvilleVector_contraction _ x
    (N.liouvilleEquation_exists _ x
      ((isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage).2.2 x (mem_univ _)))
  completeFlow := Classical.choice (exists_potential_W_levelCompleteLiouvilleFlow hφ hEnd1 hEnds hhom
    hc hU hlower hupper hL hend I w ha j himage)

omit ha himage in
/-- One disk works for the entire prescribed coefficient path. Beyond it,
the whole literal fiber has a constructed actual complete intrinsic
primitive for the retained chosen potential, without regularity or flow
being supplied as additional input. -/
theorem ToricInput.coefficientPath_exists_completePotentialFiber :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, B < ‖w‖ →
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        range j.map = {y | W (I.alongCoefficientPath t) y = w} ∧
          Nonempty (CompletePrimitive N
            (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) := by
  obtain ⟨B, hB, hpos⟩ := I.coefficientPath_a_pos_of_large_value
  refine ⟨B, hB, fun t ht w hw => ?_⟩
  have ha : ∀ y, W (I.alongCoefficientPath t) y = w → 0 < a (I.alongCoefficientPath t) y := by
    intro y hy
    exact hpos t ht y (by rwa [hy])
  obtain ⟨N, j, himage, _⟩ := exists_potential_W_level_symplecticEmbedding
    hφ hc hU hlower hupper (I.alongCoefficientPath t) w ha
  exact ⟨N, j, himage, ⟨potential_W_levelCompletePrimitive hφ hEnd1 hEnds hhom hc hU
    hlower hupper hL hend (I.alongCoefficientPath t) w ha j himage⟩⟩

end Fiber
end FsFltz.Geometry
