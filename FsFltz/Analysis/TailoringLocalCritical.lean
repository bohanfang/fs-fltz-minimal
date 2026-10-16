import FsFltz.Analysis.TailoringCriticalUniformLimits
import FsFltz.Analysis.TailoringGoodDifferential
import FsFltz.Analysis.TailoringConormalReality

/-!
# Positive holomorphic face equations at intrinsic critical points

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1428–1468.
The same actual full-fiber point has a proper-face holomorphic neighborhood,
positive real face monomials, and the uniform face-minimum approximation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- The actual full-fiber critical and zero sets have positive real
monomials on their holomorphic proper faces, with uniform convergence
to the corresponding literal face minima and normalized coefficients. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_positive_holomorphic
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a d : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEndStrong : IsStronglyCompatibleEndPotential I φEnd)
    (hEnd1 : ContDiff ℝ 1 φEnd) (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
      ∃ s : Finset (Lattice n),
        s = tailoringRetainedVertices I β (j.map z).1 ∧
        IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices ∧
        (∀ v ∈ s, (monomial (Real.exp (-β) : ℂ) v (j.map z)).im = 0 ∧
          0 < (monomial (Real.exp (-β) : ℂ) v (j.map z)).re) ∧
        TailoringFaceMinimumApproximation I φEnd β (j.map z) η ∧
        (∃ x ∈ polarFace I s, IsMinOn φEnd (polarFace I s) x ∧
          ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 < a v) ∧
            coordinateGradient φEnd x = ∑ v ∈ s, a v • latticeReal v ∧
            0 < ∑ v ∈ s, a v ∧
            ∀ v ∈ s,
              ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (β⁻¹ • (j.map z).1 - x)‖ +
                ‖tailoringRetainedMonomial I β v (j.map z) -
                  (a v / (∑ w ∈ s, a w) : ℝ)‖ < η) ∧
        ∃ O : Set (LGSpace n), IsOpen O ∧ j.map z ∈ O ∧
          ∀ w ∈ O,
            tailoringCutoff I β 0 w.1 = 1 ∧
            (∀ v ∈ I.vertices, tailoringCutoff I β v w.1 = if v ∈ s then 1 else 0) ∧
            tailoringFamily I β 1 w = ∑ v ∈ s, monomial (Real.exp (-β) : ℂ) v w := by
  classical
  obtain ⟨B, hB, hhol⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_holomorphic
    I hφ hc hU hlower hupper hEndStrong ha hEndLower hEnd
  obtain ⟨B', _, happrox⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_faceMinimum_approximation
    I hφ hc hU hlower hupper hEndStrong hEnd1 hd hEndConv ha hEndLower hEnd hη
  obtain ⟨B'', _, hconormal⟩ := tailoringEndpoint_exists_uniform_fullFiber_good_critical_conormal_eq
    I hφ hc hU hlower hupper
  obtain ⟨Beq, _, heq⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  obtain ⟨_, _, Brad, _, hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨_, _, hangle⟩ := hEndStrong.exists_coordinateGradient_radial_angle ha hEndLower
  refine ⟨max B (max B' (max B'' (max Beq Brad))), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hcritical
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβB' : B' ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβB'' : B'' ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβBeq : Beq ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hβBrad : Brad ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  obtain ⟨s, hseq, hs, hsne, hsproper, O, hO, hzO, hlocal⟩ :=
    hhol β hβB N j himage z hcritical
  obtain ⟨hzero, hcutoff, _⟩ := hlocal (j.map z) hzO
  have hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v (j.map z).1 = 0 ∨ tailoringCutoff I β v (j.map z).1 = 1 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv0 | hvV
    · subst v
      exact Or.inr hzero
    · rw [hcutoff v hvV]
      split_ifs <;> simp
  obtain ⟨t, ht⟩ := hconormal β hβB'' N j himage z hgood hcritical
  have hgrad : coordinateGradient φ (j.map z).1 ≠ 0 := by
    rw [heq β hβBeq 1 (by simp) (j.map z) hfiber]
    exact (hangle (j.map z).1 ((hrad β hβBrad (j.map z) hfiber).1)).1
  let q : Lattice n → ℂ := fun v => tailoringRetainedMonomial I β v (j.map z)
  have hsum : ∑ v ∈ s, q v = 1 := by
    calc
      ∑ v ∈ s, q v = ∑ v ∈ I.vertices, q v := by
        apply Finset.sum_subset hs.1
        intro v hv hvs
        exact tailoringRetainedMonomial_eq_zero_of_not_mem_support I β (j.map z)
          (Finset.Subset.refl _) hv (hseq ▸ hvs)
      _ = 1 := by
        change ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v (j.map z) = 1
        rw [sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β (j.map z) hfiber,
          hzero, Complex.ofReal_one]
  have hnormal : (fun k => (coordinateGradient φ (j.map z).1 k : ℂ)) =
      t • ∑ v ∈ s, q v • latticeComplex v := by
    rw [ht]
    congr 1
    symm
    apply Finset.sum_subset hs.1
    intro v hv hvs
    have hqzero := tailoringRetainedMonomial_eq_zero_of_not_mem_support I β (j.map z)
      (Finset.Subset.refl _) hv (hseq ▸ hvs)
    simp [q, hqzero]
  obtain ⟨_, _, hreal⟩ := face_complex_conormal_real I hs hsne hsproper hgrad q t hsum hnormal
  have hap := happrox β hβB' N j himage z hcritical
  have hnormalized := hap.exists_positive_normalized_coefficients
  rw [← hseq] at hnormalized
  refine ⟨s, hseq, hs, hsne, hsproper, ?_, hap, hnormalized, O, hO, hzO, hlocal⟩
  intro v hv
  have hqmon : q v = monomial (Real.exp (-β) : ℂ) v (j.map z) := by
    change (tailoringCutoff I β v (j.map z).1 : ℂ) * _ = _
    rw [hcutoff v (hs.1 hv), ite_eq_left hv, Complex.ofReal_one, one_mul]
  rw [← hqmon]
  exact ⟨hreal v hv, hap.1 v (hseq ▸ hv)⟩

end FsFltz
