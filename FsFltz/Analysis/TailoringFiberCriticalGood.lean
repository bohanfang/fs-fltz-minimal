import FsFltz.Analysis.TailoringFiberCriticalConormal
import FsFltz.Analysis.TailoringBadSeparation
import FsFltz.Analysis.PotentialPath

/-!
# Intrinsic critical points of the full endpoint avoid cutoff transitions

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1428–1431
and 1452–1454. The actual full-fiber critical estimate and the finite-input
uniform bad-region separation are substantive consumers of one another.
This proves the cutoff-value conclusion, without claiming a holomorphic
neighborhood or the remaining critical-point/full-core classification.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- Every intrinsic potential critical point and intrinsic Liouville zero
on the actual full endpoint fiber has every actual augmented cutoff equal
to zero or one, uniformly for all sufficiently large parameters. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_good
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U a : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEndStrong : IsStronglyCompatibleEndPotential I φEnd)
    (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ z : N.Point,
      ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
      ∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v (j.map z).1 = 0 ∨ tailoringCutoff I β v (j.map z).1 = 1 := by
  obtain ⟨C, hC, B, hB, hcrit⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_end_critical_conormal_bound
      I hφ hc hU hlower hupper hEnd
  obtain ⟨δ, hδ, B', hB', hsep⟩ :=
    tailoringEndpoint_exists_uniform_bad_conormal_separation I hEndStrong ha hEndLower
  obtain ⟨_, _, B'', hB'', hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨_, _, hangle⟩ := hEndStrong.exists_coordinateGradient_radial_angle ha hEndLower
  have hlim : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const hδ)
  refine ⟨max B (max B' (max B'' Be)), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hcritical v hv
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβB' : B' ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβB'' : B'' ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβBe : Be ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  obtain ⟨t, ht⟩ := hcrit β hβB N j himage z hcritical
  have hu := (hrad β hβB'' (j.map z) hfiber).1
  have hp := (hangle (j.map z).1 hu).1
  have hpn : 0 < ‖coordinateGradient φEnd (j.map z).1‖ := norm_pos_iff.mpr hp
  by_cases hzero : tailoringCutoff I β v (j.map z).1 = 0
  · exact Or.inl hzero
  refine Or.inr ?_
  by_contra hone
  have hbad : ∃ v ∈ tailoringExponents I,
      0 < tailoringCutoff I β v (j.map z).1 ∧ tailoringCutoff I β v (j.map z).1 < 1 :=
    ⟨v, hv,
      lt_of_le_of_ne (tailoringCutoff_nonneg I β v (j.map z).1) (Ne.symm hzero),
      lt_of_le_of_ne (tailoringCutoff_le_one I β v (j.map z).1) hone⟩
  have hb := hsep β hβB' (j.map z) hfiber hbad t
  have hstrict := mul_lt_mul_of_pos_right (he β hβBe) hpn
  exact (not_le_of_gt hstrict) (hb.trans ht)

/-- The finite toric input produces a smooth compatible potential and the
actual full symplectic endpoint fibers, with every intrinsic potential
critical point and every intrinsic Liouville zero avoiding all transitions. -/
theorem ToricInput.exists_compatiblePotential_with_fullFiber_critical_good
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧
      ContDiff ℝ ∞ φ ∧
      (∃ R > 0, ∀ u,
        R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} ∧
          N.IsSymplecticOn
            (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
              univ ∧
          ∀ z : N.Point,
          ((∀ v : N.Tangent z, N.scalarDerivative (fun q => φ (j.map q).1) z v = 0) ∨
            N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) z = 0) →
          ∀ v ∈ tailoringExponents I,
            tailoringCutoff I β v (j.map z).1 = 0 ∨
              tailoringCutoff I β v (j.map z).1 = 1 := by
  obtain ⟨φEnd, hstrong, hφEnd1, hφEnd0, a, ha, hconv, hpos, _⟩ :=
    I.exists_stronglyCompatibleEndPotential
  obtain ⟨φ, hφs, hφlower, _, ⟨R, hR, hend⟩, _⟩ :=
    exists_native_smooth_extension_with_legendre ha hφEnd1.continuous hφEnd0
      hstrong.smooth hconv hpos
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφEs : ContDiff ℝ ∞ (φ ∘ e) := hφs.comp e.contDiff
  have hφEndEs : ∀ x ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) x :=
    fun x hx => (hstrong.smooth (e x) (by simpa [e] using hx)).comp x e.contDiff.contDiffAt
  have hhom : ∀ r : ℝ, 0 < r → ∀ x, (φEnd ∘ e) (r • x) = r ^ 2 * (φEnd ∘ e) x := by
    intro r hr x
    simp only [Function.comp_apply, map_smul]
    exact hstrong.homogeneous r hr (e x)
  obtain ⟨U, hU, hUb⟩ := exists_hessian_norm_bound_of_homogeneous_end hR hφEs
    (hφEnd1.comp e.contDiff) hφEndEs hhom (fun x hx => by simpa [e] using hend (e x) hx)
  have hφupper := hessian_upperBound_of_norm_bound hUb
  have hend' : ∀ u, R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ →
      φ u = φEnd u := hend
  have hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u := by
    intro u
    have hn : ‖u‖ ≤ ‖e.symm u‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro k
      exact PiLp.norm_apply_le (e.symm u) k
    have hsq := pow_le_pow_left₀ (norm_nonneg u) hn 2
    exact (mul_le_mul_of_nonneg_left hsq ha.le).trans
      (by simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hpos (e.symm u))
  obtain ⟨B, hB, hgood⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_good
    I hφs ha hU hφlower hφupper hstrong ha hEndLower hend'
  obtain ⟨B', hB', hfull⟩ :=
    tailoringFamily_exists_uniform_symplectic_levelEmbedding I hφs ha hU hφlower hφupper
  refine ⟨φEnd, φ, hstrong, hφEnd1, hφs, ⟨R, hR, hend'⟩,
    max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  obtain ⟨N, j, himage, hsympl⟩ :=
    hfull β ((le_max_right _ _).trans hβ) 1 (by simp) 1 (by simp)
  exact ⟨N, j, himage, hsympl, hgood β ((le_max_left _ _).trans hβ) N j himage⟩

end FsFltz
