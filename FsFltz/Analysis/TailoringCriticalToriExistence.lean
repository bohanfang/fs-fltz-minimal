import FsFltz.Analysis.TailoringCriticalToriBranch
import FsFltz.Analysis.TailoringCriticalToriHessian

/-!
# Reconstructed branches give actual intrinsic critical points

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`,
`eq:criticalIFT`, lines 1512–1540. The reduced branch is constructed from
the actual constrained minimum. Its shifted levels and cutoff plateaus
identify its literal retained normal, and the native normal converse gives
critical points on every presentation of the whole endpoint fiber. The
global potential is the same smooth extension of the homogeneous end.
This module does not exclude other critical points or assert the inertia.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- The retained monomial is exactly the reconstructed face weight, and is
zero at every other vertex. -/
theorem tailoringRetainedMonomial_eq_weight_of_shifted_face_levels
    (I : ToricInput n) {s : Finset (Lattice n)} {β : ℝ} (hβ : β ≠ 0)
    {x : RealSpace n} {θ : Torus n} (q : s → ℝ) (hq : ∀ v, 0 < q v)
    (hlevel : ∀ v : s, pairing v.val x = 1 + β⁻¹ * Real.log (q v))
    (hθ : ∀ v : s, (character v.val θ : ℂ) = 1)
    (hcut : ∀ a ∈ tailoringExponents I,
      tailoringCutoff I β a (β • x) = if a = 0 ∨ a ∈ s then 1 else 0)
    (v : Lattice n) (hv : v ∈ I.vertices) :
    tailoringRetainedMonomial I β v (β • x, θ) =
      if hvs : v ∈ s then (q ⟨v, hvs⟩ : ℂ) else 0 := by
  classical
  rw [tailoringRetainedMonomial, hcut v (Finset.mem_insert_of_mem hv)]
  by_cases hvs : v ∈ s
  · rw [ite_eq_left (Or.inr hvs), Complex.ofReal_one, one_mul, dite_eq_left hvs]
    exact monomial_eq_weight_of_shifted_face_level hβ (hq ⟨v, hvs⟩)
      (hlevel ⟨v, hvs⟩) (hθ ⟨v, hvs⟩)
  · have hv0 : v ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ hv)
    rw [dite_eq_right hvs, ite_eq_right (not_or.mpr ⟨hv0, hvs⟩)]
    simp only [Complex.ofReal_zero, zero_mul]

/-- The literal retained real normal is exactly the face normal map of the
positive reconstructed weights. -/
theorem tailoringRetained_real_normal_eq_of_shifted_face_levels
    (I : ToricInput n) {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    {β : ℝ} (hβ : β ≠ 0) {x : RealSpace n} {θ : Torus n}
    (q : s → ℝ) (hq : ∀ v, 0 < q v)
    (hlevel : ∀ v : s, pairing v.val x = 1 + β⁻¹ * Real.log (q v))
    (hθ : ∀ v : s, (character v.val θ : ℂ) = 1)
    (hcut : ∀ a ∈ tailoringExponents I,
      tailoringCutoff I β a (β • x) = if a = 0 ∨ a ∈ s then 1 else 0) :
    (∀ v ∈ I.vertices, (tailoringRetainedMonomial I β v (β • x, θ)).im = 0) ∧
      (∑ v ∈ I.vertices, (tailoringRetainedMonomial I β v (β • x, θ)).re • latticeReal v) =
        faceNormalMap s q := by
  classical
  have hret := tailoringRetainedMonomial_eq_weight_of_shifted_face_levels I hβ q hq hlevel hθ hcut
  constructor
  · intro v hv
    rw [hret v hv]
    split_ifs <;> simp
  · calc
      _ = ∑ v ∈ s, (tailoringRetainedMonomial I β v (β • x, θ)).re • latticeReal v := by
        symm
        apply Finset.sum_subset hsub
        intro v hv hvs
        rw [hret v hv, dite_eq_right hvs, Complex.zero_re, zero_smul]
      _ = ∑ v : s, q v • latticeReal v.val := by
        rw [← Finset.sum_attach]
        apply Finset.sum_congr rfl
        intro v _
        rw [hret v.val (hsub v.property), dite_eq_left v.property, Complex.ofReal_re]
      _ = faceNormalMap s q := (faceNormalMap_apply s q).symm

/-- The actual constrained minima and reduced implicit branch give intrinsic
critical points at every face-torus angle, for the same smooth ambient
potential whose homogeneous end was used to construct the branch. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_face_branch_native_critical
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hEnd : ∀ u, R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φEnd (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        (∀ v, 0 < (z β⁻¹).1 v) ∧ 0 < (z β⁻¹).2 ∧
        ∀ θ : Torus n, (∀ v : s, (character v.val θ : ℂ) = 1) →
          tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
          ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
            Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
            ∃ p : N.Point, j.map p = (faceCriticalRadius x z β, θ) ∧
              ∀ V : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p V = 0 := by
  classical
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  obtain ⟨x, z, hx₀, hm₀, hxs, _, hpos, hz₀, hzs, hsol, hzsol, _, hradial, hfiber⟩ :=
    hStrong.exists_actual_positive_faceReduced_branch hEnd1 hc hconv hs hsne hsproper
  have hstrict := hStrong.strict_of_polarFace_minimum hs hsne hsproper hx₀ hm₀
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
  have hμpos : 0 < ∑ v, faceReducedCoefficient φEnd x 0 v :=
    Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hq₀ : ∀ v, 0 < (z 0).1 v := by
    intro v
    rw [hz₀]
    exact div_pos (hpos v) hμpos
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter
        (hzs.fst.differentiableAt (by simp)) hq₀).continuousAt.tendsto.comp
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hcut := critical_reduced_branch_eventually_face_plateaus I
    (hxs.differentiableAt (by simp)) hface (hzs.fst.differentiableAt (by simp)) hq₀
  obtain ⟨Bg, _, hgrad⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  have hcomplete : ∀ᶠ β : ℝ in atTop,
      (∀ v, 0 < (z β⁻¹).1 v) ∧ 0 < (z β⁻¹).2 ∧
      ∀ θ : Torus n, (∀ v : s, (character v.val θ : ℂ) = 1) →
        tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∃ p : N.Point, j.map p = (faceCriticalRadius x z β, θ) ∧
            ∀ V : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p V = 0 := by
    filter_upwards [hcut, hparam.eventually hlevel,
      tendsto_inv_atTop_zero.eventually hzsol, hradial, hfiber,
      eventually_gt_atTop (0 : ℝ), eventually_ge_atTop Bg]
      with β hcutβ hlevelβ hsolβ hradialβ hfiberβ hβ hβg
    refine ⟨hsolβ.1, hsolβ.2.1, ?_⟩
    intro θ hθ
    have hy := hfiberβ θ hθ
    refine ⟨hy, ?_⟩
    intro N j himage
    have hymem : (faceCriticalRadius x z β, θ) ∈ Set.range j.map := by
      rw [himage]
      exact hy
    obtain ⟨p, hp⟩ := hymem
    refine ⟨p, hp, ?_⟩
    obtain ⟨U, _, hu, hcU⟩ := hcutβ
    have hcutpoint : ∀ a ∈ tailoringExponents I,
        tailoringCutoff I β a (faceCriticalRadius x z β) = if a = 0 ∨ a ∈ s then 1 else 0 :=
      hcU _ hu
    have hlevels : ∀ v : s,
        pairing v.val (x (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))) =
          1 + β⁻¹ * Real.log ((z β⁻¹).1 v) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hlevelβ
    obtain ⟨hreal, hnormal⟩ := tailoringRetained_real_normal_eq_of_shifted_face_levels
      I hs.1 hβ.ne' ((z β⁻¹).1) hsolβ.1 hlevels hθ hcutpoint
    have hnormalφ : coordinateGradient φ (faceCriticalRadius x z β) =
        (β * (z β⁻¹).2) • ∑ v ∈ I.vertices,
          (tailoringRetainedMonomial I β v (faceCriticalRadius x z β, θ)).re • latticeReal v := by
      rw [hgrad β hβg 1 (by simp) _ hy, hradialβ]
      simpa only [faceCriticalRadius] using
        congrArg (fun u => (β * (z β⁻¹).2) • u) hnormal.symm
    obtain ⟨ξ, hξ⟩ := lgCover_surjective n (faceCriticalRadius x z β, θ)
    have hξlog : ξ.1 = faceCriticalRadius x z β := by
      simpa only [lgCover] using congrArg Prod.fst hξ
    have hξpoint : j.map p = lgCover ξ := hp.trans hξ.symm
    have hgoodξ : ∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v ξ.1 = 0 ∨ tailoringCutoff I β v ξ.1 = 1 := by
      intro v hv
      rw [hξlog, hcutpoint v hv]
      split_ifs <;> simp
    have hrealξ : ∀ v ∈ I.vertices,
        (tailoringRetainedMonomial I β v (lgCover ξ)).im = 0 := by
      intro v hv
      exact (congrArg (fun y : LGSpace n => (tailoringRetainedMonomial I β v y).im) hξ).trans
        (hreal v hv)
    have hnormalξ : coordinateGradient φ ξ.1 = (β * (z β⁻¹).2) •
        ∑ v ∈ I.vertices, (tailoringRetainedMonomial I β v (lgCover ξ)).re • latticeReal v := by
      have htransport := congrArg (fun y : LGSpace n => (β * (z β⁻¹).2) •
        ∑ v ∈ I.vertices, (tailoringRetainedMonomial I β v y).re • latticeReal v) hξ
      exact (congrArg (coordinateGradient φ) hξlog).trans (hnormalφ.trans htransport.symm)
    exact tailoring_fullFiber_critical_of_real_normal_equation I β hφ N j himage p ξ hξpoint
      hgoodξ (β * (z β⁻¹).2) hrealξ hnormalξ
  obtain ⟨B, hB⟩ := eventually_atTop.mp hcomplete
  refine ⟨x, z, hx₀, hm₀, hxs, hzs, max B 1, ?_, ?_⟩
  · exact zero_lt_one.trans_le (le_max_right _ _)
  · intro β hβ
    exact hB β ((le_max_left _ _).trans hβ)

end FsFltz
