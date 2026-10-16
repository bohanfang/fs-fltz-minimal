import FsFltz.Analysis.TailoringCriticalToriExistence
import FsFltz.Analysis.TailoringLocalCritical
import FsFltz.Analysis.TailoringLyapunov
import FsFltz.ToricFaceTorus

/-!
# Exhaustion by the actual critical face branches

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1428–1468,
and `prop:morsebott`, lines 1512–1540. Uniform localization is consumed
together with the actual affine minimum and the local reduced implicit
function to rule out additional radial branches. All angles are quotient
torus characters.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- A positive real normalized monomial has trivial quotient character and
its logarithm is its literal normalized affine level. -/
theorem positive_monomial_character_and_log_level
    {β : ℝ} {v : Lattice n} {y : LGSpace n}
    (him : (monomial (Real.exp (-β) : ℂ) v y).im = 0)
    (hpos : 0 < (monomial (Real.exp (-β) : ℂ) v y).re) :
    (character v y.2 : ℂ) = 1 ∧
      Real.log (monomial (Real.exp (-β) : ℂ) v y).re = pairing v y.1 - β := by
  let q := (monomial (Real.exp (-β) : ℂ) v y).re
  have hreal : monomial (Real.exp (-β) : ℂ) v y = (q : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  have hnorm : q = Real.exp (pairing v y.1 - β) := by
    have h := norm_monomial (Real.exp (-β) : ℂ) v y
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← Real.exp_add] at h
    exact h.trans (congrArg Real.exp (by ring))
  refine ⟨?_, ?_⟩
  · have hmul : (q : ℂ) * (character v y.2 : ℂ) = (q : ℂ) * 1 := by
      calc
        _ = monomial (Real.exp (-β) : ℂ) v y := by
          rw [hnorm, monomial, sub_eq_add_neg, Real.exp_add]
          rw [← Complex.ofReal_exp]
          simp only [Complex.ofReal_mul]
          ring
        _ = _ := by rw [hreal, mul_one]
    exact mul_left_cancel₀ (by exact_mod_cast hpos.ne') hmul
  · change Real.log q = _
    rw [hnorm, Real.log_exp]

/-- Normalization removes the multiplier as an independent local unknown:
it is the sum of the actual reduced coefficients. Thus local IFT uniqueness
requires only proximity of the weights and the parameter. -/
theorem criticalReduced_eventually_unique_of_weights
    {ι : Type*} [Fintype ι] {a : (ι → ℝ) → (ι → ℝ)}
    (ha : ContinuousAt a 0) {q₀ : ι → ℝ} {μ₀ : ℝ}
    (hq₀ : ∀ i, 0 < q₀ i) (hμ₀ : ∑ i, a 0 i = μ₀)
    {z : ℝ → ((ι → ℝ) × ℝ)}
    (hunique : ∀ᶠ p in 𝓝 (0, (q₀, μ₀)),
      criticalReducedEquation a p = 0 ↔ z p.1 = p.2) :
    ∀ᶠ p : ℝ × (ι → ℝ) in 𝓝 (0, q₀), ∀ μ : ℝ,
      a (p.1 • (fun i => Real.log (p.2 i))) = μ • p.2 →
      (∑ i, p.2 i) = 1 → z p.1 = (p.2, μ) := by
  have hlog : ContinuousAt (fun p : ℝ × (ι → ℝ) => fun i => Real.log (p.2 i))
      (0, q₀) := by
    apply continuousAt_pi.mpr
    intro i
    have hcoord : ContinuousAt (fun p : ℝ × (ι → ℝ) => p.2 i) (0, q₀) := by fun_prop
    exact hcoord.log (hq₀ i).ne'
  have harg : ContinuousAt (fun p : ℝ × (ι → ℝ) =>
      p.1 • (fun i => Real.log (p.2 i))) (0, q₀) := continuousAt_fst.smul hlog
  have hac : ContinuousAt (fun p : ℝ × (ι → ℝ) =>
      a (p.1 • (fun i => Real.log (p.2 i)))) (0, q₀) := by
    exact ContinuousAt.comp (by simpa only [zero_smul] using ha) harg
  have hsum : ContinuousAt (fun p : ℝ × (ι → ℝ) =>
      ∑ i, a (p.1 • (fun i => Real.log (p.2 i))) i) (0, q₀) := by
    simpa only [Function.comp_def, criticalCoordinateSum_apply] using
      (criticalCoordinateSum (ι := ι)).continuous.continuousAt.comp hac
  have hmap : Tendsto (fun p : ℝ × (ι → ℝ) =>
      (p.1, (p.2, ∑ i, a (p.1 • (fun i => Real.log (p.2 i))) i)))
      (𝓝 (0, q₀)) (𝓝 (0, (q₀, μ₀))) := by
    simpa only [zero_smul, hμ₀] using
      (continuousAt_fst.prodMk (continuousAt_snd.prodMk hsum)).tendsto
  filter_upwards [hmap.eventually hunique] with p hp μ heq hsumq
  have hμ : ∑ i, a (p.1 • (fun i => Real.log (p.2 i))) i = μ := by
    rw [heq]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsumq, mul_one]
  rw [hμ] at hp
  apply hp.mp
  simp [criticalReducedEquation, heq, hsumq]

/-- Global uniqueness of the actual affine constrained minimum turns the
ambient normal equation into the literal reduced equation. -/
theorem faceCriticalRadius_eq_of_local_reduced_uniqueness
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hA : Surjective (faceLevelMap s))
    {x : (s → ℝ) → RealSpace n} {z : ℝ → ((s → ℝ) × ℝ)}
    {β : ℝ} (hβ : 0 < β) {u : RealSpace n} (hu : u ≠ 0) (q : s → ℝ)
    (hlevel : faceLevelMap s (β⁻¹ • u) =
      fun v => 1 + β⁻¹ * Real.log (q v))
    {Λ : ℝ} (hnormal : coordinateGradient φ u = Λ • faceNormalMap s q)
    (hsol : x (β⁻¹ • (fun v => Real.log (q v))) ∈
        faceCoordinateSlice s (β⁻¹ • (fun v => Real.log (q v))) ∧
      coordinateGradient φ (x (β⁻¹ • (fun v => Real.log (q v)))) =
        faceNormalMap s (faceReducedCoefficient φ x (β⁻¹ • (fun v => Real.log (q v)))) ∧
      IsMinOn φ (faceCoordinateSlice s (β⁻¹ • (fun v => Real.log (q v))))
        (x (β⁻¹ • (fun v => Real.log (q v)))))
    (hsum : ∑ v, q v = 1)
    (hunique : ∀ μ : ℝ,
      faceReducedCoefficient φ x (β⁻¹ • (fun v => Real.log (q v))) = μ • q →
      (∑ v, q v) = 1 → z β⁻¹ = (q, μ)) :
    u = faceCriticalRadius x z β := by
  have hscaled : coordinateGradient φ (β⁻¹ • u) =
      (β⁻¹ * Λ) • faceNormalMap s q := by
    rw [coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun v hv => (hφ.smooth v hv).differentiableAt (by simp)) hu (inv_pos.mpr hβ),
      hnormal, smul_smul]
  have hxmem : β⁻¹ • u ∈ faceCoordinateSlice s (β⁻¹ • (fun v => Real.log (q v))) := by
    apply (mem_faceCoordinateSlice_iff _ _ _).mpr
    simpa only [Pi.smul_apply, smul_eq_mul] using hlevel
  have hmin : IsMinOn φ (faceCoordinateSlice s (β⁻¹ • (fun v => Real.log (q v))))
      (β⁻¹ • u) := by
    apply isMinOn_faceAffineLevel_of_normal_equation (hφ1.differentiable (by simp))
      (convexOn_of_euclidean_convex_quadratic hc.le hconv) hxmem
    rw [hscaled, ← map_smul, faceNormalMap_eq_extended_sum]
  have hx : β⁻¹ • u = x (β⁻¹ • (fun v => Real.log (q v))) :=
    eq_of_faceAffineLevel_minima hφ1 hc hconv hxmem hsol.1 hmin hsol.2.2
  have heq : faceReducedCoefficient φ x (β⁻¹ • (fun v => Real.log (q v))) =
      (β⁻¹ * Λ) • q := by
    apply faceNormalMap_injective_of_surjective hA
    rw [map_smul, ← hsol.2.1, ← hx, hscaled]
  have hz := hunique (β⁻¹ * Λ) heq hsum
  rw [faceCriticalRadius, hz]
  change u = β • x (β⁻¹ • (fun v => Real.log (q v)))
  rw [← hx, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]

/-- Uniform approximation to a face minimum is approximation to its actual
reduced coefficients: the minimum and its normal coefficients are unique. -/
theorem TailoringFaceMinimumApproximation.weights_close_to_face_base
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices)
    {x₀ : RealSpace n} (hx₀ : x₀ ∈ polarFace I s)
    (hmin₀ : IsMinOn φ (polarFace I s) x₀) (a₀ : s → ℝ)
    (hnormal₀ : coordinateGradient φ x₀ = faceNormalMap s a₀)
    {β η : ℝ} {y : LGSpace n}
    (hseq : tailoringRetainedVertices I β y.1 = s)
    (happrox : TailoringFaceMinimumApproximation I φ β y η) :
    ∀ v : s, |(tailoringRetainedMonomial I β v.val y).re - a₀ v / (∑ w, a₀ w)| < η := by
  classical
  obtain ⟨b, hb, hminb, a, _, hnormal, _, herr⟩ :=
    happrox.exists_positive_normalized_coefficients
  rw [hseq] at hb hminb hnormal herr
  have hb₀ : b = x₀ := hφ.eq_of_polarFace_minima hφ1 hc hconv hs hsne hsproper
    hb hx₀ hminb hmin₀
  have ha : (fun v : s => a v.val) = a₀ := by
    apply faceNormalMap_injective_of_surjective (I.faceLevelMap_surjective hs hsne hsproper)
    rw [faceNormalMap_apply, Finset.sum_coe_sort s (fun v => a v • latticeReal v),
      ← hnormal, hb₀, hnormal₀]
  have hsum : ∑ v ∈ s, a v = ∑ v, a₀ v := by
    rw [← Finset.sum_coe_sort s a]
    exact congrArg (fun b : s → ℝ => ∑ v, b v) ha
  intro v
  have hbound := herr v.val v.property
  have hnorm : ‖tailoringRetainedMonomial I β v.val y -
      (a v.val / (∑ w ∈ s, a w) : ℝ)‖ < η :=
    lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) hbound
  have hare : a v.val = a₀ v := congrFun ha v
  have hle := Complex.abs_re_le_norm (tailoringRetainedMonomial I β v.val y -
    (a v.val / (∑ w ∈ s, a w) : ℝ))
  simpa only [Complex.sub_re, Complex.ofReal_re, hare, hsum] using hle.trans_lt hnorm

/-- Exact cutoff plateaus and the actual radial normal equation construct
native critical points with precisely the prescribed retained support. -/
theorem actual_faceReduced_branch_eventually_native_critical
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {s : Finset (Lattice n)} (hsub : s ⊆ I.vertices)
    {x : (s → ℝ) → RealSpace n} {z : ℝ → ((s → ℝ) × ℝ)}
    (hxs : ContDiffAt ℝ ∞ x 0) (hzs : ContDiffAt ℝ ∞ z 0)
    (hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1)
    (hpositive : ∀ v, 0 < (z 0).1 v)
    (hlevel : ∀ᶠ y in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v)
    (hzsol : ∀ᶠ ε : ℝ in 𝓝 0,
      (∀ v, 0 < (z ε).1 v) ∧ (∑ v, (z ε).1 v) = 1)
    (hradial : ∀ᶠ β : ℝ in atTop,
      coordinateGradient φEnd (faceCriticalRadius x z β) =
        (β * (z β⁻¹).2) • faceNormalMap s ((z β⁻¹).1))
    (hfiber : ∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
      (∀ v : s, (character v.val θ : ℂ) = 1) →
        tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1) :
    ∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
      (∀ v : s, (character v.val θ : ℂ) = 1) →
      tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
      tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
        ∃ p : N.Point, j.map p = (faceCriticalRadius x z β, θ) ∧
          ∀ V : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p V = 0 := by
  classical
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      (differentiableAt_critical_logarithmic_parameter
        (hzs.fst.differentiableAt (by simp)) hpositive).continuousAt.tendsto.comp
          (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hcut := critical_reduced_branch_eventually_face_plateaus I
    (hxs.differentiableAt (by simp)) hface (hzs.fst.differentiableAt (by simp)) hpositive
  obtain ⟨Bg, _, hgrad⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  filter_upwards [hcut, hparam.eventually hlevel,
    tendsto_inv_atTop_zero.eventually hzsol, hradial, hfiber,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop Bg]
    with β hcutβ hlevelβ hsolβ hradialβ hfiberβ hβ hβg θ hθ
  have hy := hfiberβ θ hθ
  obtain ⟨U, _, hu, hcU⟩ := hcutβ
  have hcutpoint : ∀ a ∈ tailoringExponents I,
      tailoringCutoff I β a (faceCriticalRadius x z β) = if a = 0 ∨ a ∈ s then 1 else 0 :=
    hcU _ hu
  have hsupport : tailoringRetainedVertices I β (faceCriticalRadius x z β) = s := by
    ext v
    rw [mem_tailoringRetainedVertices_iff]
    constructor
    · intro hv
      rw [hcutpoint v (Finset.mem_insert_of_mem hv.1)] at hv
      by_contra hvs
      have hv0 : v ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ hv.1)
      simpa [hv0, hvs] using hv.2
    · intro hv
      refine ⟨hsub hv, ?_⟩
      rw [hcutpoint v (Finset.mem_insert_of_mem (hsub hv)), ite_eq_left (Or.inr hv)]
      norm_num
  refine ⟨hy, hsupport, ?_⟩
  intro N j himage
  have hymem : (faceCriticalRadius x z β, θ) ∈ Set.range j.map := by
    rw [himage]
    exact hy
  obtain ⟨p, hp⟩ := hymem
  refine ⟨p, hp, ?_⟩
  have hlevels : ∀ v : s,
      pairing v.val (x (β⁻¹ • (fun v => Real.log ((z β⁻¹).1 v)))) =
        1 + β⁻¹ * Real.log ((z β⁻¹).1 v) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hlevelβ
  obtain ⟨hreal, hnormal⟩ := tailoringRetained_real_normal_eq_of_shifted_face_levels
    I hsub hβ.ne' ((z β⁻¹).1) hsolβ.1 hlevels hθ hcutpoint
  have hnormalφ : coordinateGradient φ (faceCriticalRadius x z β) =
      (β * (z β⁻¹).2) • ∑ v ∈ I.vertices,
        (tailoringRetainedMonomial I β v (faceCriticalRadius x z β, θ)).re • latticeReal v := by
    rw [hgrad β hβg 1 (by simp) _ hy, hradialβ]
    exact congrArg (fun u => (β * (z β⁻¹).2) • u) hnormal.symm
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

/-- The actual reduced branch exhausts every native critical or zero point
with its prescribed face support, and every point on the branch at a face
torus angle is an actual critical point with precisely that support. -/
theorem IsStronglyCompatibleEndPotential.exists_face_branch_exhaustive_native
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {a : ℝ} (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n, ∃ z : ℝ → ((s → ℝ) × ℝ),
      x 0 ∈ polarFace I s ∧ IsMinOn φEnd (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ z 0 ∧
      (∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ p : N.Point,
          ((∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0) ∨
            N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0) →
          tailoringRetainedVertices I β (j.map p).1 = s →
          (j.map p).1 = faceCriticalRadius x z β ∧
            ∀ v : s, (character v.val (j.map p).2 : ℂ) = 1) ∧
      (∀ᶠ β : ℝ in atTop, ∀ θ : Torus n,
        (∀ v : s, (character v.val θ : ℂ) = 1) →
        tailoringFamily I β 1 (faceCriticalRadius x z β, θ) = 1 ∧
        tailoringRetainedVertices I β (faceCriticalRadius x z β) = s ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∃ p : N.Point, j.map p = (faceCriticalRadius x z β, θ) ∧
            ∀ V : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p V = 0) := by
  classical
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  obtain ⟨x, z, hx₀, hmin₀, hxs, has, hpos, hz₀, hzs, hsol, hzsol, hunique, hradial, hfiber⟩ :=
    hStrong.exists_actual_positive_faceReduced_branch hEnd1 hd hEndConv hs hsne hsproper
  let A := faceReducedCoefficient φEnd x
  let q₀ : s → ℝ := fun v => A 0 v / (∑ w, A 0 w)
  have hμ : 0 < ∑ v, A 0 v := Finset.sum_pos (fun v _ => hpos v) Finset.univ_nonempty
  have hq₀ : ∀ v, 0 < q₀ v := fun v => div_pos (hpos v) hμ
  have hstrict := hStrong.strict_of_polarFace_minimum hs hsne hsproper hx₀ hmin₀
  have hface : ∀ v ∈ I.vertices,
      if v ∈ s then pairing v (x 0) = 1 else pairing v (x 0) < 1 := by
    intro v hv
    split_ifs with hvs
    · exact hx₀.2 v hvs
    · exact hstrict v hv hvs
  have hlevelx : ∀ᶠ y in 𝓝 0, ∀ v : s, pairing v.val (x y) = 1 + y v := by
    filter_upwards [hsol] with y hy v
    simpa only [faceLevelMap_apply] using
      congrFun ((mem_faceCoordinateSlice_iff s y (x y)).mp hy.1) v
  have hqz₀ : ∀ v, 0 < (z 0).1 v := by
    simpa only [hz₀] using hq₀
  have hbranch := actual_faceReduced_branch_eventually_native_critical hφ hEnd hs.1
    hxs hzs hface hqz₀ hlevelx (hzsol.mono fun ε hε => ⟨hε.1, hε.2.2.2⟩) hradial hfiber
  have hweights : ∀ᶠ p : ℝ × (s → ℝ) in 𝓝 (0, q₀), ∀ μ : ℝ,
      A (p.1 • (fun v => Real.log (p.2 v))) = μ • p.2 →
      (∑ v, p.2 v) = 1 → z p.1 = (p.2, μ) := by
    apply criticalReduced_eventually_unique_of_weights has.continuousAt hq₀ rfl
    simpa only [hz₀] using hunique
  have hlog : ContinuousAt (fun p : ℝ × (s → ℝ) => fun v => Real.log (p.2 v))
      (0, q₀) := by
    apply continuousAt_pi.mpr
    intro v
    have hcoord : ContinuousAt (fun p : ℝ × (s → ℝ) => p.2 v) (0, q₀) := by fun_prop
    exact hcoord.log (hq₀ v).ne'
  have harg : Tendsto (fun p : ℝ × (s → ℝ) =>
      p.1 • (fun v => Real.log (p.2 v))) (𝓝 (0, q₀)) (𝓝 0) := by
    have hh : ContinuousAt (fun p : ℝ × (s → ℝ) =>
        p.1 • (fun v => Real.log (p.2 v))) (0, q₀) := continuousAt_fst.smul hlog
    simpa only [zero_smul] using hh.tendsto
  have hnear : ∀ᶠ p : ℝ × (s → ℝ) in 𝓝 (0, q₀),
      (x (p.1 • (fun v => Real.log (p.2 v))) ∈
        faceCoordinateSlice s (p.1 • (fun v => Real.log (p.2 v))) ∧
       coordinateGradient φEnd (x (p.1 • (fun v => Real.log (p.2 v)))) =
         faceNormalMap s (A (p.1 • (fun v => Real.log (p.2 v)))) ∧
       IsMinOn φEnd (faceCoordinateSlice s (p.1 • (fun v => Real.log (p.2 v))))
         (x (p.1 • (fun v => Real.log (p.2 v))))) ∧
      (∀ μ : ℝ, A (p.1 • (fun v => Real.log (p.2 v))) = μ • p.2 →
        (∑ v, p.2 v) = 1 → z p.1 = (p.2, μ)) := by
    filter_upwards [harg.eventually hsol, hweights] with p hp hw
    exact ⟨⟨hp.1, hp.2.1, hp.2.2.1⟩, hw⟩
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨B, hB, hloc⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_positive_holomorphic
    I hφ hc hU hlower hupper hStrong hEnd1 hd hEndConv ha hEndLower hEnd hη
  obtain ⟨Bc, _, hconormal⟩ := tailoringEndpoint_exists_uniform_fullFiber_good_critical_conormal_eq
    I hφ hc hU hlower hupper
  obtain ⟨Bg, _, hgrad⟩ := tailoringFamily_exists_fiber_gradient_eq_homogeneousEnd I hEnd
  obtain ⟨_, _, Br, _, hrad⟩ := tailoringEndpoint_exists_small_relative_deficit I
    (show (0 : ℝ) < 1 by norm_num)
  have hinvnorm : Tendsto (fun β : ℝ => ‖β⁻¹‖) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).norm
  obtain ⟨Bi, hi⟩ := eventually_atTop.mp (hinvnorm.eventually_lt_const hη)
  have hn₀ : coordinateGradient φEnd (x 0) = faceNormalMap s (A 0) :=
    hsol.self_of_nhds.2.1
  refine ⟨x, z, hx₀, hmin₀, hxs, hzs,
    ⟨max B (max Bc (max Bg (max Br Bi))), hB.trans_le (le_max_left _ _), ?_⟩, hbranch⟩
  intro β hβ N j himage p hcritical hsupport
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβpos : 0 < β := hB.trans_le hβB
  have hβBc : Bc ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβBg : Bg ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβBr : Br ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hβBi : Bi ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  let y := j.map p
  have hy : tailoringFamily I β 1 y = 1 := by
    have hm : y ∈ Set.range j.map := ⟨p, rfl⟩
    rwa [himage] at hm
  obtain ⟨t, htseq, _, _, _, hpositive, happrox, _, O, _, hpO, hlocal⟩ :=
    hloc β hβB N j himage p hcritical
  have hts : t = s := htseq.trans hsupport
  rw [hts] at hpositive hlocal
  obtain ⟨hzero, hcut, _⟩ := hlocal (j.map p) hpO
  let q : s → ℝ := fun v => (tailoringRetainedMonomial I β v.val y).re
  have hmon (v : s) : tailoringRetainedMonomial I β v.val y =
      monomial (Real.exp (-β) : ℂ) v.val y := by
    change (tailoringCutoff I β v.val y.1 : ℂ) * _ = _
    rw [hcut v.val (hs.1 v.property), ite_eq_left v.property, Complex.ofReal_one, one_mul]
  have hqreal (v : s) : tailoringRetainedMonomial I β v.val y = (q v : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [hmon v, Complex.ofReal_im] using (hpositive v.val v.property).1
  have hθ (v : s) : (character v.val y.2 : ℂ) = 1 :=
    (positive_monomial_character_and_log_level (hpositive v.val v.property).1
      (hpositive v.val v.property).2).1
  have hlevel : faceLevelMap s (β⁻¹ • y.1) =
      fun v => 1 + β⁻¹ * Real.log (q v) := by
    ext v
    have hlogv := (positive_monomial_character_and_log_level
      (hpositive v.val v.property).1 (hpositive v.val v.property).2).2
    have he : Real.log (q v) = pairing v.val y.1 - β := by
      change Real.log (tailoringRetainedMonomial I β v.val y).re = _
      rw [hmon v]
      exact hlogv
    rw [faceLevelMap_apply, pairing_smul_real, he]
    field_simp [hβpos.ne']
    ring
  have hsumComplex : ∑ v ∈ s, tailoringRetainedMonomial I β v y = 1 := by
    calc
      _ = ∑ v ∈ I.vertices, tailoringRetainedMonomial I β v y := by
        apply Finset.sum_subset hs.1
        intro v hv hvs
        exact tailoringRetainedMonomial_eq_zero_of_not_mem_support I β y
          (Finset.Subset.refl _) hv (hsupport ▸ hvs)
      _ = 1 := by
        rw [sum_tailoringRetainedMonomial_eq_cutoff_of_fiber I β y hy,
          hzero, Complex.ofReal_one]
  have hsum : ∑ v, q v = 1 := by
    have h := congrArg Complex.re hsumComplex
    simpa only [Complex.re_sum, Complex.one_re, ← Finset.sum_coe_sort s
      (fun v => (tailoringRetainedMonomial I β v y).re)] using h
  have hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v y.1 = 0 ∨ tailoringCutoff I β v y.1 = 1 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv0 | hvV
    · subst v
      exact Or.inr hzero
    · rw [hcut v hvV]
      split_ifs <;> simp
  obtain ⟨τ, hτ⟩ := hconormal β hβBc N j himage p hgood hcritical
  have hrealnormal : coordinateGradient φEnd y.1 = τ.re • faceNormalMap s q := by
    rw [← hgrad β hβBg 1 (by simp) y hy]
    have hnormalface : tailoringRetainedNormal I β y =
        ∑ v : s, (q v : ℂ) • latticeComplex v.val := by
      rw [tailoringRetainedNormal_eq_face_sum I β y hs.1
        (by intro v hv; exact hsupport ▸ hv)]
      change (∑ v : s, tailoringRetainedMonomial I β v.val y • latticeComplex v.val) = _
      exact Finset.sum_congr rfl (fun v _ => by rw [hqreal v])
    rw [hnormalface] at hτ
    ext k
    have hk := congrArg (fun b : Fin n → ℂ => (b k).re) hτ
    simpa [faceNormalMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, latticeComplex, latticeReal, Finset.mul_sum, mul_assoc] using hk
  have hclose : ‖q - q₀‖ < η := by
    apply (pi_norm_lt_iff hη).mpr
    intro v
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      happrox.weights_close_to_face_base hStrong hEnd1 hd hEndConv hs hsne hsproper
        hx₀ hmin₀ (A 0) hn₀ hsupport v
  have hnearβ := hball (show (β⁻¹, q) ∈ Metric.ball (0, q₀) η by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, dist_eq_norm]
    exact ⟨hi β hβBi, hclose⟩)
  refine ⟨?_, hθ⟩
  exact faceCriticalRadius_eq_of_local_reduced_uniqueness hStrong hEnd1 hd hEndConv
    (I.faceLevelMap_surjective hs hsne hsproper) (hB.trans_le hβB)
    (hrad β hβBr y hy).1 q hlevel hrealnormal hnearβ.1 hsum hnearβ.2

/-- One common large-parameter threshold classifies the entire native
critical locus and Liouville zero locus as a finite disjoint union of the
literal embedded face tori. -/
theorem IsStronglyCompatibleEndPotential.exists_fullFiber_critical_face_tori
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {d : ℝ} (hd : 0 < d)
    (hEndConv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φEnd ((EuclideanSpace.equiv (Fin n) ℝ) u) - d * ‖u‖ ^ 2))
    {a : ℝ} (ha : 0 < a) (hEndLower : ∀ u, a * ‖u‖ ^ 2 ≤ φEnd u)
    {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {R : ℝ} (hEnd : ∀ u,
      R ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ u : {s : Finset (Lattice n) //
        IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices} → ℝ → RealSpace n,
      ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
        (∀ s, ∀ θ ∈ coneTorus (positiveCone s.val),
          tailoringFamily I β 1 (u s β, θ) = 1 ∧
          tailoringRetainedVertices I β (u s β) = s.val) ∧
        Pairwise (fun s t => Disjoint
          ({u s β} ×ˢ coneTorus (positiveCone s.val))
          ({u t β} ×ˢ coneTorus (positiveCone t.val))) ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ p : N.Point,
          ((∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0) ↔
            ∃ s, j.map p ∈ {u s β} ×ˢ coneTorus (positiveCone s.val)) ∧
          (((∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0) ∨
            N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0) ↔
            ∃ s, j.map p ∈ {u s β} ×ˢ coneTorus (positiveCone s.val)) ∧
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0 ↔
            ∃ s, j.map p ∈ {u s β} ×ˢ coneTorus (positiveCone s.val)) := by
  classical
  let F := {s : Finset (Lattice n) //
    IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices}
  let embed : F → {s // s ∈ I.vertices.powerset} := fun s =>
    ⟨s.val, Finset.mem_powerset.mpr s.property.1.1⟩
  have hinj : Injective embed := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun t : {s // s ∈ I.vertices.powerset} => t.val) h
  let : Finite F := Finite.of_injective embed hinj
  let : Fintype F := Fintype.ofFinite F
  have hface (s : F) : ∃ r : ℝ → RealSpace n, ∀ᶠ β : ℝ in atTop,
      (∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ p : N.Point,
        ((∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0) ∨
          N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0) →
        tailoringRetainedVertices I β (j.map p).1 = s.val →
          (j.map p).1 = r β ∧ ∀ v : s.val, (character v.val (j.map p).2 : ℂ) = 1) ∧
      (∀ θ : Torus n, (∀ v : s.val, (character v.val θ : ℂ) = 1) →
        tailoringFamily I β 1 (r β, θ) = 1 ∧
        tailoringRetainedVertices I β (r β) = s.val ∧
        ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
          Set.range j.map = {y | tailoringFamily I β 1 y = 1} →
          ∃ p : N.Point, j.map p = (r β, θ) ∧
            ∀ V : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p V = 0) := by
    obtain ⟨x, z, _, _, _, _, ⟨B, _, hclass⟩, hbranch⟩ :=
      hStrong.exists_face_branch_exhaustive_native hEnd1 hd hEndConv ha hEndLower
        hφ hc hU hlower hupper hEnd s.property.1 s.property.2.1 s.property.2.2
    refine ⟨faceCriticalRadius x z, ?_⟩
    filter_upwards [eventually_ge_atTop B, hbranch] with β hβ hbranchβ
    exact ⟨hclass β hβ, hbranchβ⟩
  choose u hu using hface
  have hall : ∀ᶠ β : ℝ in atTop, ∀ s : F, _ := Filter.eventually_all.mpr hu
  obtain ⟨Bh, _, hhol⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_holomorphic
    I hφ hc hU hlower hupper hStrong ha hEndLower hEnd
  obtain ⟨Bz, _, heq⟩ := tailoringEndpoint_exists_uniform_fullFiber_critical_iff_liouville_zero
    I hφ hc hU hlower hupper hStrong ha hEndLower hEnd
  obtain ⟨B, hB⟩ := eventually_atTop.mp hall
  refine ⟨u, max 1 (max B (max Bh Bz)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβB : B ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβBh : Bh ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβBz : Bz ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hb := hB β hβB
  constructor
  · intro s θ hθ
    have hcharacters : ∀ v : s.val, (character v.val θ : ℂ) = 1 :=
      fun v => (I.mem_coneTorus_positiveCone_iff s.property.1 s.property.2.1
        s.property.2.2 θ).mp hθ v.val v.property
    exact ⟨((hb s).2 θ hcharacters).1, ((hb s).2 θ hcharacters).2.1⟩
  · constructor
    · intro s t hst
      apply Set.disjoint_left.mpr
      intro y hys hyt
      have hrs : tailoringRetainedVertices I β y.1 = s.val := by
        rw [hys.1]
        exact ((hb s).2 y.2 (fun v => (I.mem_coneTorus_positiveCone_iff s.property.1
          s.property.2.1 s.property.2.2 y.2).mp hys.2 v.val v.property)).2.1
      have hrt : tailoringRetainedVertices I β y.1 = t.val := by
        rw [hyt.1]
        exact ((hb t).2 y.2 (fun v => (I.mem_coneTorus_positiveCone_iff t.property.1
          t.property.2.1 t.property.2.2 y.2).mp hyt.2 v.val v.property)).2.1
      exact hst (Subtype.ext (hrs.symm.trans hrt))
    intro N j himage p
    have hforward :
        ((∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0) ∨
          N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) p = 0) →
        ∃ s : F, j.map p ∈ {u s β} ×ˢ coneTorus (positiveCone s.val) := by
      intro hp
      obtain ⟨s, hseq, hs, hsne, hsproper, _⟩ := hhol β hβBh N j himage p hp
      let f : F := ⟨s, hs, hsne, hsproper⟩
      obtain ⟨hrad, hchars⟩ := (hb f).1 N j himage p hp hseq.symm
      refine ⟨f, hrad, ?_⟩
      apply (I.mem_coneTorus_positiveCone_iff hs hsne hsproper (j.map p).2).mpr
      intro v hv
      exact hchars ⟨v, hv⟩
    have hbackward : (∃ s : F, j.map p ∈ {u s β} ×ˢ coneTorus (positiveCone s.val)) →
        ∀ v : N.Tangent p, N.scalarDerivative (fun q => φ (j.map q).1) p v = 0 := by
      rintro ⟨s, hp⟩
      have hcharacters : ∀ v : s.val, (character v.val (j.map p).2 : ℂ) = 1 :=
        fun v => (I.mem_coneTorus_positiveCone_iff s.property.1 s.property.2.1
          s.property.2.2 (j.map p).2).mp hp.2 v.val v.property
      obtain ⟨p', hp', hcrit⟩ := ((hb s).2 (j.map p).2 hcharacters).2.2 N j himage
      have hpoint : j.map p = (u s β, (j.map p).2) := Prod.ext hp.1 rfl
      have he : p' = p := j.embedding.injective (hp'.trans hpoint.symm)
      subst p'
      exact hcrit
    exact ⟨⟨fun hp => hforward (Or.inl hp), hbackward⟩,
      ⟨hforward, fun hp => Or.inl (hbackward hp)⟩,
      ⟨fun hp => hforward (Or.inr hp), fun hp =>
        (heq β hβBz N j himage p).mp (hbackward hp)⟩⟩

end FsFltz
