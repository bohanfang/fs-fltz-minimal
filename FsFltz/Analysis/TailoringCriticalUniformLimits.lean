import FsFltz.Analysis.TailoringCriticalFaceLimits

/-!
# Uniform approximation by the actual retained-face minimum

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1440–1448
and 1454–1468. Both positions and actual retained coefficients approach
the unique minimum and its positive normalized normal coefficients.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- An explicit comparison with the literal minimum of the actual
retained polar face and its positive normalized normal representation. -/
def TailoringFaceMinimumApproximation (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β : ℝ) (y : LGSpace n) (η : ℝ) : Prop :=
  (∀ v ∈ tailoringRetainedVertices I β y.1,
    0 < (tailoringRetainedMonomial I β v y).re) ∧
  ∃ x ∈ polarFace I (tailoringRetainedVertices I β y.1),
    IsMinOn φ (polarFace I (tailoringRetainedVertices I β y.1)) x ∧
    ∃ q : Lattice n → ℂ, ∃ τ : ℂ,
      (∑ v ∈ I.vertices, q v = 1) ∧ τ.im = 0 ∧ 0 < τ.re ∧
      (∀ v ∈ I.vertices, v ∉ tailoringRetainedVertices I β y.1 → q v = 0) ∧
      (∀ v ∈ tailoringRetainedVertices I β y.1, (q v).im = 0 ∧ 0 < (q v).re) ∧
      (fun k => (coordinateGradient φ x k : ℂ)) =
        τ • ∑ v ∈ I.vertices, q v • latticeComplex v ∧
      ∀ v ∈ I.vertices,
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (β⁻¹ • y.1 - x)‖ +
          ‖tailoringRetainedMonomial I β v y - q v‖ < η

/-- The comparison coefficients are exactly the positive real gradient
coefficients divided by their sum, as in the source's uniform estimate. -/
theorem TailoringFaceMinimumApproximation.exists_positive_normalized_coefficients
    {I : ToricInput n} {φ : RealSpace n → ℝ} {β η : ℝ} {y : LGSpace n}
    (h : TailoringFaceMinimumApproximation I φ β y η) :
    ∃ x ∈ polarFace I (tailoringRetainedVertices I β y.1),
      IsMinOn φ (polarFace I (tailoringRetainedVertices I β y.1)) x ∧
      ∃ a : Lattice n → ℝ,
        (∀ v ∈ tailoringRetainedVertices I β y.1, 0 < a v) ∧
        coordinateGradient φ x = ∑ v ∈ tailoringRetainedVertices I β y.1, a v • latticeReal v ∧
        0 < ∑ v ∈ tailoringRetainedVertices I β y.1, a v ∧
        ∀ v ∈ tailoringRetainedVertices I β y.1,
          ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (β⁻¹ • y.1 - x)‖ +
            ‖tailoringRetainedMonomial I β v y -
              (a v / (∑ w ∈ tailoringRetainedVertices I β y.1, a w) : ℝ)‖ < η := by
  classical
  obtain ⟨_, x, hx, hmin, q, τ, hsum, hτim, hτpos, hqoff, hqpos, hp, herr⟩ := h
  let s := tailoringRetainedVertices I β y.1
  let a : Lattice n → ℝ := fun v => τ.re * (q v).re
  have hs := tailoringRetainedVertices_subset I β y.1
  have hsumS : ∑ v ∈ s, q v = 1 := by
    rw [← hsum]
    exact Finset.sum_subset hs (fun v hv hvs => hqoff v hv hvs)
  have hsumRe : ∑ v ∈ s, (q v).re = 1 := by
    simpa using congrArg Complex.re hsumS
  have hsumA : ∑ v ∈ s, a v = τ.re := by
    change ∑ v ∈ s, τ.re * (q v).re = τ.re
    rw [← Finset.mul_sum, hsumRe, mul_one]
  have hnormal : (fun k => (coordinateGradient φ x k : ℂ)) =
      τ • ∑ v ∈ s, q v • latticeComplex v := by
    rw [hp]
    congr 1
    symm
    exact Finset.sum_subset hs (fun v hv hvs => by simp [hqoff v hv hvs])
  have hgrad : coordinateGradient φ x = ∑ v ∈ s, a v • latticeReal v := by
    ext k
    have hk := congrArg (fun z : Fin n → ℂ => (z k).re) hnormal
    simpa [a, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_re, hτim, mul_assoc] using hk
  refine ⟨x, hx, hmin, a, fun v hv => mul_pos hτpos (hqpos v hv).2,
    hgrad, hsumA.symm ▸ hτpos, ?_⟩
  intro v hv
  have hratio : a v / (∑ w ∈ s, a w) = (q v).re := by
    rw [hsumA]
    exact mul_div_cancel_left₀ _ hτpos.ne'
  have hqeq : ((a v / (∑ w ∈ s, a w) : ℝ) : ℂ) = q v := by
    rw [hratio]
    apply Complex.ext
    · simp
    · simpa using (hqpos v hv).1.symm
  rw [hqeq]
  exact herr v (hs hv)

/-- Vanishing critical-conormal errors give uniform approximation by
the actual retained-face minimum and its positive normalized coefficients. -/
theorem tailoringEndpoint_exists_uniform_small_conormal_faceMinimum_approximation
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {a : ℝ} (ha : 0 < a) (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ t : ℂ,
        ‖(fun k => (coordinateGradient φ y.1 k : ℂ)) -
          t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖) →
      TailoringFaceMinimumApproximation I φ β y η := by
  classical
  by_contra! hno
  have hex (j : ℕ) : ∃ β ≥ (j : ℝ) + 1, ∃ y : LGSpace n,
      tailoringFamily I β 1 y = 1 ∧
      (∃ t : ℂ,
        ‖(fun k => (coordinateGradient φ y.1 k : ℂ)) -
          t • tailoringRetainedNormal I β y‖ ≤
            ((j : ℝ) + 1)⁻¹ * ‖coordinateGradient φ y.1‖) ∧
      ¬ TailoringFaceMinimumApproximation I φ β y η :=
    hno (((j : ℝ) + 1)⁻¹) (inv_pos.mpr (by positivity))
      ((j : ℝ) + 1) (by positivity)
  choose β hβj y hy ht hbad using hex
  choose t herr using ht
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hindex : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by linarith) tendsto_natCast_atTop_atTop
  have hβ : Tendsto β atTop atTop := tendsto_atTop_mono hβj hindex
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hindex
  obtain ⟨ρ, hρ, s, hs, _, _, x, hxF, hmin, _, q, τ, hx, hq, hτ,
      hsupport, hsum, hτim, hτpos, hqpos, hp⟩ :=
    tailoringEndpoint_extract_positive_face_minimum_limit I hφ hφ1 hc hconv ha hlower
      β y t ε hβ hε (Eventually.of_forall hy) (Eventually.of_forall herr)
  have hqoff : ∀ v ∈ I.vertices, v ∉ s → q v = 0 := by
    intro v hv hvs
    have heq : (fun j => tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j))) =ᶠ[atTop]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [hsupport] with j hj
      exact tailoringRetainedMonomial_eq_zero_of_not_mem_support I (β (ρ j)) (y (ρ j))
        (Finset.Subset.refl _) hv (hj.symm ▸ hvs)
    exact tendsto_nhds_unique (hq v hv) (tendsto_const_nhds.congr' heq.symm)
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hxE : Tendsto (fun j => e.symm ((β (ρ j))⁻¹ • (y (ρ j)).1))
      atTop (𝓝 (e.symm x)) := e.symm.continuous.tendsto x |>.comp hx
  have hposition : ∀ᶠ j in atTop,
      ‖e.symm ((β (ρ j))⁻¹ • (y (ρ j)).1) - e.symm x‖ < η / 2 := by
    have hh : Tendsto (fun j => ‖e.symm ((β (ρ j))⁻¹ • (y (ρ j)).1) - e.symm x‖)
        atTop (𝓝 0) := by simpa using (hxE.sub_const (e.symm x)).norm
    exact hh.eventually_lt_const (by positivity)
  have hcoeff : ∀ᶠ j in atTop, ∀ v ∈ I.vertices,
      ‖tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j)) - q v‖ < η / 2 := by
    apply (I.vertices.eventually_all).mpr
    intro v hv
    have hh : Tendsto
        (fun j => ‖tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j)) - q v‖)
        atTop (𝓝 0) := by simpa using ((hq v hv).sub_const (q v)).norm
    exact hh.eventually_lt_const (by positivity)
  have hpositive : ∀ᶠ j in atTop, ∀ v ∈ s,
      0 < (tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j))).re := by
    apply s.eventually_all.mpr
    intro v hv
    exact (Complex.continuous_re.continuousAt.tendsto.comp (hq v (hs.1 hv))).eventually_const_lt
      (hqpos v hv).2
  have hgood : ∀ᶠ j in atTop, TailoringFaceMinimumApproximation I φ
      (β (ρ j)) (y (ρ j)) η := by
    filter_upwards [hsupport, hposition, hcoeff, hpositive] with j hj hpos hco hpo
    unfold TailoringFaceMinimumApproximation
    rw [hj]
    refine ⟨hpo, x, hxF, hmin, q, τ, hsum, hτim, hτpos, hqoff, hqpos, hp, ?_⟩
    intro v hv
    change ‖e.symm ((β (ρ j))⁻¹ • (y (ρ j)).1 - x)‖ + _ < η
    rw [map_sub]
    linarith [hco v hv]
  obtain ⟨j, hj⟩ := hgood.exists
  exact hbad (ρ j) hj

/-- Every intrinsic critical or Liouville-zero point on every actual
full endpoint fiber approaches its own retained-face minimum uniformly. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_critical_faceMinimum_approximation
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
      TailoringFaceMinimumApproximation I φEnd β (j.map z) η := by
  obtain ⟨C, _, B, hB, hcrit⟩ :=
    tailoringEndpoint_exists_uniform_fullFiber_end_critical_conormal_bound
      I hφ hc hU hlower hupper hEnd
  obtain ⟨δ, hδ, B', _, happrox⟩ :=
    tailoringEndpoint_exists_uniform_small_conormal_faceMinimum_approximation
      I hEndStrong hEnd1 hd hEndConv ha hEndLower hη
  have hlim : Tendsto (fun β : ℝ => C * Real.exp (-Real.sqrt β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_sqrt_atTop)
  obtain ⟨Be, he⟩ := eventually_atTop.mp (hlim.eventually_lt_const hδ)
  refine ⟨max B (max B' Be), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage z hcritical
  have hfiber : tailoringFamily I β 1 (j.map z) = 1 := by
    have hmem : j.map z ∈ Set.range j.map := ⟨z, rfl⟩
    rwa [himage] at hmem
  apply happrox β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) (j.map z) hfiber
  obtain ⟨t, ht⟩ := hcrit β ((le_max_left _ _).trans hβ) N j himage z hcritical
  exact ⟨t, ht.trans (mul_le_mul_of_nonneg_right
    (he β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))).le (norm_nonneg _))⟩

end FsFltz
