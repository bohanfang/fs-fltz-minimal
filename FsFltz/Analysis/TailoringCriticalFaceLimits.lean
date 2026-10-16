import FsFltz.Analysis.TailoringCriticalHolomorphic
import FsFltz.Analysis.FacePotentialMinima

/-!
# Full active-face support at normalized critical conormal limits

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1454–1457.
The actual retained coefficients, positions, and conormals converge along
the proved compact subsequences. The resulting support is exactly every
active polar facet, not a face classification supplied as a hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- Actual normalized approximate-critical subsequences have precisely the
full active polar face as support, with positive real limiting coefficients.
The face and signs are conclusions of the fiber and conormal equations. -/
theorem tailoring_normalized_critical_limit_active_face
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (hβ : Tendsto β atTop atTop)
    (B : ℝ) (hB : ∀ᶠ j in atTop, tailoringMaxWeight I (β j) (y j).1 ≤ B)
    (hy : ∀ᶠ j in atTop, tailoringFamily I (β j) 1 (y j) = 1)
    (hzero : ∀ᶠ j in atTop, tailoringCutoff I (β j) 0 (y j).1 = 1)
    (x : RealSpace n) (hx₀ : x ≠ 0)
    (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (q : Lattice n → ℂ)
    (hq : ∀ v ∈ I.vertices, Tendsto (fun j => tailoringRetainedMonomial I (β j) v (y j))
      atTop (𝓝 (q v)))
    (t : ℕ → ℂ) (τ : ℂ)
    (ht : Tendsto (fun j => ((β j)⁻¹ : ℂ) * t j) atTop (𝓝 τ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ᶠ j in atTop,
      ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤
          δ j * ‖coordinateGradient φ (y j).1‖) :
    x ∈ polarPolytope I ∧ supportHeight I x = 1 ∧
      (∀ v ∈ I.vertices, q v ≠ 0 ↔ pairing v x = 1) ∧
      (∑ v ∈ I.vertices, q v = 1) ∧
      (fun k => (coordinateGradient φ x k : ℂ)) =
        τ • ∑ v ∈ I.vertices, q v • latticeComplex v ∧
      τ.im = 0 ∧ 0 < τ.re ∧ ∀ a ∈ I.vertices, pairing a x = 1 →
        (q a).im = 0 ∧ 0 < (q a).re := by
  classical
  have hxP : x ∈ polarPolytope I := (mem_polarPolytope_iff I x).mpr
    (fun v hv => pairing_limit_le_one_of_bounded_tailoringMaxWeight I v hv β
      (fun j => (y j).1) hβ B hB x hx)
  have hsum := sum_retained_limits_eq_one I β y hy hzero q hq
  have hex : ∃ a ∈ I.vertices, q a ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : ∑ a ∈ I.vertices, q a = 0 :=
      Finset.sum_eq_zero (fun a ha => hn a ha)
    exact zero_ne_one (hz.symm.trans hsum)
  obtain ⟨a, ha, hqa⟩ := hex
  have hax := pairing_eq_one_of_retained_limit_ne_zero I a ha β y hβ B hB x hx
    (q a) (hq a ha) hqa
  have hlevel := supportHeight_eq_one_of_mem_polarFacet I ha ⟨hxP, hax⟩
  have hqoff : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0 := by
    intro v hv hvlt
    exact tendsto_nhds_unique (hq v hv)
      (tailoringRetainedMonomial_tendsto_zero_of_pairing_limit_lt_one I v hv β y hβ x hx hvlt)
  have hp := tailoring_conormal_equation_of_normalized_limits hφ β y hβ
    x hx₀ hx q hq t τ ht δ hδ herr
  refine ⟨hxP, hlevel, ?_, hsum, hp,
    hφ.active_complex_conormal_positive hxP hlevel q τ hqoff hsum hp⟩
  intro v hv
  exact ⟨pairing_eq_one_of_retained_limit_ne_zero I v hv β y hβ B hB x hx
    (q v) (hq v hv), hφ.active_complex_conormal_coefficient_ne_zero
      hxP hlevel q τ hqoff hp hv⟩

/-- Once the actual coefficients have a full active-face limit, the
actual finite retained support is eventually exactly that face. -/
theorem eventually_retained_support_eq_maximizingVertexFace_of_normalized_limit
    (I : ToricInput n) (β : ℕ → ℝ) (y : ℕ → LGSpace n)
    (hβ : Tendsto β atTop atTop)
    (x : RealSpace n) (hxP : x ∈ polarPolytope I)
    (hx : Tendsto (fun j => (β j)⁻¹ • (y j).1) atTop (𝓝 x))
    (hlevel : supportHeight I x = 1) (q : Lattice n → ℂ)
    (hq : ∀ v ∈ I.vertices, Tendsto (fun j => tailoringRetainedMonomial I (β j) v (y j))
      atTop (𝓝 (q v)))
    (hactive : ∀ v ∈ I.vertices, q v ≠ 0 ↔ pairing v x = 1) :
    ∀ᶠ j in atTop, tailoringRetainedVertices I (β j) (y j).1 = maximizingVertexFace I x := by
  classical
  have hvertex (v : Lattice n) (hv : v ∈ I.vertices) :
      ∀ᶠ j in atTop, v ∈ tailoringRetainedVertices I (β j) (y j).1 ↔
        v ∈ maximizingVertexFace I x := by
    by_cases ha : pairing v x = 1
    · have hqne := (hactive v hv).mpr ha
      filter_upwards [(hq v hv).eventually_ne hqne] with j hj
      refine ⟨fun _ => (mem_maximizingVertexFace I x v).mpr ⟨hv, ha.trans hlevel.symm⟩, ?_⟩
      intro _
      by_contra hn
      exact hj (tailoringRetainedMonomial_eq_zero_of_not_mem_support I (β j) (y j)
        (Finset.Subset.refl _) hv hn)
    · have hlt : pairing v x < 1 := lt_of_le_of_ne
        ((mem_polarPolytope_iff I x).mp hxP v hv) ha
      have hinv := tendsto_inv_atTop_zero.comp hβ
      have hsqrt : Tendsto (fun j => Real.sqrt (β j) / β j) atTop (𝓝 0) := by
        simpa only [Real.sqrt_div_self, Function.comp_def] using
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hβ)
      have hlow : Tendsto (fun j => pairing v ((β j)⁻¹ • (y j).1) +
          Real.sqrt (β j) / β j + 2 * (β j)⁻¹) atTop (𝓝 (pairing v x)) := by
        simpa using ((pairing_normalized_tendsto v β (fun j => (y j).1) x hx).add hsqrt).add
          ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
      filter_upwards [hlow.eventually_lt_const hlt,
        hβ.eventually (eventually_gt_atTop 0)] with j hj hpos
      have hn : v ∉ tailoringRetainedVertices I (β j) (y j).1 := by
        intro hret
        have hw := tailoringCutoff_retained_deficit I (β j) v (y j).1
          ((mem_tailoringRetainedVertices_iff I (β j) (y j).1 v).mp hret).2
        have hm : 0 ≤ tailoringMaxWeight I (β j) (y j).1 := le_max_left _ _
        rw [tailoringWeight_vertex I (β j) ⟨v, hv⟩] at hw
        have hb := mul_le_mul_of_nonneg_left (show -Real.sqrt (β j) - 2 ≤
            pairing v (y j).1 - β j by linarith) (inv_pos.mpr hpos).le
        rw [pairing_smul_real, div_eq_mul_inv] at hj
        have hc : (β j)⁻¹ * β j = 1 := inv_mul_cancel₀ hpos.ne'
        nlinarith
      have hnA : v ∉ maximizingVertexFace I x := by
        intro hvA
        exact ha (((mem_maximizingVertexFace I x v).mp hvA).2.trans hlevel)
      simp [hn, hnA]
  have hall : ∀ᶠ j in atTop, ∀ v ∈ I.vertices,
      v ∈ tailoringRetainedVertices I (β j) (y j).1 ↔ v ∈ maximizingVertexFace I x :=
    (I.vertices.eventually_all).mpr hvertex
  filter_upwards [hall] with j hj
  ext v
  by_cases hv : v ∈ I.vertices
  · exact hj v hv
  · exact ⟨fun hr => (hv (tailoringRetainedVertices_subset I (β j) (y j).1 hr)).elim,
      fun hA => (hv ((mem_maximizingVertexFace I x v).mp hA).1).elim⟩

/-- The limiting complex conormal equation gives a literal minimum on
the active polar face. Taking real parts produces its stationary normals. -/
theorem isMinOn_active_polarFace_of_complex_conormal
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 ≤ c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {x : RealSpace n} (hxP : x ∈ polarPolytope I)
    (hlevel : supportHeight I x = 1) (q : Lattice n → ℂ) (τ : ℂ)
    (hqoff : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0)
    (hp : (fun k => (coordinateGradient φ x k : ℂ)) =
      τ • ∑ v ∈ I.vertices, q v • latticeComplex v) :
    IsMinOn φ (polarFace I (maximizingVertexFace I x)) x := by
  classical
  have hreal : coordinateGradient φ x =
      ∑ v ∈ I.vertices, (τ * q v).re • latticeReal v := by
    ext k
    have hk := congrArg (fun z : Fin n → ℂ => (z k).re) hp
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_re, sub_mul, mul_assoc,
      Finset.sum_sub_distrib] using hk
  have hnormal : coordinateGradient φ x =
      ∑ v ∈ maximizingVertexFace I x, (τ * q v).re • latticeReal v := by
    rw [hreal]
    symm
    apply Finset.sum_subset (I.maximizingVertexFace_isPolytopeFace x).1.1
    intro v hv hvA
    have hvlt : pairing v x < 1 := lt_of_le_of_ne
      ((mem_polarPolytope_iff I x).mp hxP v hv)
      (fun he => hvA ((mem_maximizingVertexFace I x v).mpr ⟨hv, he.trans hlevel.symm⟩))
    simp [hqoff v hv hvlt]
  apply isMinOn_polarFace_of_convex_quadratic_normal I hφ1 hc hconv _ hnormal
  exact ⟨hxP, fun v hv => ((mem_maximizingVertexFace I x v).mp hv).2.trans hlevel⟩

/-- Every actual endpoint sequence with vanishing relative critical
conormal errors has a subsequence converging to the unique minimum of
its eventual retained face, with positive real normalized coefficients. -/
theorem tailoringEndpoint_extract_positive_face_minimum_limit
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {a : ℝ} (ha : 0 < a) (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u)
    (β : ℕ → ℝ) (y : ℕ → LGSpace n) (t : ℕ → ℂ) (ε : ℕ → ℝ)
    (hβ : Tendsto β atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hy : ∀ᶠ j in atTop, tailoringFamily I (β j) 1 (y j) = 1)
    (he : ∀ᶠ j in atTop,
      ‖(fun k => (coordinateGradient φ (y j).1 k : ℂ)) -
        t j • tailoringRetainedNormal I (β j) (y j)‖ ≤
          ε j * ‖coordinateGradient φ (y j).1‖) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ s : Finset (Lattice n),
      IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices ∧
      ∃ x ∈ polarFace I s, IsMinOn φ (polarFace I s) x ∧
        (∀ z ∈ polarFace I s, IsMinOn φ (polarFace I s) z → z = x) ∧
        ∃ q : Lattice n → ℂ, ∃ τ : ℂ,
          Tendsto (fun j => (β (ρ j))⁻¹ • (y (ρ j)).1) atTop (𝓝 x) ∧
          (∀ v ∈ I.vertices, Tendsto
            (fun j => tailoringRetainedMonomial I (β (ρ j)) v (y (ρ j))) atTop (𝓝 (q v))) ∧
          Tendsto (fun j => t (ρ j) / (β (ρ j) : ℂ)) atTop (𝓝 τ) ∧
          (∀ᶠ j in atTop, tailoringRetainedVertices I (β (ρ j)) (y (ρ j)).1 = s) ∧
          (∑ v ∈ I.vertices, q v = 1) ∧ τ.im = 0 ∧ 0 < τ.re ∧
          (∀ v ∈ s, (q v).im = 0 ∧ 0 < (q v).re) ∧
          (fun k => (coordinateGradient φ x k : ℂ)) =
            τ • ∑ v ∈ I.vertices, q v • latticeComplex v := by
  classical
  obtain ⟨⟨B, hB⟩, hzero, ρ, hρ, x, hx₀, q, τ, hx, hq, ht⟩ :=
    tailoringEndpoint_extract_small_conormal_subsequence I hφ ha hlower β y t ε hβ hε hy he
  have ht' : Tendsto (fun j => ((β (ρ j))⁻¹ : ℂ) * t (ρ j)) atTop (𝓝 τ) := by
    simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using ht
  have hβ' := hβ.comp hρ.tendsto_atTop
  obtain ⟨hxP, hlevel, hactive, hsum, hp, hτim, hτpos, hqpos⟩ :=
    tailoring_normalized_critical_limit_active_face hφ (β ∘ ρ) (y ∘ ρ) hβ' B
      (hρ.tendsto_atTop.eventually hB) (hρ.tendsto_atTop.eventually hy)
      (hρ.tendsto_atTop.eventually hzero) x hx₀ hx q hq (t ∘ ρ) τ ht' (ε ∘ ρ)
      (hε.comp hρ.tendsto_atTop) (hρ.tendsto_atTop.eventually he)
  let s := maximizingVertexFace I x
  obtain ⟨hs, hsne⟩ := I.maximizingVertexFace_isPolytopeFace x
  have hsproper := I.maximizingVertexFace_ne_vertices hx₀
  have hxF : x ∈ polarFace I s :=
    ⟨hxP, fun v hv => ((mem_maximizingVertexFace I x v).mp hv).2.trans hlevel⟩
  have hqoff : ∀ v ∈ I.vertices, pairing v x < 1 → q v = 0 := by
    intro v hv hvlt
    by_contra hne
    exact hvlt.ne ((hactive v hv).mp hne)
  have hmin := isMinOn_active_polarFace_of_complex_conormal I hφ1 hc.le hconv
    hxP hlevel q τ hqoff hp
  refine ⟨ρ, hρ, s, hs, hsne, hsproper, x, hxF, hmin,
    fun z hz hmz => hφ.eq_of_polarFace_minima hφ1 hc hconv hs hsne hsproper hz hxF hmz hmin,
    q, τ, hx, hq, ht, ?_, hsum, hτim, hτpos, ?_, hp⟩
  · exact eventually_retained_support_eq_maximizingVertexFace_of_normalized_limit I
      (β ∘ ρ) (y ∘ ρ) hβ' x hxP hx hlevel q hq hactive
  · intro v hv
    have hv' := (mem_maximizingVertexFace I x v).mp hv
    exact hqpos v hv'.1 (hv'.2.trans hlevel)

end FsFltz
