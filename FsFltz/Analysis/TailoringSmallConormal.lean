import FsFltz.Analysis.TailoringSmallConormalRadial

/-!
# Small retained conormal distance localizes the full tailored fiber

Source: `geometric-part-fsf-proof.tex`, `lem:smallzeta`, lines 1367–1391.
The small-error hypothesis refers to the actual homogeneous gradient and
the actual retained normal. All localization constants are constructed
uniformly from the finite toric input and the constructed potential.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators Topology ContDiff

variable {n : ℕ}

/-- The whole endpoint fiber has a linear native radius lower bound, and
its retained deficit is uniformly small relative to that radius. -/
theorem tailoringEndpoint_exists_small_relative_deficit (I : ToricInput n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
        y.1 ≠ 0 ∧ d * β ≤ ‖y.1‖ ∧ Real.sqrt β + 2 ≤ ε * ‖y.1‖ := by
  let H := (supportHeightLipschitzConstant I : ℝ)
  have hH : 0 < H := supportHeightLipschitzConstant_pos I
  obtain ⟨B, hB, hdeficit⟩ := exists_tailoringDeficit_threshold H ε hH hε
  let L := Real.log (I.vertices.card : ℝ)
  let B' := max B (max (L ^ 2) 16)
  refine ⟨1 / (2 * H), by positivity, B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy
  have hβpos : 0 < β := hB.trans_le ((le_max_left _ _).trans hβ)
  have hLβ : L ^ 2 ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hL : L ≤ Real.sqrt β := by
    have hs := Real.sqrt_le_sqrt hLβ
    rw [Real.sqrt_sq_eq_abs] at hs
    exact (le_abs_self L).trans hs
  obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
  have hχ := tailoringEndpoint_maximizing_cutoff_eq_one I β y hy hL v hv
  have hret : v.val ∈ tailoringRetainedVertices I β y.1 :=
    (mem_tailoringRetainedVertices_iff I β y.1 v.val).mpr ⟨v.property, by rw [hχ]; norm_num⟩
  have hpair := (tailoringRetainedVertex_estimates I β y.1 v.val hret).2
  have hh : supportHeight I y.1 ≤ H * ‖y.1‖ := by
    simpa only [I.supportHeight_zero, sub_zero] using I.supportHeight_sub_le y.1 0
  have hrad : β - Real.sqrt β - 2 < H * ‖y.1‖ :=
    hpair.trans_le ((I.pairing_le_supportHeight y.1 v).trans hh)
  obtain ⟨hlarge, hsmall⟩ := hdeficit β ((le_max_left _ _).trans hβ)
  have hne : y.1 ≠ 0 := by intro he; simp [he] at hrad; linarith
  have h16 : (16 : ℝ) ≤ β :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hs := Real.sq_sqrt hβpos.le
  have hs0 := Real.sqrt_nonneg β
  have hhalf : β / 2 ≤ β - Real.sqrt β - 2 := by
    have : 4 ≤ Real.sqrt β := by nlinarith
    nlinarith
  refine ⟨hne, ?_, ?_⟩
  · have : β ≤ ‖y.1‖ * (2 * H) := by linarith
    simpa only [div_mul_eq_mul_div, one_mul] using (div_le_iff₀ (mul_pos (by norm_num) hH)).mpr this
  · apply (mul_le_mul_iff_right₀ hH).mp
    calc
      H * (Real.sqrt β + 2) ≤ ε * (β - Real.sqrt β - 2) := hsmall
      _ ≤ ε * (H * ‖y.1‖) := mul_le_mul_of_nonneg_left hrad.le hε.le
      _ = H * (ε * ‖y.1‖) := by ring

private theorem complexRadialPairing_gradient (φ : RealSpace n → ℝ) (u : RealSpace n) :
    complexRadialPairing u (fun j => (coordinateGradient φ u j : ℂ)) =
      (fderiv ℝ φ u u : ℂ) := by
  rw [fderiv_apply_eq_coordinateGradient_pairing]
  simp only [complexRadialPairing, Complex.ofReal_sum, Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private theorem complexRadialPairing_split (u : RealSpace n) (p : Fin n → ℂ)
    (g : Fin n → ℂ) (t : ℂ) :
    complexRadialPairing u p = t * complexRadialPairing u g +
      complexRadialPairing u (p - t • g) := by
  simp only [complexRadialPairing, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have he : (∑ j : Fin n, (u j : ℂ) * (t * g j)) =
      ∑ j : Fin n, t * ((u j : ℂ) * g j) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [he]
  ring

/-- The central quantitative estimate: small complex-line error forces a
uniform upper bound on the maximum monomial of the actual endpoint fiber. -/
theorem tailoringEndpoint_exists_small_conormal_max_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ t : ℂ, ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
        t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖) →
      Real.exp (supportHeight I y.1 - β) ≤ M₀ := by
  obtain ⟨k, hk, hangle⟩ := hφ.exists_coordinateGradient_radial_angle ha hlower
  obtain ⟨c, hc, B, hB, hnormal⟩ := tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  let N := (I.vertices.card : ℝ)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast I.vertices_nonempty.card_pos
  let H := (supportHeightLipschitzConstant I : ℝ)
  have hH : 0 < H := supportHeightLipschitzConstant_pos I
  let δ := min 1 (k / (4 * (n + 1)))
  let ε := k * c / (8 * N)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hε : 0 < ε := by positivity
  obtain ⟨d, hd, B', hB', hdeficit⟩ := tailoringEndpoint_exists_small_relative_deficit I hε
  refine ⟨δ, hδ, 4 * H / (c * k), by positivity,
    max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy ht
  obtain ⟨t, ht⟩ := ht
  let u := y.1
  let p := coordinateGradient φ u
  let pc : Fin n → ℂ := fun j => (p j : ℂ)
  let G := tailoringRetainedNormal I β y
  let M := Real.exp (supportHeight I u - β)
  let r := ‖u‖
  let P := ‖p‖
  obtain ⟨hu, _, hsmall⟩ := hdeficit β ((le_max_right _ _).trans hβ) y hy
  have hr : 0 < r := norm_pos_iff.mpr hu
  obtain ⟨hp, hradial⟩ := hangle u hu
  have hP : 0 < P := norm_pos_iff.mpr hp
  have hM : 0 < M := Real.exp_pos _
  have hG : c * M ≤ ‖G‖ := hnormal β ((le_max_left _ _).trans hβ) y hy
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have htG : ‖t‖ * ‖G‖ ≤ 2 * P := by
    have htri := norm_le_insert pc (t • G)
    rw [norm_smul, norm_coordinateComplexification] at htri
    have herr : ‖pc - t • G‖ ≤ δ * P := ht
    have hδP := mul_le_mul_of_nonneg_right hδ1 hP.le
    linarith
  have htM : ‖t‖ * M ≤ 2 * P / c := by
    apply (le_div_iff₀ hc).mpr
    have hm := mul_le_mul_of_nonneg_left hG (norm_nonneg t)
    nlinarith only [hm, htG]
  have hh : supportHeight I u ≤ H * r := by
    simpa only [I.supportHeight_zero, sub_zero] using I.supportHeight_sub_le u 0
  have hradG : ‖complexRadialPairing u G‖ ≤ H * r + N * ε * r * M := by
    apply (tailoringEndpoint_retainedNormal_radial_bound I β y hy).trans
    have hhχ : supportHeight I u * tailoringCutoff I β 0 u ≤ H * r :=
      (mul_le_mul_of_nonneg_left (tailoringCutoff_le_one I β 0 u)
        (by obtain ⟨b, hb, _, _, hh'⟩ := I.exists_supportHeight_linear_bounds
            exact (mul_nonneg hb.le (Real.sqrt_nonneg _)).trans (hh' u).1)).trans
          (by simpa using hh)
    have hΔ := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ N * M by positivity)
    dsimp [N, M, u, r] at hΔ ⊢
    nlinarith only [hhχ, hΔ]
  have hfdpos : 0 < fderiv ℝ φ u u :=
    (mul_pos (mul_pos hk hP) hr).trans_le hradial
  have hcontract : k * P * r ≤ ‖t‖ * (H * r + N * ε * r * M) + n * r * (δ * P) := by
    calc
      _ ≤ fderiv ℝ φ u u := hradial
      _ = ‖complexRadialPairing u pc‖ := by
        rw [complexRadialPairing_gradient, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hfdpos]
      _ ≤ ‖t‖ * ‖complexRadialPairing u G‖ + ‖complexRadialPairing u (pc - t • G)‖ := by
        rw [complexRadialPairing_split u pc G t]
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ ‖t‖ * (H * r + N * ε * r * M) + n * r * (δ * P) :=
        add_le_add (mul_le_mul_of_nonneg_left hradG (norm_nonneg t))
          ((norm_complexRadialPairing_le u (pc - t • G)).trans
            (mul_le_mul_of_nonneg_left ht (by positivity)))
  have hnδ : (n : ℝ) * δ ≤ k / 4 := by
    have hd' : δ ≤ k / (4 * (n + 1)) := min_le_right _ _
    have hdiv : δ * (4 * (n + 1)) ≤ k := (le_div_iff₀ (by positivity)).mp hd'
    nlinarith [hδ.le]
  have hεeq : N * ε = k * c / 8 := by dsimp [ε]; field_simp
  have hmain : (k / 2) * P * r * M ≤ (2 * H / c) * P * r := by
    have h1 := mul_le_mul_of_nonneg_right hcontract hM.le
    have h2 := mul_le_mul_of_nonneg_right htM (show 0 ≤ H * r by positivity)
    have h3 := mul_le_mul_of_nonneg_right htM (show 0 ≤ N * ε * r * M by positivity)
    have h4 := mul_le_mul_of_nonneg_right hnδ (show 0 ≤ r * P * M by positivity)
    rw [hεeq] at h1
    rw [hεeq] at h3
    have heq : (2 * P / c) * (k * c / 8 * r * M) = k / 4 * P * r * M := by field_simp; ring
    rw [heq] at h3
    linear_combination h1 + h2 + h3 + h4
  change M ≤ 4 * H / (c * k)
  apply (le_div_iff₀ (mul_pos hc hk)).mpr
  have hmain' : M * (c * k) * (P * r) ≤ 4 * H * (P * r) := by
    have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 * c by positivity)
    have heq : (2 * c) * (2 * H / c * P * r) = 4 * H * (P * r) := by field_simp; ring
    rw [heq] at hm
    nlinarith only [hm]
  exact (mul_le_mul_iff_right₀ (mul_pos hP hr)).mp
    (by simpa only [mul_comm] using hmain')

private theorem native_norm_le_euclidean_radius (u : RealSpace n) :
    ‖u‖ ≤ Real.sqrt (realSquaredNorm u) := by
  have he : Real.sqrt (realSquaredNorm u) =
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [realSquaredNorm, Real.norm_eq_abs]
  rw [he]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin n) ℝ).symm u) j

/-- Full quantitative small-conormal localization. Its hypothesis is the
literal error to the actual retained complex line, and its conclusions
include the exactly uncut constant and a uniform radial annulus. -/
theorem tailoringEndpoint_exists_small_conormal_localization
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∃ d : ℝ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ t : ℂ, ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
        t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖) →
      1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) ∧
      Real.exp (supportHeight I y.1 - β) ≤ M₀ ∧
      tailoringCutoff I β 0 y.1 = 1 ∧
      |supportHeight I y.1 - β| ≤ C ∧
      d * β ≤ ‖y.1‖ ∧ ‖y.1‖ ≤ D * β := by
  obtain ⟨δ, hδ, M₀, hM₀, B, hB, hmax⟩ :=
    tailoringEndpoint_exists_small_conormal_max_bound I hφ ha hlower
  obtain ⟨d, hd, B', hB', hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨c, hc, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  let M' := max M₀ 1
  have hM' : 0 < M' := zero_lt_one.trans_le (le_max_right _ _)
  let L := Real.log (1 / (I.vertices.card : ℝ))
  let U := Real.log M'
  let C := 1 + |L| + |U|
  have hC : 0 < C := by dsimp [C]; positivity
  let D := (1 + C) / c
  have hD : 0 < D := by dsimp [D]; positivity
  let B'' := max (max B B') (max 1 (U ^ 2))
  refine ⟨δ, hδ, M', hM', C, hC, d, hd, D, hD,
    B'', hB.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro β hβ y hy ht
  have hBβ : B ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have hB'β : B' ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have h1β : (1 : ℝ) ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hUβ : U ^ 2 ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hU : U ≤ Real.sqrt β := by
    have hs := Real.sqrt_le_sqrt hUβ
    rw [Real.sqrt_sq_eq_abs] at hs
    exact (le_abs_self U).trans hs
  have hMlower := tailoringEndpoint_max_monomial_lower I β y hy
  have hMupper : Real.exp (supportHeight I y.1 - β) ≤ M' :=
    (hmax β hBβ y hy ht).trans (le_max_left _ _)
  have hN : 0 < (I.vertices.card : ℝ) := by exact_mod_cast I.vertices_nonempty.card_pos
  have hloglower : L ≤ supportHeight I y.1 - β :=
    (Real.log_le_iff_le_exp (by positivity)).mpr hMlower
  have hlogupper : supportHeight I y.1 - β ≤ U := by
    apply Real.exp_le_exp.mp
    exact hMupper.trans_eq (Real.exp_log hM').symm
  have hχ : tailoringCutoff I β 0 y.1 = 1 := by
    apply tailoringCutoff_eq_one_of_gap
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp only [tailoringWeight_zero]
      simpa only [zero_sub] using neg_nonpos.mpr (Real.sqrt_nonneg β)
    rw [tailoringWeight_vertex I β ⟨v, hv⟩, tailoringWeight_zero]
    have hp := I.pairing_le_supportHeight y.1 ⟨v, hv⟩
    linarith
  have herror : |supportHeight I y.1 - β| ≤ C := by
    apply abs_le.mpr
    have hL := neg_abs_le L
    have hU' := le_abs_self U
    dsimp [C]
    constructor <;> linarith [abs_nonneg L, abs_nonneg U]
  obtain ⟨_, hlow, _⟩ := hrad β hB'β y hy
  refine ⟨hMlower, hMupper, hχ, herror, hlow, ?_⟩
  have hnative : c * ‖y.1‖ ≤ supportHeight I y.1 :=
    (mul_le_mul_of_nonneg_left (native_norm_le_euclidean_radius y.1) hc.le).trans
      (hheight y.1).1
  have hhupper : supportHeight I y.1 ≤ (1 + C) * β := by
    have herr := (abs_le.mp herror).2
    have hCb := mul_le_mul_of_nonneg_left h1β hC.le
    linarith
  have hbound : ‖y.1‖ ≤ (1 + C) * β / c := (le_div_iff₀ hc).mpr (by linarith)
  simpa only [D, div_mul_eq_mul_div, mul_div_assoc] using hbound

/-- The finite original toric input constructs a strongly compatible
potential together with the complete small-conormal localization package. -/
theorem ToricInput.exists_stronglyCompatibleEndPotential_with_smallConormal_localization
    (I : ToricInput n) :
    ∃ φ : RealSpace n → ℝ, IsStronglyCompatibleEndPotential I φ ∧
      ContDiff ℝ 1 φ ∧ φ 0 = 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∃ d : ℝ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      (∃ t : ℂ, ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
        t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖) →
      1 / (I.vertices.card : ℝ) ≤ Real.exp (supportHeight I y.1 - β) ∧
      Real.exp (supportHeight I y.1 - β) ≤ M₀ ∧
      tailoringCutoff I β 0 y.1 = 1 ∧
      |supportHeight I y.1 - β| ≤ C ∧
      d * β ≤ ‖y.1‖ ∧ ‖y.1‖ ≤ D * β := by
  obtain ⟨φ, hφ, hφ1, hφ0, a, ha, _, hpos, _⟩ := I.exists_stronglyCompatibleEndPotential
  refine ⟨φ, hφ, hφ1, hφ0, tailoringEndpoint_exists_small_conormal_localization I hφ ha ?_⟩
  intro u
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hn : ‖u‖ ≤ ‖e.symm u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact PiLp.norm_apply_le (e.symm u) j
  have hsq : ‖u‖ ^ 2 ≤ ‖e.symm u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact (mul_le_mul_of_nonneg_left hsq ha.le).trans
    (by simpa only [e, ContinuousLinearEquiv.apply_symm_apply] using hpos (e.symm u))

/-- Every sufficiently accurate retained-line approximant has a uniformly
bounded normalized scalar. This supplies the compactness of `t / β` used
in the bad-region subsequence argument. -/
theorem tailoringEndpoint_exists_approximant_linear_bound
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ φ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℝ, 0 < T ∧ ∃ B : ℝ, 0 < B ∧
      ∀ β ≥ B, ∀ y : LGSpace n, tailoringFamily I β 1 y = 1 →
      ∀ t : ℂ, ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
        t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖ →
      ‖t‖ ≤ T * β := by
  obtain ⟨δ, hδ, _, _, _, _, _, _, D, hD, B, hB, hloc⟩ :=
    tailoringEndpoint_exists_small_conormal_localization I hφ ha hlower
  obtain ⟨P, hP, hgrad⟩ := hφ.exists_coordinateGradient_upper
  obtain ⟨c, hc, B', hB', hnormal⟩ :=
    tailoringEndpoint_exists_uniform_retainedNormal_lower_bound I
  obtain ⟨_, _, B'', hB'', hrad⟩ :=
    tailoringEndpoint_exists_small_relative_deficit I (show (0 : ℝ) < 1 by norm_num)
  let N := (I.vertices.card : ℝ)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast I.vertices_nonempty.card_pos
  refine ⟨min δ 1, lt_min hδ zero_lt_one, 2 * P * D * N / c, by positivity,
    max B (max B' B''), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy t ht
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβB' : B' ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβB'' : B'' ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have herror : ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
      t • tailoringRetainedNormal I β y‖ ≤ δ * ‖coordinateGradient φ y.1‖ :=
    ht.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  obtain ⟨hM, _, _, _, _, huupper⟩ := hloc β hβB y hy ⟨t, herror⟩
  have hu := (hrad β hβB'' y hy).1
  have hgrad' : ‖coordinateGradient φ y.1‖ ≤ P * D * β :=
    (hgrad y.1 hu).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left huupper hP.le)
  have hG : c / N ≤ ‖tailoringRetainedNormal I β y‖ := by
    have hb := hnormal β hβB' y hy
    have hl : c / N ≤ c * Real.exp (supportHeight I y.1 - β) := by
      simpa only [N, mul_one_div] using mul_le_mul_of_nonneg_left hM hc.le
    exact hl.trans hb
  have htri := norm_le_insert (fun j => (coordinateGradient φ y.1 j : ℂ))
    (t • tailoringRetainedNormal I β y)
  rw [norm_smul, norm_coordinateComplexification] at htri
  have herror' : ‖(fun j => (coordinateGradient φ y.1 j : ℂ)) -
      t • tailoringRetainedNormal I β y‖ ≤ ‖coordinateGradient φ y.1‖ :=
    ht.trans (by simpa using
      mul_le_mul_of_nonneg_right (min_le_right δ 1) (norm_nonneg (coordinateGradient φ y.1)))
  have htG : ‖t‖ * (c / N) ≤ 2 * P * D * β := by
    have hb := mul_le_mul_of_nonneg_left hG (norm_nonneg t)
    linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  have hm := mul_le_mul_of_nonneg_right htG hN.le
  have he : (‖t‖ * (c / N)) * N = ‖t‖ * c := by field_simp
  rw [he] at hm
  simpa only [div_mul_eq_mul_div, mul_assoc, mul_comm, mul_left_comm] using hm

end FsFltz
