import FsFltz.Analysis.OriginalAmbientMargin
import FsFltz.Geometry.AdmissibilityBridge

/-!
# Linear growth of the original ambient Liouville field

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 799–818.
The explicit inverse formula, native dominant-face bound and Cauchy–Schwarz
give linear growth on the end. Finite coefficients bound the compact radial
remainder, including critical points. The existing quotient tangent bridge
identifies this formula with the actual field of `lambdaKForm`.
Both-time ODE continuation and completion markings remain separate results.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-- Finite support bounds the native superpotential by cardinality times the
actual maximal monomial magnitude. -/
theorem norm_W_le_card_mul_maxMonomialMagnitude (I : ToricInput n) (y : LGSpace n) :
    ‖W I y‖ ≤ (I.vertices.card : ℝ) * maxMonomialMagnitude I y := by
  calc
    ‖W I y‖ ≤ ∑ v : {v : Lattice n // v ∈ I.vertices},
        ‖monomial (I.coeff v) v.val y‖ := norm_sum_le _ _
    _ ≤ ∑ _v : {v : Lattice n // v ∈ I.vertices}, maxMonomialMagnitude I y :=
      Finset.sum_le_sum (fun v _ => I.norm_monomial_le_maxMonomialMagnitude y v)
    _ = _ := by simp

/-- Coefficient mass and support height give an explicit angle-uniform
bound on the superpotential, used on the compact radial remainder. -/
theorem norm_W_le_coeff_sum_mul_exp_supportHeight (I : ToricInput n) (y : LGSpace n) :
    ‖W I y‖ ≤ (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) *
      Real.exp (supportHeight I y.1) := by
  calc
    ‖W I y‖ ≤ ∑ v : {v : Lattice n // v ∈ I.vertices},
        ‖monomial (I.coeff v) v.val y‖ := norm_sum_le _ _
    _ ≤ ∑ v : {v : Lattice n // v ∈ I.vertices},
        ‖I.coeff v‖ * Real.exp (supportHeight I y.1) := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_monomial]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (I.pairing_le_supportHeight y.1 v)) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

private theorem inverse_gain_bounds {K a : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) :
    0 ≤ K / (1 + K * a) ∧
      K / (1 + K * a) * a ≤ 1 ∧
      K / (1 + K * a) * Real.sqrt a ≤ K + 1 := by
  have hd : 0 < 1 + K * a := by positivity
  refine ⟨div_nonneg hK hd.le, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    linarith
  · have hsqrt : Real.sqrt a ≤ 1 + a := by
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]
    have hmul := mul_le_mul_of_nonneg_left hsqrt hK
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg K) ha]

private theorem norm_coordinates_le_complex (q : TangentCoordinates n) :
    ‖q‖ ≤ ‖tangentComplexCoordinates q‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    have hj : ‖q.1 j‖ ≤ ‖tangentComplexCoordinates q j‖ := by
      simpa [tangentComplexCoordinates, Real.norm_eq_abs] using
        Complex.abs_re_le_norm (tangentComplexCoordinates q j)
    exact hj.trans (norm_le_pi_norm _ j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    have hj : ‖q.2 j‖ ≤ ‖tangentComplexCoordinates q j‖ := by
      simpa [tangentComplexCoordinates, Real.norm_eq_abs] using
        Complex.abs_im_le_norm (tangentComplexCoordinates q j)
    exact hj.trans (norm_le_pi_norm _ j)

private theorem abs_coordinate_le_radius (u : RealSpace n) (j : Fin n) :
    |u j| ≤ Real.sqrt (realSquaredNorm u) := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (u k)) (Finset.mem_univ j)

/-- A direct global estimate for the literal inverse-system solution.
Its derivative-dependent gain remains finite at critical points. -/
theorem norm_liouvilleCoordinates_le_inverse_gain (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : LGSpace n) :
    ‖liouvilleCoordinates I K y‖ ≤ 2 * Real.sqrt (realSquaredNorm y.1) +
      K / (1 + K * a I y) * Real.sqrt (a I y) * ‖W I y‖ / 2 := by
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a I y)
  let q := K / (1 + K * a I y)
  obtain ⟨hq, hqa, _⟩ := inverse_gain_bounds hK (a_nonneg I y)
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = a I y := Real.sq_sqrt (a_nonneg I y)
  have hF : ‖W I y / 2 - b0 I y‖ ≤ ‖W I y‖ / 2 + r * g := by
    calc
      ‖W I y / 2 - b0 I y‖ ≤ ‖W I y / 2‖ + ‖b0 I y‖ := norm_sub_le _ _
      _ ≤ ‖W I y‖ / 2 + r * g := by
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num]
        exact add_le_add le_rfl (norm_b0_le_euclidean_radius_mul_sqrt_a I y)
  apply (norm_coordinates_le_complex _).trans
  rw [tangentComplexCoordinates_liouville]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hGj : ‖G I y j‖ ≤ g :=
    (norm_le_pi_norm (G I y) j).trans (norm_G_le_sqrt_a I y)
  calc
    ‖CoordinateGeometry.liouville (G I y) (radialComplexCoordinates y) (W I y) K j‖ ≤
        |y.1 j| + q * ‖G I y j‖ * ‖W I y / 2 - b0 I y‖ := by
      simp only [CoordinateGeometry.liouville, evaluation_radialComplexCoordinates]
      change ‖(y.1 j : ℂ) + (q : ℂ) * conj (G I y j) * (W I y / 2 - b0 I y)‖ ≤ _
      have hq' : 0 ≤ q := hq
      simpa only [radialComplexCoordinates,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq', Complex.norm_conj]
        using norm_add_le (radialComplexCoordinates y j)
          ((q : ℝ) * conj (G I y j) * (W I y / 2 - b0 I y))
    _ ≤ r + q * g * (‖W I y‖ / 2 + r * g) := by
      apply add_le_add (abs_coordinate_le_radius y.1 j)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hGj hq) hF (norm_nonneg _)
        (mul_nonneg hq hg)
    _ ≤ 2 * r + q * g * ‖W I y‖ / 2 := by
      have hqr : r * (q * a I y) ≤ r := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hqa hr
      calc
        r + q * g * (‖W I y‖ / 2 + r * g) =
            r + q * g * ‖W I y‖ / 2 + r * (q * a I y) := by rw [← hg2]; ring
        _ ≤ 2 * r + q * g * ‖W I y‖ / 2 := by linarith

/-- For each finite nonnegative `K`, the original native coordinate field has
one global linear-growth constant. The bounded radial part is controlled by
the actual finite coefficient mass, so critical points are included. -/
theorem ToricInput.exists_liouvilleCoordinates_linear_growth (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n,
      ‖liouvilleCoordinates I K y‖ ≤ C * (1 + Real.sqrt (realSquaredNorm y.1)) := by
  obtain ⟨k, hk, L, hL, hdom⟩ := I.G_dominant_lowerBound
  obtain ⟨c, _, H, hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  let S : ℝ := ∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let B : ℝ := 1 + S * Real.exp (H * L)
  have hB : 0 < B := by dsimp [B]; positivity
  let T : ℝ := (I.vertices.card : ℝ) / k
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let F : ℝ := T / 2 + (K + 1) * B / 2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨2 + F, by positivity, ?_⟩
  intro y
  let r := Real.sqrt (realSquaredNorm y.1)
  let g := Real.sqrt (a I y)
  let q := K / (1 + K * a I y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = a I y := Real.sq_sqrt (a_nonneg I y)
  obtain ⟨hq, hqa, hqg⟩ := inverse_gain_bounds hK (a_nonneg I y)
  have hterm : q * g * ‖W I y‖ / 2 ≤ F := by
    by_cases hy : L ≤ r
    · have hMg : maxMonomialMagnitude I y ≤ g / k := by
        apply (le_div_iff₀ hk).mpr
        simpa only [mul_comm] using hdom y hy
      have hW : ‖W I y‖ ≤ T * g := by
        calc
          ‖W I y‖ ≤ (I.vertices.card : ℝ) * maxMonomialMagnitude I y :=
            norm_W_le_card_mul_maxMonomialMagnitude I y
          _ ≤ (I.vertices.card : ℝ) * (g / k) :=
            mul_le_mul_of_nonneg_left hMg (by positivity)
          _ = T * g := by dsimp [T]; ring
      have htermT : q * g * ‖W I y‖ / 2 ≤ T / 2 := by
        calc
          q * g * ‖W I y‖ / 2 ≤ q * g * (T * g) / 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hW (mul_nonneg hq hg)) (by norm_num)
          _ = T / 2 * (q * a I y) := by rw [← hg2]; ring
          _ ≤ T / 2 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hqa (by positivity : 0 ≤ T / 2)
      exact htermT.trans (by
        dsimp [F]
        have hp : 0 ≤ (K + 1) * B / 2 := by positivity
        linarith)
    · have hrL : r ≤ L := le_of_not_ge hy
      have hheightL : supportHeight I y.1 ≤ H * L :=
        (hheight y.1).2.trans (mul_le_mul_of_nonneg_left hrL hH.le)
      have hW : ‖W I y‖ ≤ B := by
        calc
          ‖W I y‖ ≤ S * Real.exp (supportHeight I y.1) :=
            norm_W_le_coeff_sum_mul_exp_supportHeight I y
          _ ≤ S * Real.exp (H * L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hheightL) hS
          _ ≤ B := by dsimp [B]; linarith
      have htermB : q * g * ‖W I y‖ / 2 ≤ (K + 1) * B / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hqg hW (norm_nonneg _) (by linarith)) (by norm_num)
      exact htermB.trans (by dsimp [F]; linarith)
  have hcoord : ‖liouvilleCoordinates I K y‖ ≤ 2 * r + F :=
    (norm_liouvilleCoordinates_le_inverse_gain I hK y).trans (by linarith)
  change ‖liouvilleCoordinates I K y‖ ≤ (2 + F) * (1 + r)
  nlinarith [mul_nonneg hF hr]

private theorem euclidean_tangent_norm_le_pi_norm (q : TangentCoordinates n) :
    Real.sqrt (realSquaredNorm q.1 + realSquaredNorm q.2) ≤
      (2 * (n : ℝ) + 1) * ‖q‖ := by
  have hsum (u : RealSpace n) (hu : ‖u‖ ≤ ‖q‖) :
      realSquaredNorm u ≤ (n : ℝ) * ‖q‖ ^ 2 := by
    calc
      realSquaredNorm u ≤ ∑ _j : Fin n, ‖q‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hj : |u j| ≤ ‖q‖ := by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm u j).trans hu
        nlinarith [abs_nonneg (u j), sq_abs (u j), norm_nonneg q]
      _ = _ := by simp
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hN : 2 * (n : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hm := mul_le_mul_of_nonneg_right hN (sq_nonneg ‖q‖)
  nlinarith [hsum q.1 (norm_fst_le q), hsum q.2 (norm_snd_le q)]

/-- The original field's full based Euclidean length grows at most linearly
in its logarithmic radial coordinate, for every finite nonnegative `K`. -/
theorem ToricInput.exists_liouvilleCoordinates_euclidean_growth (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : LGSpace n,
      Real.sqrt (realSquaredNorm (liouvilleCoordinates I K y).1 +
        realSquaredNorm (liouvilleCoordinates I K y).2) ≤
          C * (1 + Real.sqrt (realSquaredNorm y.1)) := by
  obtain ⟨C, hC, hbound⟩ := I.exists_liouvilleCoordinates_linear_growth hK
  have hscale : 0 < 2 * (n : ℝ) + 1 := by positivity
  refine ⟨(2 * (n : ℝ) + 1) * C, mul_pos hscale hC, ?_⟩
  intro y
  calc
    Real.sqrt (realSquaredNorm (liouvilleCoordinates I K y).1 +
        realSquaredNorm (liouvilleCoordinates I K y).2) ≤
        (2 * (n : ℝ) + 1) * ‖liouvilleCoordinates I K y‖ :=
      euclidean_tangent_norm_le_pi_norm _
    _ ≤ (2 * (n : ℝ) + 1) * (C * (1 + Real.sqrt (realSquaredNorm y.1))) :=
      mul_le_mul_of_nonneg_left (hbound y) hscale.le
    _ = _ := by ring

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

/-- The actual original manifold Liouville vector has a cover-coordinate lift
with the proved global Euclidean linear-growth bound. The lift is the native
inverse-system solution, and the quotient tangent identity is already proved.
No complete flow or continuation hypothesis is supplied here. -/
theorem ToricInput.exists_originalLiouville_cover_growth (I : FsFltz.ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : TangentCoordinates n,
      ∃ q : TangentCoordinates n,
        (lgManifold n).liouvilleVector (lambdaKForm I K) (lgCover x) = lgCoverTangent x q ∧
        Real.sqrt (realSquaredNorm q.1 + realSquaredNorm q.2) ≤
          C * (1 + Real.sqrt (realSquaredNorm x.1)) := by
  obtain ⟨C, hC, hbound⟩ := I.exists_liouvilleCoordinates_euclidean_growth hK
  refine ⟨C, hC, ?_⟩
  intro x
  refine ⟨liouvilleCoordinates I K (lgCover x), liouvilleVector_lambdaKForm_lgCover I hK x, ?_⟩
  exact hbound (lgCover x)

end FsFltz.Geometry
