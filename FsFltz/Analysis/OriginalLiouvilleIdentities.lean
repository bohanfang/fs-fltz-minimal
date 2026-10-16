import FsFltz.Geometry.AdmissibilityBridge

/-!
# Liouville identities for the original quadratic potential

The original potential has Hessian `I` on all of `Y`. This module proves
`eq:holoflow` and `eq:holoexhaustion` of `geometric-part-fsf-proof.tex`,
lines 710–750, for the actual native Liouville vector of `lambdaKForm`.
The base outward estimate (`eq:baseoutward`, lines 869–875) is a direct
producer for `prop:allinitial`, lines 878–945. These local calculations
assert no completeness, end-bound existence, or completion marking.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace FsFltz

variable {n : ℕ}

theorem originalLiouville_denominator_pos (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : LGSpace n) : 0 < 1 + K * a I y := by
  exact CoordinateGeometry.liouville_denominator_pos (G I y) hK

/-- Coordinate calculation underlying `eq:holoflow`; the manifold identity
below transfers this proved calculation to the actual field. -/
theorem dW_liouvilleCoordinates (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : LGSpace n) :
    dW I y (liouvilleCoordinates I K y) =
      (b0 I y + (K : ℂ) * (a I y : ℂ) * W I y / 2) /
        (1 + (K : ℂ) * (a I y : ℂ)) := by
  rw [dW_eq_evaluation, tangentComplexCoordinates_liouville,
    CoordinateGeometry.evaluation_liouville, evaluation_radialComplexCoordinates]
  change b0 I y + (K / (1 + K * a I y) : ℝ) * (a I y : ℂ) *
    (W I y / 2 - b0 I y) = _
  have hd : (1 : ℂ) + (K : ℂ) * (a I y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (originalLiouville_denominator_pos I hK y))
  push_cast
  field_simp
  ring

/-- Coordinate calculation underlying `eq:holoexhaustion`. -/
theorem dPhi0_liouvilleCoordinates (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : LGSpace n) :
    dPhi0 y (liouvilleCoordinates I K y) =
      (realSquaredNorm y.1 + K * QW I y) / (1 + K * a I y) := by
  have hsum : (∑ j, y.1 j *
      (conj (G I y j) * (W I y / 2 - b0 I y)).re) =
      (conj (b0 I y) * (W I y / 2 - b0 I y)).re := by
    have hb : conj (b0 I y) = ∑ j, conj ((y.1 j : ℂ) * G I y j) := by
      simp only [b0, map_sum]
    rw [hb, Finset.sum_mul]
    change _ = Complex.reAddGroupHom (∑ j,
      conj ((y.1 j : ℂ) * G I y j) * (W I y / 2 - b0 I y))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hexpand : dPhi0 y (liouvilleCoordinates I K y) =
      realSquaredNorm y.1 + K / (1 + K * a I y) *
        (conj (b0 I y) * (W I y / 2 - b0 I y)).re := by
    simp only [dPhi0, liouvilleCoordinates, mul_add, Finset.sum_add_distrib,
      realSquaredNorm, pow_two]
    congr 1
    simp_rw [← mul_assoc, mul_comm (y.1 _) (K / (1 + K * a I y)), mul_assoc]
    rw [← Finset.mul_sum]
    exact congrArg (fun s => K / (1 + K * a I y) * s) hsum
  rw [hexpand]
  have hd := ne_of_gt (originalLiouville_denominator_pos I hK y)
  unfold QW
  field_simp
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- The squared-base differential formula from `eq:baseoutward`. -/
theorem dAbsWSq_liouvilleCoordinates (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : LGSpace n) :
    dAbsWSq I y (liouvilleCoordinates I K y) =
      (2 * (conj (W I y) * b0 I y).re + K * a I y *
        Complex.normSq (W I y)) / (1 + K * a I y) := by
  rw [dAbsWSq, dW_eq_evaluation, tangentComplexCoordinates_liouville,
    CoordinateGeometry.evaluation_liouville, evaluation_radialComplexCoordinates]
  change 2 * (conj (W I y) * (b0 I y +
    (K / (1 + K * a I y) : ℝ) * (a I y : ℂ) *
      (W I y / 2 - b0 I y))).re = _
  have hd := ne_of_gt (originalLiouville_denominator_pos I hK y)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.normSq_apply]
  norm_num
  field_simp
  ring

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

/-- `eq:holoflow`, for the actual manifold differential and actual field,
without a regular-point hypothesis. -/
theorem complexDifferential_W_originalLiouville (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : (lgManifold n).Point) :
    complexDifferential (lgManifold n) (W I) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) =
      (b0 I y + (K : ℂ) * (a I y : ℂ) * W I y / 2) /
        (1 + (K : ℂ) * (a I y : ℂ)) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [liouvilleVector_lambdaKForm_lgCover I hK, complexDifferential_W_lgCover]
  exact dW_liouvilleCoordinates I hK (lgCover x)

/-- `eq:holoexhaustion`, for the prescribed original potential and field. -/
theorem differentialCovector_phi0_originalLiouville (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : (lgManifold n).Point) :
    differentialCovector (lgManifold n) phi0 y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) =
      (realSquaredNorm y.1 + K * QW I y) / (1 + K * a I y) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [liouvilleVector_lambdaKForm_lgCover I hK, differentialCovector_phi0_lgCover]
  exact dPhi0_liouvilleCoordinates I hK (lgCover x)

/-- The base outwardness formula evaluated on the actual native field. -/
theorem differentialCovector_absWSq_originalLiouville (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) (y : (lgManifold n).Point) :
    differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) =
      (2 * (conj (W I y) * b0 I y).re + K * a I y *
        Complex.normSq (W I y)) / (1 + K * a I y) := by
  rw [differentialCovector_absWSq_liouvilleVector I hK]
  exact dAbsWSq_liouvilleCoordinates I hK y

/-- Local ambient outwardness from an honest positive end expression. The
existence of such an end bound is a separate geometric obligation. -/
theorem differentialCovector_phi0_originalLiouville_pos (I : ToricInput n)
    {K Aamb : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb)
    (y : (lgManifold n).Point) (hy : Aamb ≤ phi0 y) :
    0 < differentialCovector (lgManifold n) phi0 y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
  rw [differentialCovector_phi0_originalLiouville I hK]
  have hr : 0 < realSquaredNorm y.1 := by
    have hp : 0 < phi0 y := hamb.1.trans_le hy
    change 0 < realSquaredNorm y.1 / 2 at hp
    linarith
  exact div_pos (add_pos_of_pos_of_nonneg hr (mul_nonneg hK (hamb.2 y hy).2.le))
    (originalLiouville_denominator_pos I hK y)

/-- The literal threshold `K0 = 1 + 2 sup S_R` gives exactly the source's
lower bound in `eq:baseoutward`. Nonemptiness and boundedness of the actual
range set are explicit; a positive derivative is not an input assumption. -/
theorem differentialCovector_absWSq_originalLiouville_lower_bound
    (I : ToricInput n) {R K : ℝ} (hR : 0 < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (y : (lgManifold n).Point) (hy : R ≤ ‖W I y‖) (ha : 0 < a I y) :
    a I y * Complex.normSq (W I y) / (1 + K * a I y) ≤
      differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  rw [differentialCovector_absWSq_originalLiouville I hKnonneg]
  apply (div_le_div_iff_of_pos_right (originalLiouville_denominator_pos I hKnonneg y)).mpr
  have hw : 0 < ‖W I y‖ := hR.trans_le hy
  have hratio : 2 * endRatio I y ≤ K - 1 := by
    have hs := endRatio_le_sup I R hset.2 y hy
    unfold K0 at hK
    linarith
  have hb : 2 * ‖b0 I y‖ ≤ (K - 1) * (a I y * ‖W I y‖) := by
    have hd : 0 < a I y * ‖W I y‖ := mul_pos ha hw
    have hh : ‖b0 I y‖ / (a I y * ‖W I y‖) ≤ (K - 1) / 2 := by
      change 2 * (‖b0 I y‖ / (a I y * ‖W I y‖)) ≤ K - 1 at hratio
      linarith
    have hh' := (div_le_iff₀ hd).mp hh
    linarith
  have hb' := mul_le_mul_of_nonneg_right hb hw.le
  have hre : -(‖W I y‖ * ‖b0 I y‖) ≤ (conj (W I y) * b0 I y).re := by
    have hh := Complex.abs_re_le_norm (conj (W I y) * b0 I y)
    have hh' := neg_le_abs (conj (W I y) * b0 I y).re
    rw [norm_mul, Complex.norm_conj] at hh
    linarith
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

/-- Strict outwardness over the far base region, with the same literal `K0`.
This is the analytic producer used at the corner in `prop:allinitial`. -/
theorem differentialCovector_absWSq_originalLiouville_pos
    (I : ToricInput n) {R K : ℝ} (hR : 0 < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (y : (lgManifold n).Point) (hy : R ≤ ‖W I y‖) (ha : 0 < a I y) :
    0 < differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hw : 0 < Complex.normSq (W I y) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (hR.trans_le hy)
  exact (div_pos (mul_pos ha hw) (originalLiouville_denominator_pos I hKnonneg y)).trans_le
    (differentialCovector_absWSq_originalLiouville_lower_bound I hR hset hK y hy ha)

/-- Both defining functions are strictly outward at an original corner.
The only hypotheses are the source's explicit analytic bounds and literal
threshold conditions. This supplies the two positivity inputs in the first
paragraph of `prop:allinitial`, proof manuscript lines 886–896. It does not
assert transverse-corner or rounding existence; those separate producers
are proved in `OriginalRoundingCorner` and `OriginalRounding`. -/
theorem original_corner_outward_derivatives (I : ToricInput n)
    {Aamb R K A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hmax : SublevelMaximumAttained I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hA : Aamb ≤ A) (y : (lgManifold n).Point)
    (hphi : phi0 y = A) (hW : ‖W I y‖ = R) :
    0 < differentialCovector (lgManifold n) phi0 y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y) ∧
      0 < differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hy : R ≤ ‖W I y‖ := hW.ge
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  have hden := endRatio_denominator_pos I Aamb R hamb hmax hR y hy
  have ha : 0 < a I y := (mul_pos_iff_of_pos_right (hRpos.trans_le hy)).mp hden
  exact ⟨differentialCovector_phi0_originalLiouville_pos I hKnonneg hamb y
      (by simpa only [hphi] using hA),
    differentialCovector_absWSq_originalLiouville_pos I hRpos hset hK y hy ha⟩

end FsFltz.Geometry
