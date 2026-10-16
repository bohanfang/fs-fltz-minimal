import FsFltz.Analysis.OriginalLiouvilleIdentities
import FsFltz.Compactness

/-!
# Transversality and compact band persistence for original roundings

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 886–896,
and `geoemtric-part-fsf.tex`, `def:rounding`, lines 309–326.
The projected radial vector proves corner transversality from the prescribed
fiber end bound. Compactness then persists base outwardness on a small band.
These are producers for admissible rounding existence; smooth-max profile
existence and the completion markings are separate obligations.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace FsFltz

variable {n : ℕ}

/-- The real tangent coordinates of the radial vector projected to `ker dW`.
This is an input-defined vector, with no assumed fiber field or flow. -/
def originalFiberTangentCoordinates (I : ToricInput n) (y : LGSpace n) :
    TangentCoordinates n :=
  let z : Fin n → ℂ := fun j => (y.1 j : ℂ) - conj (G I y j) *
    (b0 I y / (a I y : ℂ))
  (fun j => (z j).re, fun j => (z j).im)

theorem tangentComplexCoordinates_originalFiberTangent (I : ToricInput n)
    (y : LGSpace n) :
    tangentComplexCoordinates (originalFiberTangentCoordinates I y) =
      fun j => (y.1 j : ℂ) - conj (G I y j) * (b0 I y / (a I y : ℂ)) := by
  funext j
  apply Complex.ext <;> simp [tangentComplexCoordinates, originalFiberTangentCoordinates]

/-- The projected radial vector is tangent to every regular original fiber.
Source: `prop:allinitial`, proof manuscript lines 887–891. -/
theorem dW_originalFiberTangent_zero (I : ToricInput n) (y : LGSpace n)
    (ha : 0 < a I y) :
    dW I y (originalFiberTangentCoordinates I y) = 0 := by
  rw [dW_eq_evaluation, tangentComplexCoordinates_originalFiberTangent]
  have hsum : (∑ j, G I y j * conj (G I y j)) = (a I y : ℂ) := by
    simp only [a, Complex.ofReal_sum, Complex.mul_conj]
  have he : CoordinateGeometry.evaluation (G I y)
      (fun j => (y.1 j : ℂ) - conj (G I y j) * (b0 I y / (a I y : ℂ))) =
      b0 I y - (a I y : ℂ) * (b0 I y / (a I y : ℂ)) := by
    simp only [CoordinateGeometry.evaluation, mul_sub, Finset.sum_sub_distrib,
      ← mul_assoc, ← Finset.sum_mul, hsum, b0]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [he]
  have hane : (a I y : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

/-- The potential derivative on the projected radial vector is precisely the
strict Cauchy defect appearing in `eq:fiberbound`, target lines 277–280. -/
theorem dPhi0_originalFiberTangent (I : ToricInput n) (y : LGSpace n) :
    dPhi0 y (originalFiberTangentCoordinates I y) =
      realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y := by
  have hsum : (∑ j, (y.1 j : ℂ) * conj (G I y j)) = conj (b0 I y) := by
    simp [b0, map_sum, map_mul]
  have hreal : (∑ j, y.1 j *
      (conj (G I y j) * (b0 I y / (a I y : ℂ))).re) =
      Complex.normSq (b0 I y) / a I y := by
    calc
      _ = (∑ j, (y.1 j : ℂ) *
          (conj (G I y j) * (b0 I y / (a I y : ℂ)))).re := by
        change _ = Complex.reAddGroupHom _
        rw [map_sum]
        simp
      _ = (conj (b0 I y) * (b0 I y / (a I y : ℂ))).re := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, hsum]
      _ = _ := by
        rw [← mul_div_assoc, Complex.conj_mul', Complex.div_ofReal_re]
        rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [dPhi0, originalFiberTangentCoordinates, Complex.sub_re,
    Complex.ofReal_re, mul_sub, Finset.sum_sub_distrib, hreal]
  congr 1
  simp [realSquaredNorm, pow_two]

/-- The projected radial vector kills the first coefficient of a covector
relation; any strictly base-outward vector then kills its second coefficient.
Source: `prop:allinitial`, proof manuscript lines 886–891. -/
theorem cornerCovectorsIndependent_of_fiberDefect (I : ToricInput n)
    (y : LGSpace n) (ha : 0 < a I y)
    (hdef : 0 < realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y)
    (q : TangentCoordinates n) (hq : 0 < dAbsWSq I y q) :
    CornerCovectorsIndependent I y := by
  intro s t hst
  have hf := hst (originalFiberTangentCoordinates I y)
  rw [dPhi0_originalFiberTangent, dAbsWSq, dW_originalFiberTangent_zero I y ha] at hf
  simp only [mul_zero, Complex.zero_re, add_zero] at hf
  have hs : s = 0 := (mul_eq_zero.mp hf).resolve_right hdef.ne'
  have hb := hst q
  rw [hs, zero_mul, zero_add] at hb
  exact ⟨hs, (mul_eq_zero.mp hb).resolve_right hq.ne'⟩

@[fun_prop]
theorem continuous_G (I : ToricInput n) (j : Fin n) :
    Continuous (fun y => G I y j) := by
  unfold G
  fun_prop

@[fun_prop]
theorem continuous_a (I : ToricInput n) : Continuous (a I) := by
  unfold a
  simp only [Complex.normSq_apply]
  fun_prop

@[fun_prop]
theorem continuous_b0 (I : ToricInput n) : Continuous (b0 I) := by
  unfold b0
  fun_prop

/-- The coordinate base derivative is continuous on the actual quotient for
every nonnegative coefficient, since its native denominator stays positive. -/
theorem continuous_originalBaseDerivative (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) :
    Continuous (fun y => dAbsWSq I y (liouvilleCoordinates I K y)) := by
  simp_rw [dAbsWSq_liouvilleCoordinates I hK]
  apply Continuous.div
  · simp only [Complex.normSq_apply]
    fun_prop
  · fun_prop
  · intro y
    exact (originalLiouville_denominator_pos I hK y).ne'

/-- Strict base outwardness at the compact corner persists on all sufficiently
small literal bands. The compact bad set has a positive minimum of the sum
of the two level deficits; an empty bad set is handled directly.
Source: `prop:allinitial`, proof manuscript lines 886–896. -/
theorem exists_original_cornerBand_base_outward (I : ToricInput n)
    {Aamb R K A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hmax : SublevelMaximumAttained I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K) (hA : Aamb ≤ A) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ eps : ℝ, eps ≤ delta →
      ∀ y ∈ CornerBand I R A eps,
        0 < dAbsWSq I y (liouvilleCoordinates I K y) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  let D : LGSpace n → ℝ := fun y => dAbsWSq I y (liouvilleCoordinates I K y)
  let S : Set (LGSpace n) := {y | phi0 y ≤ A ∧
    Complex.normSq (W I y) ≤ R ^ 2 ∧ D y ≤ 0}
  let g : LGSpace n → ℝ := fun y => A - phi0 y + (R ^ 2 - Complex.normSq (W I y))
  have hD : Continuous D := continuous_originalBaseDerivative I hKnonneg
  have hW : Continuous (fun y => Complex.normSq (W I y)) := by
    simp only [Complex.normSq_apply]
    fun_prop
  have hg : Continuous g := (continuous_const.sub continuous_phi0).add
    (continuous_const.sub hW)
  have hS : IsCompact S := by
    apply (isCompact_phi0_sublevel A (hamb.1.le.trans hA)).of_isClosed_subset
    · exact (isClosed_le continuous_phi0 continuous_const).inter
        ((isClosed_le hW continuous_const).inter (isClosed_le hD continuous_const))
    · exact fun y hy => hy.1
  have hpos : ∀ y ∈ S, 0 < g y := by
    intro y hy
    by_contra hn
    have hphi : phi0 y = A := by
      change ¬0 < A - phi0 y + (R ^ 2 - Complex.normSq (W I y)) at hn
      linarith [hy.1, hy.2.1]
    have hnormSq : Complex.normSq (W I y) = R ^ 2 := by
      change ¬0 < A - phi0 y + (R ^ 2 - Complex.normSq (W I y)) at hn
      linarith [hy.1, hy.2.1]
    have hnorm : ‖W I y‖ = R := by
      rw [Complex.normSq_eq_norm_sq] at hnormSq
      nlinarith [norm_nonneg (W I y)]
    have hout := (Geometry.original_corner_outward_derivatives I hamb hmax hR
      hset hK hA y hphi hnorm).2
    rw [Geometry.differentialCovector_absWSq_liouvilleVector I hKnonneg y] at hout
    exact (not_lt_of_ge hy.2.2) hout
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    refine ⟨g z / 2, half_pos (hpos z hz), ?_⟩
    intro eps heps y hy
    by_contra hn
    have hyS : y ∈ S := ⟨by linarith [hy.2.1], by linarith [hy.2.2.2], le_of_not_gt hn⟩
    have hmin' : g z ≤ g y := hmin hyS
    have hsmall : g y < 2 * eps := by
      change A - phi0 y + (R ^ 2 - Complex.normSq (W I y)) < 2 * eps
      linarith [hy.1, hy.2.2.1]
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro eps _ y hy
    by_contra hn
    apply hne
    refine ⟨y, ?_⟩
    exact ⟨by linarith [hy.2.1], by linarith [hy.2.2.2], le_of_not_gt hn⟩

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

/-- A valid fiber end bound proves the actual corner transversality whenever
the native base derivative is positive. It applies to the whole permitted
band, and also to an empty rank-one band without a dimension restriction.
Source: `prop:allinitial`, proof manuscript lines 886–896. -/
theorem original_cornerBand_covectorsIndependent (I : ToricInput n)
    {Aamb R Afib K Aminus A eps : ℝ} (hfib : FiberEndBound I Aamb R Afib)
    (hR : 0 ≤ R) (hlevels : Afib < Aminus) (hwidth : eps < A - Aminus)
    (hK : 0 ≤ K) (y : (lgManifold n).Point) (hy : y ∈ CornerBand I R A eps)
    (hbase : 0 < differentialCovector (lgManifold n)
      (fun x => Complex.normSq (W I x)) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y)) :
    GeometricCornerCovectorsIndependent I y := by
  rw [geometricCornerCovectorsIndependent_iff]
  have hphi : Afib ≤ phi0 y := by
    have hh := hy.1
    linarith
  have hW : ‖W I y‖ ≤ R := by
    have hh := hy.2.2.2
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (W I y)]
  obtain ⟨ha, hdef⟩ := hfib.2 y hphi hW
  apply cornerCovectorsIndependent_of_fiberDefect I y ha hdef (liouvilleCoordinates I K y)
  rwa [differentialCovector_absWSq_liouvilleVector I hK] at hbase

/-- Every valid choice of original fiber bound and levels has a positive
width below which both actual geometric band conditions hold. This statement
does not quantify over profiles, so its geometric content is independent of
the separate smooth-max construction.
Source: `prop:allinitial`, lines 886–896; `def:rounding`, lines 309–326. -/
theorem exists_original_cornerBand_geometry (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (hA : Aminus < A) :
    ∃ delta : ℝ, 0 < delta ∧ delta < A - Aminus ∧
      ∀ eps : ℝ, eps ≤ delta → ∀ y ∈ CornerBand I R A eps,
        0 < differentialCovector (lgManifold n)
          (fun x => Complex.normSq (W I x)) y
          ((lgManifold n).liouvilleVector (lambdaKForm I K) y) ∧
        GeometricCornerCovectorsIndependent I y := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  have hAamb : Aamb ≤ A := hfib.1.trans (hlevels.le.trans hA.le)
  obtain ⟨delta0, hd0, hband⟩ := exists_original_cornerBand_base_outward I hamb
    (sublevelMaximumAttained I Aamb hamb.1.le) hR hset hK hAamb
  let delta := min delta0 ((A - Aminus) / 2)
  have hd : 0 < delta := lt_min hd0 (half_pos (sub_pos.mpr hA))
  have hdwidth : delta < A - Aminus := by
    exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨delta, hd, hdwidth, ?_⟩
  intro eps heps y hy
  have hwidth : eps < A - Aminus := heps.trans_lt hdwidth
  have hbase : 0 < differentialCovector (lgManifold n)
      (fun x => Complex.normSq (W I x)) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
    rw [differentialCovector_absWSq_liouvilleVector I hKnonneg y]
    exact hband eps (heps.trans (min_le_left _ _)) y hy
  exact ⟨hbase, original_cornerBand_covectorsIndependent I hfib hRpos.le hlevels
    hwidth hKnonneg y hy hbase⟩

/-- The proved geometric band width makes every positive-width smooth-max
profile admissible. The profile-existence producer completes the actual
rounding-existence assertion of `prop:allinitial`, lines 878–908. -/
theorem exists_original_admissible_rounding_width (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (hA : Aminus < A) :
    ∃ delta : ℝ, 0 < delta ∧ delta < A - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ delta →
        GeometricAdmissibleRounding I R K Aminus A m := by
  obtain ⟨delta, hd, hwidth, hband⟩ := exists_original_cornerBand_geometry I
    hamb hR hset hK hfib hlevels hA
  refine ⟨delta, hd, hwidth, ?_⟩
  intro m hm heps
  exact ⟨hm, heps.trans_lt hwidth, hband m.eps heps⟩

end FsFltz.Geometry
