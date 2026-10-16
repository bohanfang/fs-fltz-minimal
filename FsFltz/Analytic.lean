import FsFltz.Toric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Analytic expressions and the specified initial sets

This module encodes `sec:initial` of `geoemtric-part-fsf.tex`, lines 249–348,
and the bound/rounding handoff in `sec:lean`, lines 798–802. All norms of
coordinate vectors use the Euclidean sum of squares. The superpotential is
the quotient-defined function `W`; no global real angle is chosen.

The tangent-coordinate expressions below are concrete formulas, rather than
assumed vector fields or opaque admissibility predicates. Their identification
with descended smooth forms, actual differentials and the Liouville field
requires separate foundational bridge lemmas. Accordingly the rounding
predicate is named `CoordinateAdmissibleRounding`. Neither its existence nor
the existence of an end bound is proved here.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ContDiff

variable {n : ℕ}

/-- The squared Euclidean norm associated to the fixed basis. -/
def realSquaredNorm (u : RealSpace n) : ℝ := ∑ j, (u j) ^ 2

/-- The prescribed quadratic potential (`sec:data`, line 71). -/
def phi0 (y : LGSpace n) : ℝ := realSquaredNorm y.1 / 2

/-- Complex logarithmic derivative vector (`sec:initial`, lines 253–254). -/
def G (I : ToricInput n) (y : LGSpace n) (j : Fin n) : ℂ :=
  ∑ v : {v : Lattice n // v ∈ I.vertices},
    monomial (I.coeff v) v.val y * (v.val j : ℂ)

/-- The real scalar `ḠᵀG`, written as a sum of squared complex norms. -/
def a (I : ToricInput n) (y : LGSpace n) : ℝ :=
  ∑ j, Complex.normSq (G I y j)

/-- The complex scalar `u · G` (`sec:initial`, line 255). -/
def b0 (I : ToricInput n) (y : LGSpace n) : ℂ :=
  ∑ j, (y.1 j : ℂ) * G I y j

/-- The prescribed ambient end expression (`sec:initial`, line 256). -/
def QW (I : ToricInput n) (y : LGSpace n) : ℝ :=
  realSquaredNorm y.1 * a I y - Complex.normSq (b0 I y) +
    (star (W I y) * b0 I y).re / 2

/-- Basis components of a tangent vector to `M_ℝ × T`. -/
abbrev TangentCoordinates (n : ℕ) := RealSpace n × RealSpace n

/-- Concrete candidate for the differential of `W` on quotient tangent
coordinates. Its differential/descent bridge is a separate lemma. -/
def dW (I : ToricInput n) (y : LGSpace n) (q : TangentCoordinates n) : ℂ :=
  ∑ j, G I y j * ((q.1 j : ℂ) + Complex.I * (q.2 j : ℂ))

/-- Concrete differential of the quadratic potential. -/
def dPhi0 (y : LGSpace n) (q : TangentCoordinates n) : ℝ :=
  ∑ j, y.1 j * q.1 j

/-- Concrete candidate for `d(|W|²)` on quotient tangent coordinates. -/
def dAbsWSq (I : ToricInput n) (y : LGSpace n)
    (q : TangentCoordinates n) : ℝ :=
  2 * (star (W I y) * dW I y q).re

/-- The descended coordinate formula for the original primitive. -/
def lambda0Coordinates (y : LGSpace n) (q : TangentCoordinates n) : ℝ :=
  ∑ j, y.1 j * q.2 j

/-- Explicit coordinate formula for `λ₀ + K W*λ_ℂ` (`sec:data`, lines 74–85). -/
def lambdaKCoordinates (I : ToricInput n) (K : ℝ) (y : LGSpace n)
    (q : TangentCoordinates n) : ℝ :=
  lambda0Coordinates y q + K / 2 *
    ((W I y).re * (dW I y q).im - (W I y).im * (dW I y q).re)

/-- The canonical symplectic coordinate formula `Σ duⱼ ∧ dθⱼ`. -/
def omega0Coordinates (q r : TangentCoordinates n) : ℝ :=
  ∑ j, (q.1 j * r.2 j - r.1 j * q.2 j)

/-- Explicit candidate for `dλ_K`; exterior differentiation is a bridge to prove. -/
def omegaKCoordinates (I : ToricInput n) (K : ℝ) (y : LGSpace n)
    (q r : TangentCoordinates n) : ℝ :=
  omega0Coordinates q r + K *
    ((dW I y q).re * (dW I y r).im - (dW I y r).re * (dW I y q).im)

/-- Rank-two inverse formula for the candidate Liouville field. It is defined
from the input, with no arbitrary field supplied. The pointwise equation
`ω_K(Z_K, ·) = λ_K` is proved in `AnalyticGeometry`; its realization as the
smooth geometric Liouville field remains a separate bridge. -/
def liouvilleCoordinates (I : ToricInput n) (K : ℝ) (y : LGSpace n) :
    TangentCoordinates n :=
  (fun j => y.1 j + K / (1 + K * a I y) *
      (star (G I y j) * (W I y / 2 - b0 I y)).re,
   fun j => K / (1 + K * a I y) *
      (star (G I y j) * (W I y / 2 - b0 I y)).im)

/-- Pointwise nonzero wedge of the two real covectors, spelled out as linear
independence. This permits empty bands, including the rank-one case. -/
def CornerCovectorsIndependent (I : ToricInput n) (y : LGSpace n) : Prop :=
  ∀ s t : ℝ, (∀ q : TangentCoordinates n,
    s * dPhi0 y q + t * dAbsWSq I y q = 0) → s = 0 ∧ t = 0

/-- The exact positive ambient end conditions (`sec:initial`, lines 259–260). -/
def AmbientEndBound (I : ToricInput n) (Aamb : ℝ) : Prop :=
  0 < Aamb ∧ ∀ y, Aamb ≤ phi0 y → 0 < a I y ∧ 0 < QW I y

/-- Literal magnitude image of the potential sublevel. -/
def sublevelMagnitudes (I : ToricInput n) (Aamb : ℝ) : Set ℝ :=
  (fun y => ‖W I y‖) '' {y | phi0 y ≤ Aamb}

/-- Total supremum formula for `M(Aamb)`. Attainment and compactness must be
proved before calling this number the source's maximum. -/
def sublevelMagnitudeSup (I : ToricInput n) (Aamb : ℝ) : ℝ :=
  sSup (sublevelMagnitudes I Aamb)

/-- The assertion that the prescribed supremum is an actual maximum. -/
def SublevelMaximumAttained (I : ToricInput n) (Aamb : ℝ) : Prop :=
  (∀ y, phi0 y ≤ Aamb → ‖W I y‖ ≤ sublevelMagnitudeSup I Aamb) ∧
  ∃ y, phi0 y ≤ Aamb ∧ ‖W I y‖ = sublevelMagnitudeSup I Aamb

/-- The formula-defined ratio, with the usual total real division. -/
def endRatio (I : ToricInput n) (y : LGSpace n) : ℝ :=
  ‖b0 I y‖ / (a I y * ‖W I y‖)

/-- The literal set `S_R` (`sec:initial`, lines 263–266). -/
def ratioSet (I : ToricInput n) (R : ℝ) : Set ℝ :=
  endRatio I '' {y | R ≤ ‖W I y‖}

/-- Required nonemptiness and boundedness, retained separately from the total
supremum. These are conclusions of the target, never input fields. -/
def RatioSetWellDefined (I : ToricInput n) (R : ℝ) : Prop :=
  (ratioSet I R).Nonempty ∧ BddAbove (ratioSet I R)

/-- The prescribed threshold `1 + 2 sup S_R` (`eq:threshold`, lines 269–276). -/
def K0 (I : ToricInput n) (R : ℝ) : ℝ := 1 + 2 * sSup (ratioSet I R)

/-- Exact fiber-end conditions (`eq:fiberbound`, lines 277–289). In dimension
one this condition is allowed to hold on an empty end, with no positivity
claim on a nonempty band. -/
def FiberEndBound (I : ToricInput n) (Aamb R Afib : ℝ) : Prop :=
  Aamb ≤ Afib ∧ ∀ y, Afib ≤ phi0 y → ‖W I y‖ ≤ R →
    0 < a I y ∧ 0 < realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y

/-- A global `C∞` convex smooth-max profile. In this pinned Mathlib, `∞` is
smooth regularity; the outer `⊤` would require analytic regularity. -/
structure RoundingProfile (eps : ℝ) where
  toFun : ℝ × ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  convex : ConvexOn ℝ Set.univ toFun
  partialFirst_nonneg : ∀ xy, 0 ≤ fderiv ℝ toFun xy (1, 0)
  partialSecond_nonneg : ∀ xy, 0 ≤ fderiv ℝ toFun xy (0, 1)
  partial_sum : ∀ xy, fderiv ℝ toFun xy (1, 0) + fderiv ℝ toFun xy (0, 1) = 1
  lower : ∀ xy, max xy.1 xy.2 ≤ toFun xy
  upper : ∀ xy, toFun xy ≤ max xy.1 xy.2 + eps
  exact_away : ∀ xy, eps ≤ |xy.1 - xy.2| → toFun xy = max xy.1 xy.2

/-- A rounding choice contains only its width and profile, with admissibility
tested against the fixed input and parameters rather than baked into inputs. -/
structure RoundingChoice where
  eps : ℝ
  profile : RoundingProfile eps

/-- The literal rounded domain (`eq:initialpair`, lines 302–304). -/
def RoundedDomain (I : ToricInput n) (R A : ℝ) (m : RoundingChoice) :
    Set (LGSpace n) :=
  {y | m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2) ≤ 0}

/-- The domain with corners before rounding (`sec:initial`, line 329). -/
def CornerDomain (I : ToricInput n) (R A : ℝ) : Set (LGSpace n) :=
  {y | phi0 y ≤ A ∧ ‖W I y‖ ≤ R}

/-- The explicitly specified full-fiber truncation; `R` is the real positive
value itself, not merely its modulus (`eq:initialpair`, line 305). -/
def InitialRibbon (I : ToricInput n) (R Aminus : ℝ) : Set (LGSpace n) :=
  {y | W I y = (R : ℂ) ∧ phi0 y ≤ Aminus}

/-- The whole complex fiber named in the source's second completion marking. -/
def FullFiber (I : ToricInput n) (R : ℝ) : Set (LGSpace n) :=
  {y | W I y = (R : ℂ)}

/-- The literal open/closed corner band (`def:rounding`, lines 313–317). -/
def CornerBand (I : ToricInput n) (R A eps : ℝ) : Set (LGSpace n) :=
  {y | -eps < phi0 y - A ∧ phi0 y - A ≤ 0 ∧
    -eps < Complex.normSq (W I y) - R ^ 2 ∧
    Complex.normSq (W I y) - R ^ 2 ≤ 0}

/-- The exact analytic conditions of `def:rounding` using concrete tangent
formulas. The geometric realization of these formulas is explicitly pending;
this predicate contains no completion, full-fiber, core, or chain condition. -/
def CoordinateAdmissibleRounding (I : ToricInput n) (R K Aminus A : ℝ)
    (m : RoundingChoice) : Prop :=
  0 < m.eps ∧ m.eps < A - Aminus ∧
  ∀ y, y ∈ CornerBand I R A m.eps →
    0 < dAbsWSq I y (liouvilleCoordinates I K y) ∧ CornerCovectorsIndependent I y

theorem realSquaredNorm_nonneg (u : RealSpace n) : 0 ≤ realSquaredNorm u := by
  exact Finset.sum_nonneg fun j _ => sq_nonneg (u j)

theorem a_nonneg (I : ToricInput n) (y : LGSpace n) : 0 ≤ a I y := by
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (G I y j)

theorem endRatio_nonneg (I : ToricInput n) (y : LGSpace n) : 0 ≤ endRatio I y := by
  exact div_nonneg (norm_nonneg _) (mul_nonneg (a_nonneg I y) (norm_nonneg _))

/-- No default value of a supremum is used: both required set hypotheses are
explicit (`eq:threshold`, lines 268–276). -/
theorem one_le_K0 (I : ToricInput n) (R : ℝ)
    (hne : (ratioSet I R).Nonempty) (hb : BddAbove (ratioSet I R)) : 1 ≤ K0 I R := by
  obtain ⟨r, hr⟩ := hne
  obtain ⟨y, hy, rfl⟩ := hr
  have h : 0 ≤ sSup (ratioSet I R) :=
    (endRatio_nonneg I y).trans (le_csSup hb ⟨y, hy, rfl⟩)
  unfold K0
  linarith

/-- A single far-end ratio is bounded by the specified supremum. -/
theorem endRatio_le_sup (I : ToricInput n) (R : ℝ)
    (hb : BddAbove (ratioSet I R)) (y : LGSpace n) (hy : R ≤ ‖W I y‖) :
    endRatio I y ≤ sSup (ratioSet I R) :=
  le_csSup hb ⟨y, hy, rfl⟩

/-- A value outside the magnitude maximum must lie strictly beyond the
ambient sublevel. The maximum assertion is explicit, not a supremum default. -/
theorem phi0_gt_of_far_value (I : ToricInput n) (Aamb R : ℝ)
    (hmax : SublevelMaximumAttained I Aamb)
    (hR : sublevelMagnitudeSup I Aamb < R) (y : LGSpace n)
    (hy : R ≤ ‖W I y‖) : Aamb < phi0 y := by
  by_contra h
  have hle : phi0 y ≤ Aamb := le_of_not_gt h
  exact (not_lt_of_ge (hy.trans (hmax.1 y hle))) hR

/-- The source's strict denominator claim follows from the ambient bound
and the stated radius restrictions (`sec:initial`, lines 267–268). -/
theorem endRatio_denominator_pos (I : ToricInput n) (Aamb R : ℝ)
    (hamb : AmbientEndBound I Aamb) (hmax : SublevelMaximumAttained I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (y : LGSpace n) (hy : R ≤ ‖W I y‖) : 0 < a I y * ‖W I y‖ := by
  have hphi : Aamb < phi0 y :=
    phi0_gt_of_far_value I Aamb R hmax ((le_max_right _ _).trans_lt hR) y hy
  have ha : 0 < a I y := (hamb.2 y hphi.le).1
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  exact mul_pos ha (hRpos.trans_le hy)

/-- The smaller of two valid fiber bounds is again valid, as used by
`lem:choices`, lines 448–449. -/
theorem min_fiberEndBound (I : ToricInput n) (Aamb R A B : ℝ)
    (hA : FiberEndBound I Aamb R A) (hB : FiberEndBound I Aamb R B) :
    FiberEndBound I Aamb R (min A B) := by
  by_cases h : A ≤ B
  · simpa only [min_eq_left h] using hA
  · simpa only [min_eq_right (le_of_not_ge h)] using hB

/-- Rounding cannot enlarge the domain with corners (`sec:initial`, line 330). -/
theorem roundedDomain_subset_cornerDomain (I : ToricInput n)
    (R A : ℝ) (m : RoundingChoice) (hR : 0 ≤ R) :
    RoundedDomain I R A m ⊆ CornerDomain I R A := by
  intro y hy
  have hlower := m.profile.lower (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
  have hmax : max (phi0 y - A) (Complex.normSq (W I y) - R ^ 2) ≤ 0 :=
    hlower.trans hy
  have hphi := (le_max_left (phi0 y - A)
    (Complex.normSq (W I y) - R ^ 2)).trans hmax
  have hnorm := (le_max_right (phi0 y - A)
    (Complex.normSq (W I y) - R ^ 2)).trans hmax
  refine ⟨by linarith, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [← Complex.normSq_eq_norm_sq]
  linarith

/-- The ribbon is on the unrounded zero face because its potential lies
strictly below the rounding band (`sec:initial`, lines 342–348). -/
theorem initialRibbon_profile_eq_zero (I : ToricInput n)
    (R Aminus A : ℝ) (m : RoundingChoice) (hpos : 0 < m.eps)
    (hwidth : m.eps < A - Aminus) (y : LGSpace n)
    (hy : y ∈ InitialRibbon I R Aminus) :
    m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2) = 0 := by
  have hx : phi0 y - A < -m.eps := by linarith [hy.2]
  have hx0 : phi0 y - A ≤ 0 := by linarith
  have hzero : Complex.normSq (W I y) - R ^ 2 = 0 := by
    rw [hy.1, Complex.normSq_ofReal]
    ring
  rw [hzero, m.profile.exact_away]
  · exact max_eq_right hx0
  · simpa only [sub_zero] using
      (show m.eps ≤ |phi0 y - A| by linarith [neg_le_abs (phi0 y - A)])

/-- No part of the prescribed ribbon is removed by rounding. -/
theorem initialRibbon_subset_roundedDomain (I : ToricInput n)
    (R Aminus A : ℝ) (m : RoundingChoice) (hpos : 0 < m.eps)
    (hwidth : m.eps < A - Aminus) :
    InitialRibbon I R Aminus ⊆ RoundedDomain I R A m := by
  intro y hy
  exact (initialRibbon_profile_eq_zero I R Aminus A m hpos hwidth y hy).le

theorem initialRibbon_subset_fullFiber (I : ToricInput n) (R Aminus : ℝ) :
    InitialRibbon I R Aminus ⊆ FullFiber I R := by
  intro y hy
  exact hy.1

/-- In rank one the fiber Cauchy defect is identically zero wherever `a>0`,
exactly as required by `sec:initial`, lines 283–289. -/
theorem fiberDefect_rank_one (I : ToricInput 1) (y : LGSpace 1)
    (ha : 0 < a I y) :
    realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y = 0 := by
  have hne : Complex.normSq (G I y 0) ≠ 0 := by
    simpa only [a, Fin.sum_univ_one] using ne_of_gt ha
  simp only [realSquaredNorm, b0, a, Fin.sum_univ_one,
    Complex.normSq_mul, Complex.normSq_ofReal]
  rw [mul_div_cancel_right₀ _ hne]
  ring

/-- A valid rank-one fiber bound forces its bounded-value end to be empty. -/
theorem fiberEnd_empty_rank_one (I : ToricInput 1) (Aamb R Afib : ℝ)
    (hfib : FiberEndBound I Aamb R Afib) :
    {y : LGSpace 1 | Afib ≤ phi0 y ∧ ‖W I y‖ ≤ R} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨ha, hdef⟩ := hfib.2 y hy.1 hy.2
  rw [fiberDefect_rank_one I y ha] at hdef
  exact lt_irrefl 0 hdef

/-- In rank one, a point of bounded superpotential value lies strictly below
every valid fiber end bound. -/
theorem phi0_lt_fiberBound_rank_one (I : ToricInput 1) (Aamb R Afib : ℝ)
    (hfib : FiberEndBound I Aamb R Afib) (y : LGSpace 1)
    (hy : ‖W I y‖ ≤ R) : phi0 y < Afib := by
  by_contra h
  have hmem : y ∈ {y : LGSpace 1 | Afib ≤ phi0 y ∧ ‖W I y‖ ≤ R} :=
    ⟨le_of_not_gt h, hy⟩
  rw [fiberEnd_empty_rank_one I Aamb R Afib hfib] at hmem
  exact hmem

/-- The rank-one corner band is empty for the source's admissible levels and
width (`sec:initial`, line 343), before any regularity assumption is added. -/
theorem cornerBand_empty_rank_one (I : ToricInput 1)
    (Aamb R Afib Aminus A eps : ℝ) (hfib : FiberEndBound I Aamb R Afib)
    (hR : 0 ≤ R) (hlevels : Afib < Aminus) (hwidth : eps < A - Aminus) :
    CornerBand I R A eps = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hnorm : ‖W I y‖ ≤ R := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    rw [← Complex.normSq_eq_norm_sq]
    linarith [hy.2.2.2]
  have hphi := phi0_lt_fiberBound_rank_one I Aamb R Afib hfib y hnorm
  linarith [hy.1]

/-- The rank-one prescribed ribbon is the whole far fiber, for every valid
fiber bound and every allowed inner level (`sec:initial`, line 343). This is
an equality of literal sets, not an assumed completion marking. -/
theorem initialRibbon_eq_fullFiber_rank_one (I : ToricInput 1)
    (Aamb R Afib Aminus : ℝ) (hfib : FiberEndBound I Aamb R Afib)
    (hR : 0 ≤ R) (hlevels : Afib < Aminus) :
    InitialRibbon I R Aminus = FullFiber I R := by
  apply Set.Subset.antisymm (initialRibbon_subset_fullFiber I R Aminus)
  intro y hy
  refine ⟨hy, ?_⟩
  have hnorm : ‖W I y‖ ≤ R := by
    change W I y = (R : ℂ) at hy
    simp only [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, le_refl]
  exact (phi0_lt_fiberBound_rank_one I Aamb R Afib hfib y hnorm).le.trans hlevels.le

/-- The width inequality already excludes the prescribed ribbon from the
corner band; no geometric regularity or existence hypothesis is needed. -/
theorem cornerBand_disjoint_initialRibbon (I : ToricInput n)
    (R Aminus A eps : ℝ) (hwidth : eps < A - Aminus) :
    Disjoint (CornerBand I R A eps) (InitialRibbon I R Aminus) := by
  rw [Set.disjoint_left]
  intro y hband hribbon
  have hband' : -eps < phi0 y - A := hband.1
  have hribbon' : phi0 y ≤ Aminus := hribbon.2
  linarith

end FsFltz
