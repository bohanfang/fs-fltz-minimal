import FsFltz.Analysis.OriginalRounding
import FsFltz.Analysis.RoundingProfileBoundary

/-!
# Native defining function of every original rounded domain

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 909–930;
`geoemtric-part-fsf.tex`, `eq:initialpair`, lines 302–307 and
`def:rounding`, lines 309–326. Smoothness, compactness and native outward
derivatives refer to the literal profile-defined scalar and domain.
Manifold-with-boundary and contact realization are separate foundations.
-/

noncomputable section

open scoped Manifold ContDiff BigOperators

namespace FsFltz

variable {n : ℕ}

/-- The literal defining scalar of `RoundedDomain`, source proof line 911. -/
def roundedDefiningFunction (I : ToricInput n) (R A : ℝ) (m : RoundingChoice)
    (y : LGSpace n) : ℝ :=
  m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2)

/-- Linearity expands the profile differential in the two coordinate directions. -/
theorem RoundingProfile.fderiv_apply {eps : ℝ} (m : RoundingProfile eps)
    (xy : ℝ × ℝ) (u v : ℝ) :
    fderiv ℝ m.toFun xy (u, v) =
      u * fderiv ℝ m.toFun xy (1, 0) + v * fderiv ℝ m.toFun xy (0, 1) := by
  have huv : (u, v) = u • ((1, 0) : ℝ × ℝ) + v • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [huv, map_add, map_smul, map_smul]
  rfl

/-- A convex combination with the prescribed nonnegative profile partials
is strictly positive whenever both input derivatives are strictly positive. -/
theorem RoundingProfile.fderiv_pos {eps : ℝ} (m : RoundingProfile eps)
    (xy : ℝ × ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 < fderiv ℝ m.toFun xy (u, v) := by
  rw [m.fderiv_apply]
  have hp := m.partialFirst_nonneg xy
  have hq := m.partialSecond_nonneg xy
  have hsum := m.partial_sum xy
  by_cases hfirst : 0 < fderiv ℝ m.toFun xy (1, 0)
  · exact add_pos_of_pos_of_nonneg (mul_pos hu hfirst) (mul_nonneg hv.le hq)
  · have hsecond : 0 < fderiv ℝ m.toFun xy (0, 1) := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg hu.le hp) (mul_pos hv hsecond)

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

local instance roundedRealContMDiffMul : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ => contDiff_mul.contDiffOn⟩

local instance roundedLGChartedSpace : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

theorem contMDiff_original_phi0 :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (phi0 : (lgManifold n).Point → ℝ) := by
  unfold phi0 realSquaredNorm
  exact (ContMDiff.sum (fun j _ => (contMDiff_lgLogCoordinate j).pow 2)).div_const 2

theorem contMDiff_original_absWSq (I : ToricInput n) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => Complex.normSq (W I y)) := by
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
    (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_W_lgManifold I)

/-- Every allowed smooth profile produces a native smooth defining scalar.
This is the scalar in `prop:allinitial`, lines 910–919. -/
theorem contMDiff_roundedDefiningFunction (I : ToricInput n) (R A : ℝ)
    (m : RoundingChoice) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (roundedDefiningFunction I R A m : (lgManifold n).Point → ℝ) :=
  m.profile.smooth.contMDiff.comp
    ((contMDiff_original_phi0.sub contMDiff_const).prodMk_space
      ((contMDiff_original_absWSq I).sub contMDiff_const))

set_option backward.isDefEq.respectTransparency false in
/-- Native chain rule for the exact defining scalar, on every tangent vector.
No prescribed derivative or vector-field identity is supplied as an input. -/
theorem differentialCovector_roundedDefiningFunction (I : ToricInput n)
    (R A : ℝ) (m : RoundingChoice) (y : (lgManifold n).Point)
    (v : (lgManifold n).Tangent y) :
    differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y v =
      fderiv ℝ m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
        (differentialCovector (lgManifold n) phi0 y v,
          differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y v) := by
  change LGSpace n at y
  change Model (2 * n) at v
  have hp := contMDiff_original_phi0.mdifferentiable (by simp) y
  have hw := (contMDiff_original_absWSq I).mdifferentiable (by simp) y
  have hp' := hp.sub (mdifferentiableAt_const (c := A))
  have hw' := hw.sub (mdifferentiableAt_const (c := R ^ 2))
  have hm := m.profile.smooth.contMDiff.mdifferentiable (by simp)
    (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
  have hpair : HasMFDerivAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
      (fun z => (phi0 z - A, Complex.normSq (W I z) - R ^ 2)) y
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z => phi0 z - A) y).prod
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z => Complex.normSq (W I z) - R ^ 2) y)) :=
    ⟨(hp'.prodMk_space hw').continuousAt, hp'.hasMFDerivAt.2.prodMk hw'.hasMFDerivAt.2⟩
  change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (m.profile.toFun ∘ fun z : LGSpace n =>
        (phi0 z - A, Complex.normSq (W I z) - R ^ 2)) y) v =
    fderiv ℝ m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) phi0 y) v,
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z : LGSpace n => Complex.normSq (W I z)) y) v)
  erw [mfderiv_comp_apply y hm (hp'.prodMk_space hw') v, mfderiv_eq_fderiv,
    hpair.mfderiv, mfderiv_sub hp mdifferentiableAt_const,
    mfderiv_sub hw mdifferentiableAt_const]
  simp
  rfl

/-- The literal rounded domain is compact: its smooth defining function
gives a closed sublevel contained in the compact original potential sublevel. -/
theorem isCompact_roundedDomain (I : ToricInput n) (R A : ℝ)
    (m : RoundingChoice) : IsCompact (RoundedDomain I R A m) := by
  have hclosed : IsClosed (RoundedDomain I R A m) :=
    isClosed_le (contMDiff_roundedDefiningFunction I R A m).continuous continuous_const
  apply (isCompact_phi0_sublevel (max A 0) (le_max_right _ _)).of_isClosed_subset hclosed
  intro y hy
  have hlow := m.profile.lower (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
  have hh := (le_max_left (phi0 y - A) (Complex.normSq (W I y) - R ^ 2)).trans
    (hlow.trans hy)
  change phi0 y ≤ max A 0
  have hphi : phi0 y ≤ A := by linarith
  exact hphi.trans (le_max_left _ _)

/-- Every admissible original profile has a strictly outward native
Liouville derivative on its whole zero level, including the flat junctions.
Source: `prop:allinitial`, proof manuscript lines 910–919. -/
theorem differentialCovector_roundedDefiningFunction_originalLiouville_pos
    (I : ToricInput n) {Aamb R Afib K Aminus A : ℝ}
    (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (y : (lgManifold n).Point) (hz : roundedDefiningFunction I R A m y = 0) :
    0 < differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y
      ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
  have hKnonneg : 0 ≤ K :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) ((one_le_K0 I R hset.1 hset.2).trans hK)
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  let p : ℝ × ℝ := (phi0 y - A, Complex.normSq (W I y) - R ^ 2)
  have hp : m.profile.toFun p = 0 := hz
  have hlower : max p.1 p.2 ≤ 0 := by rw [← hp]; exact m.profile.lower p
  have hx : p.1 ≤ 0 := (le_max_left _ _).trans hlower
  have hy : p.2 ≤ 0 := (le_max_right _ _).trans hlower
  have hbase : p.2 = 0 →
      0 < differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y) := by
    intro hzero
    have hnorm : ‖W I y‖ = R := by
      change Complex.normSq (W I y) - R ^ 2 = 0 at hzero
      rw [Complex.normSq_eq_norm_sq] at hzero
      nlinarith [norm_nonneg (W I y)]
    have hphi := phi0_gt_of_far_value I Aamb R
      (sublevelMaximumAttained I Aamb hamb.1.le)
      ((le_max_right _ _).trans_lt hR) y hnorm.ge
    exact differentialCovector_absWSq_originalLiouville_pos I hRpos hset hK y
      hnorm.ge (hamb.2 y hphi.le).1
  rw [differentialCovector_roundedDefiningFunction]
  by_cases hxp : -m.eps < p.1
  · by_cases hyp : -m.eps < p.2
    · have hband : y ∈ CornerBand I R A m.eps := ⟨hxp, hx, hyp, hy⟩
      apply m.profile.fderiv_pos p
      · apply differentialCovector_phi0_originalLiouville_pos I hKnonneg hamb y
        have hw := hadmiss.2.1
        have hf := hfib.1
        change -m.eps < phi0 y - A at hxp
        linarith
      · exact (hadmiss.2.2 y hband).1
    · have hfirst : p.1 = 0 :=
        m.profile.first_eq_zero_of_zero_of_second_le_neg_eps hadmiss.1 p hp hx
          (le_of_not_gt hyp)
      have hm : m.profile.toFun p = p.1 := hp.trans hfirst.symm
      rw [m.profile.fderiv_eq_fst_of_eq p hm]
      change 0 < differentialCovector (lgManifold n) phi0 y
        ((lgManifold n).liouvilleVector (lambdaKForm I K) y)
      apply differentialCovector_phi0_originalLiouville_pos I hKnonneg hamb y
      change phi0 y - A = 0 at hfirst
      have hw := hadmiss.2.1
      have hf := hfib.1
      linarith
  · have hsecond : p.2 = 0 :=
      m.profile.second_eq_zero_of_zero_of_first_le_neg_eps hadmiss.1 p hp
        (le_of_not_gt hxp) hy
    have hm : m.profile.toFun p = p.2 := hp.trans hsecond.symm
    rw [m.profile.fderiv_eq_snd_of_eq p hm]
    exact hbase hsecond

/-- The zero level is genuinely regular in the native manifold: its actual
differential is surjective. This is the input to the regular-sublevel
manifold-with-boundary construction, rather than an assumed boundary atlas.
Source: `prop:allinitial`, proof manuscript lines 915–919. -/
theorem roundedDefiningFunction_zeroLevel_regular (I : ToricInput n)
    {Aamb R Afib K Aminus A : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hset : RatioSetWellDefined I R) (hK : K0 I R ≤ K)
    (hfib : FiberEndBound I Aamb R Afib) (hlevels : Afib < Aminus)
    (m : RoundingChoice) (hadmiss : GeometricAdmissibleRounding I R K Aminus A m)
    (y : (lgManifold n).Point) (hz : roundedDefiningFunction I R A m y = 0) :
    Function.Surjective
      (differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y) := by
  let L := differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y
  let Z := (lgManifold n).liouvilleVector (lambdaKForm I K) y
  have hpos : 0 < L Z :=
    differentialCovector_roundedDefiningFunction_originalLiouville_pos I
      hamb hR hset hK hfib hlevels m hadmiss y hz
  intro r
  refine ⟨(r / L Z) • Z, ?_⟩
  change L ((r / L Z) • Z) = r
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ r hpos.ne'

/-- The whole literal zero level is compact, including all flat junctions
of an arbitrary admissible profile. -/
theorem isCompact_roundedDefiningFunction_zeroLevel (I : ToricInput n)
    (R A : ℝ) (m : RoundingChoice) :
    IsCompact {y : LGSpace n | roundedDefiningFunction I R A m y = 0} := by
  apply (isCompact_roundedDomain I R A m).of_isClosed_subset
  · exact isClosed_eq (contMDiff_roundedDefiningFunction I R A m).continuous continuous_const
  · intro y hy
    exact hy.le

/-- An actual open neighborhood of the entire prescribed ribbon is left
unchanged by every allowed rounding profile. On it the defining scalar is
literally the base-face scalar, rather than merely sharing its zero set.
Source: `prop:allinitial`, proof manuscript lines 923–924. -/
theorem exists_unchanged_initialRibbon_neighborhood (I : ToricInput n)
    (R Aminus A : ℝ) (m : RoundingChoice)
    (hpos : 0 < m.eps) (hwidth : m.eps < A - Aminus) :
    ∃ U : Set (LGSpace n), IsOpen U ∧ InitialRibbon I R Aminus ⊆ U ∧
      Set.EqOn (roundedDefiningFunction I R A m)
        (fun y => Complex.normSq (W I y) - R ^ 2) U := by
  let U : Set (LGSpace n) := {y | m.eps <
    (Complex.normSq (W I y) - R ^ 2) - (phi0 y - A)}
  have hU : IsOpen U := isOpen_lt continuous_const
    (((contMDiff_original_absWSq I).continuous.sub continuous_const).sub
      (continuous_phi0.sub continuous_const))
  refine ⟨U, hU, ?_, ?_⟩
  · intro y hy
    have hzero : Complex.normSq (W I y) - R ^ 2 = 0 := by
      rw [hy.1, Complex.normSq_ofReal]
      ring
    change m.eps < (Complex.normSq (W I y) - R ^ 2) - (phi0 y - A)
    rw [hzero]
    linarith [hy.2]
  · intro y hy
    change m.eps < (Complex.normSq (W I y) - R ^ 2) - (phi0 y - A) at hy
    unfold roundedDefiningFunction
    rw [m.profile.exact_away]
    · apply max_eq_right
      linarith
    · have hh := neg_le_abs ((phi0 y - A) - (Complex.normSq (W I y) - R ^ 2))
      linarith

/-- On the full prescribed ribbon the defining scalar has exactly the
unchanged base-face covector, for every allowed profile. This strengthens
the existing literal ribbon zero-level statement without changing the set.
Source: `prop:allinitial`, lines 923–926; target `eq:initialpair`, 302–307. -/
theorem differentialCovector_roundedDefiningFunction_initialRibbon
    (I : ToricInput n) (R Aminus A : ℝ) (m : RoundingChoice)
    (hpos : 0 < m.eps) (hwidth : m.eps < A - Aminus)
    (y : (lgManifold n).Point) (hy : y ∈ InitialRibbon I R Aminus) :
    differentialCovector (lgManifold n) (roundedDefiningFunction I R A m) y =
      differentialCovector (lgManifold n) (fun x => Complex.normSq (W I x)) y := by
  ext v
  rw [differentialCovector_roundedDefiningFunction]
  have hzero : Complex.normSq (W I y) - R ^ 2 = 0 := by
    rw [hy.1, Complex.normSq_ofReal]
    ring
  have hp := initialRibbon_profile_eq_zero I R Aminus A m hpos hwidth y hy
  have hm : m.profile.toFun (phi0 y - A, Complex.normSq (W I y) - R ^ 2) =
      (phi0 y - A, Complex.normSq (W I y) - R ^ 2).2 := hp.trans hzero.symm
  rw [m.profile.fderiv_eq_snd_of_eq _ hm]
  rfl

end FsFltz.Geometry
