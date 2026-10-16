import FsFltz.Geometry.TailoringRoundedBase
import FsFltz.Analysis.OriginalRoundedBoundary

/-!
# Uniform native rounded domains for the actual tailoring family

Source: `geometric-part-fsf-proof.tex`, `eq:normalizedrounding`, lines
1254–1282. Active profile partials localize to a finite potential annulus
or a fixed collar below the unit base circle. These are finite ambient
estimates; ambient completeness on the entire tailored `Y` is not claimed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set

namespace FsFltz

namespace RoundingProfile

/-- Above the rounded zero level an active first partial can only occur in
the width-two collar of the first face. -/
theorem first_ge_neg_two_eps_of_nonneg_of_partial_pos {eps : ℝ}
    (m : RoundingProfile eps) (heps : 0 < eps) (p : ℝ × ℝ)
    (hp : 0 ≤ m.toFun p) (hfirst : 0 < fderiv ℝ m.toFun p (1, 0)) :
    -2 * eps ≤ p.1 := by
  by_contra h
  have hx : p.1 < -2 * eps := lt_of_not_ge h
  have hmax : -eps ≤ max p.1 p.2 := by linarith [m.upper p]
  have hxy : p.1 ≤ p.2 := by
    by_contra hn
    rw [max_eq_left (le_of_not_ge hn)] at hmax
    linarith
  rw [max_eq_right hxy] at hmax
  have hexact := m.exact_away p (by
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith)
  have hd := m.fderiv_eq_snd_of_eq p (hexact.trans (max_eq_right hxy))
  rw [hd] at hfirst
  norm_num at hfirst

/-- The analogous localization for the second active partial. -/
theorem second_ge_neg_two_eps_of_nonneg_of_partial_pos {eps : ℝ}
    (m : RoundingProfile eps) (heps : 0 < eps) (p : ℝ × ℝ)
    (hp : 0 ≤ m.toFun p) (hsecond : 0 < fderiv ℝ m.toFun p (0, 1)) :
    -2 * eps ≤ p.2 := by
  by_contra h
  have hy : p.2 < -2 * eps := lt_of_not_ge h
  have hmax : -eps ≤ max p.1 p.2 := by linarith [m.upper p]
  have hyx : p.2 ≤ p.1 := by
    by_contra hn
    rw [max_eq_right (le_of_not_ge hn)] at hmax
    linarith
  rw [max_eq_left hyx] at hmax
  have hexact := m.exact_away p (by
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith)
  have hd := m.fderiv_eq_fst_of_eq p (hexact.trans (max_eq_left hyx))
  rw [hd] at hsecond
  norm_num at hsecond

/-- Only active partials need positive input derivatives. The other input
derivative may have either sign because its coefficient is zero. -/
theorem fderiv_pos_of_active {eps : ℝ} (m : RoundingProfile eps)
    (p : ℝ × ℝ) {u v : ℝ}
    (hu : 0 < fderiv ℝ m.toFun p (1, 0) → 0 < u)
    (hv : 0 < fderiv ℝ m.toFun p (0, 1) → 0 < v) :
    0 < fderiv ℝ m.toFun p (u, v) := by
  have hfirst := m.partialFirst_nonneg p
  have hsecond := m.partialSecond_nonneg p
  have hsum := m.partial_sum p
  by_cases hp : 0 < fderiv ℝ m.toFun p (1, 0)
  · by_cases hq : 0 < fderiv ℝ m.toFun p (0, 1)
    · exact m.fderiv_pos p (hu hp) (hv hq)
    have hzero : fderiv ℝ m.toFun p (0, 1) = 0 := le_antisymm (le_of_not_gt hq) hsecond
    rw [m.fderiv_apply, hzero, mul_zero, add_zero]
    exact mul_pos (hu hp) hp
  · have hzero : fderiv ℝ m.toFun p (1, 0) = 0 := le_antisymm (le_of_not_gt hp) hfirst
    have hq : 0 < fderiv ℝ m.toFun p (0, 1) := by linarith
    rw [m.fderiv_apply, hzero, mul_zero, zero_add]
    exact mul_pos (hv hq) hq

end RoundingProfile

open Geometry
variable {n : ℕ}

/-- The exact normalized scalar, retaining the prescribed factor `R²`. -/
def tailoringRoundedDefiningFunction (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β s R A : ℝ) (m : RoundingChoice) (y : LGSpace n) : ℝ :=
  m.profile.toFun (φ y.1 - A, R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1))

def tailoringRoundedDomain (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β s R A : ℝ) (m : RoundingChoice) : Set (LGSpace n) :=
  {y | tailoringRoundedDefiningFunction I φ β s R A m y ≤ 0}

local instance : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts

local instance : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ => contDiff_mul.contDiffOn⟩

theorem contMDiff_tailoringFamily_normSq (I : ToricInput n) (β s : ℝ) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : LGSpace n => Complex.normSq (tailoringFamily I β s y)) := by
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
    (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_tailoringFamily_lgManifold I β s)

theorem contMDiff_tailoringRoundedDefiningFunction (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (β s R A : ℝ) (m : RoundingChoice) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (tailoringRoundedDefiningFunction I φ β s R A m) :=
  m.profile.smooth.contMDiff.comp
    (((contMDiff_potentialValue hφ).sub contMDiff_const).prodMk_space
      (contMDiff_const.mul ((contMDiff_tailoringFamily_normSq I β s).sub contMDiff_const)))

/-- Native chain rule for the literal normalized scalar. -/
theorem scalarDerivative_tailoringRoundedDefiningFunction (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (β s R A : ℝ) (m : RoundingChoice)
    (y : LGSpace n) (v : (lgManifold n).Tangent y) :
    (lgManifold n).scalarDerivative (tailoringRoundedDefiningFunction I φ β s R A m) y v =
      fderiv ℝ m.profile.toFun (φ y.1 - A, R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1))
        ((lgManifold n).scalarDerivative (fun z => φ z.1) y v,
          R ^ 2 * (lgManifold n).scalarDerivative
            (fun z => Complex.normSq (tailoringFamily I β s z)) y v) := by
  change Model (2 * n) at v
  have hp := (contMDiff_potentialValue hφ).mdifferentiableAt (by simp) (x := y)
  have hf := (contMDiff_tailoringFamily_normSq I β s).mdifferentiableAt (by simp) (x := y)
  have hx := hp.hasMFDerivAt.sub (hasMFDerivAt_const (c := A) y)
  have hy := (hf.hasMFDerivAt.sub (hasMFDerivAt_const (c := (1 : ℝ)) y)).const_smul (R ^ 2)
  have hpair : HasMFDerivAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
      (fun z : LGSpace n => (φ z.1 - A, R ^ 2 * (Complex.normSq (tailoringFamily I β s z) - 1))) y
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1 - A) y).prod
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z : LGSpace n => R ^ 2 * (Complex.normSq (tailoringFamily I β s z) - 1)) y)) :=
    ⟨(hx.mdifferentiableAt.prodMk_space hy.mdifferentiableAt).continuousAt,
      hx.mdifferentiableAt.hasMFDerivAt.2.prodMk hy.mdifferentiableAt.hasMFDerivAt.2⟩
  have hm := m.profile.smooth.contMDiff.mdifferentiableAt (by simp)
    (x := (φ y.1 - A, R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1)))
  change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (m.profile.toFun ∘ fun z : LGSpace n =>
        (φ z.1 - A, R ^ 2 * (Complex.normSq (tailoringFamily I β s z) - 1))) y) v = _
  erw [mfderiv_comp_apply y hm hpair.mdifferentiableAt v, mfderiv_eq_fderiv, hpair.mfderiv]
  dsimp only [TangentSpace] at *
  change fderiv ℝ m.profile.toFun _
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => φ z.1 - A) y) v,
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z : LGSpace n => R ^ 2 * (Complex.normSq (tailoringFamily I β s z) - 1)) y) v) = _
  congr 1
  apply Prod.ext
  · have h := congrArg (fun L : Model (2 * n) →L[ℝ] ℝ => L v) hx.mfderiv
    simp only [sub_zero] at h
    convert h using 1
    rfl
  · have h := congrArg (fun L : Model (2 * n) →L[ℝ] ℝ => L v) hy.mfderiv
    simp only [sub_zero, smul_apply, smul_eq_mul] at h
    convert h using 1
    rfl

/-- Rounded carriers lie in the literal cornered domain. -/
theorem tailoringRoundedDomain_subset (I : ToricInput n) (φ : RealSpace n → ℝ)
    (β s A : ℝ) {R : ℝ} (hR : 0 < R) (m : RoundingChoice) :
    tailoringRoundedDomain I φ β s R A m ⊆
      {y : LGSpace n | φ y.1 ≤ A ∧ ‖tailoringFamily I β s y‖ ≤ 1} := by
  intro y hy
  have h := (m.profile.lower (φ y.1 - A,
    R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1))).trans hy
  have hx := (le_max_left _ _).trans h
  have hv := (le_max_right _ _).trans h
  refine ⟨by linarith only [hx], ?_⟩
  have hn : Complex.normSq (tailoringFamily I β s y) ≤ 1 := by
    nlinarith only [hv, sq_pos_of_pos hR]
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (tailoringFamily I β s y)]

/-- Compactness follows from the actual finite potential sublevel. -/
theorem isCompact_tailoringRoundedDomain (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (β s A : ℝ) {R : ℝ} (hR : 0 < R)
    (m : RoundingChoice) (hcompact : IsCompact {y : LGSpace n | φ y.1 ≤ A}) :
    IsCompact (tailoringRoundedDomain I φ β s R A m) :=
  hcompact.of_isClosed_subset
    (isClosed_le (contMDiff_tailoringRoundedDefiningFunction I hφ β s R A m).continuous continuous_const)
    (fun _ hy => (tailoringRoundedDomain_subset I φ β s A hR m hy).1)

/-- The source active-partial argument controls the whole portion of the
outer compact domain at or above the rounded zero level, as required for
finite negative absorption. -/
theorem scalarDerivative_tailoringRoundedDefiningFunction_pos_of_collars
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β s K A : ℝ) {R : ℝ} (hR : 0 < R) (m : RoundingChoice)
    (heps : 0 < m.eps) (hepsA : m.eps ≤ A / 4) (hepsR : m.eps ≤ R ^ 2 / 4)
    (hpotential : ∀ y : LGSpace n, A / 2 ≤ φ y.1 → φ y.1 ≤ A →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y))
    (hbase : ∀ y : LGSpace n, φ y.1 ≤ A → (1 / 2 : ℝ) ≤ ‖tailoringFamily I β s y‖ →
      0 < (lgManifold n).scalarDerivative (fun z => Complex.normSq (tailoringFamily I β s z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y))
    (y : LGSpace n) (hy : φ y.1 ≤ A)
    (hq : 0 ≤ tailoringRoundedDefiningFunction I φ β s R A m y) :
    0 < (lgManifold n).scalarDerivative (tailoringRoundedDefiningFunction I φ β s R A m) y
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
  rw [scalarDerivative_tailoringRoundedDefiningFunction I hφ]
  apply m.profile.fderiv_pos_of_active
  · intro hp
    have hc := m.profile.first_ge_neg_two_eps_of_nonneg_of_partial_pos heps _ hq hp
    apply hpotential y _ hy
    change -2 * m.eps ≤ φ y.1 - A at hc
    linarith only [hc, hepsA]
  · intro hp
    have hc := m.profile.second_ge_neg_two_eps_of_nonneg_of_partial_pos heps _ hq hp
    apply mul_pos (sq_pos_of_pos hR) (hbase y hy _)
    change -2 * m.eps ≤ R ^ 2 * (Complex.normSq (tailoringFamily I β s y) - 1) at hc
    rw [Complex.normSq_eq_norm_sq] at hc
    have hn : (1 / 2 : ℝ) ≤ ‖tailoringFamily I β s y‖ ^ 2 := by
      nlinarith only [hc, hepsR, sq_pos_of_pos hR]
    nlinarith only [hn, norm_nonneg (tailoringFamily I β s y)]

/-- The entire potential collar from half the outer level to the outer
level has a positive actual Liouville derivative. This follows directly
from the proved finite-band estimate after excluding the fixed compact
exceptional cylinder; no collar outwardness is supplied as an input. -/
theorem tailoringFamily_exists_uniform_finite_potential_annulus_outwardness
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, D ^ 2 * β ^ 2 / 4 ≤ φ y.1 → φ y.1 ≤ D ^ 2 * β ^ 2 / 2 →
      ∀ K : ℝ, 0 ≤ K →
        0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
  obtain ⟨Bband, _hBband, hband⟩ := tailoringFamily_exists_uniform_finite_band_outwardness
    I hφ hc hU hlower hupper hEnd hhom hREnd heq (by positivity : 0 < D / 2) hD
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (REnd ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bφ := (2 * max V 0 + 2) / D
  let β₀ := max 1 (max Bband Bφ)
  refine ⟨β₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ s hs y hlo hhi K hK
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβband : Bband ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβφ : Bφ ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hDβ : 0 < D * β := mul_pos hD (zero_lt_one.trans_le hβ₁)
  have hlevel : V < D ^ 2 * β ^ 2 / 4 := by
    have hbound : 2 * max V 0 + 2 ≤ D * β := by
      have h := (div_le_iff₀ hD).mp hβφ
      simpa only [mul_comm] using h
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 2) hbound 2
    nlinarith only [hsquare, le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  have hyEnd : REnd < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra h
    have hnorm := le_of_not_gt h
    have hsq : realSquaredNorm y.1 ≤ REnd ^ 2 := by
      simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using
        (sq_le_sq₀ (norm_nonneg _) hREnd.le).mpr hnorm
    have hmem : y ∈ {z : LGSpace n | phi0 z ≤ REnd ^ 2 / 2} := by
      change realSquaredNorm y.1 / 2 ≤ REnd ^ 2 / 2
      linarith
    have hbound := hV (mem_image_of_mem (fun z : LGSpace n => φ z.1) hmem)
    exact (not_le_of_gt hlevel) (hlo.trans hbound)
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  change D ^ 2 * β ^ 2 / 4 ≤ φ x.1 at hlo
  change φ x.1 ≤ D ^ 2 * β ^ 2 / 2 at hhi
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  have he := metricRadialSq_potential_eq_two_mul hEnd1 hEnd hhom hc hlower hREnd heq x.1 hyEnd
  have hrnonneg := Real.sqrt_nonneg (metricRadialSq H x.1)
  have hrSq : Real.sqrt (metricRadialSq H x.1) ^ 2 = 2 * φ x.1 := by
    rw [he, Real.sq_sqrt]
    linarith only [hlo, sq_nonneg D, sq_nonneg β, mul_nonneg (sq_nonneg D) (sq_nonneg β)]
  have hrlo : D / 2 * β ≤ Real.sqrt (metricRadialSq H x.1) := by
    nlinarith only [hlo, hrSq, hrnonneg, hDβ, sq_nonneg (D * β)]
  have hrhi : Real.sqrt (metricRadialSq H x.1) ≤ D * β := by
    nlinarith only [hhi, hrSq, hrnonneg, hDβ]
  exact (hband β hβband s hs x hrlo hrhi
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x))).2 K hK

/-- One actual normalized coefficient and one actual width work for all
tailoring parameters and every admissible profile below that width. The
outward derivative is proved on the entire compact exterior portion,
not merely on the rounded boundary. -/
theorem tailoringFamily_exists_uniform_rounded_outwardness
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K ≥ Kstar, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, φ y.1 ≤ D ^ 2 * β ^ 2 / 2 →
      0 ≤ tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m y →
      0 < (lgManifold n).scalarDerivative
        (tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
  obtain ⟨Ba, _hBa, hpot⟩ := tailoringFamily_exists_uniform_finite_potential_annulus_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  obtain ⟨Bb, _hBb, hbase⟩ := tailoringFamily_exists_uniform_compact_base_outwardness_above
    I hφ hc hU hlower hupper (by norm_num : (0 : ℝ) < 1 / 2)
  let β₀ := max 1 (max Ba Bb)
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβa : Ba ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβb : Bb ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  let A := D ^ 2 * β ^ 2 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hcompact := isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hREnd heq A
  obtain ⟨Kstar, hKstar, hb⟩ := hbase β hβb {y : LGSpace n | φ y.1 ≤ A} hcompact
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  let δ := min (A / 4) (min (R ^ 2 / 4) ((A - Aminus) / 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA : δ ≤ A / 4 := min_le_left _ _
  have hδR : δ ≤ R ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδgap : δ < A - Aminus := by
    have hδle : δ ≤ (A - Aminus) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    change Aminus < A at hgap
    linarith only [hδle, hgap]
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK s hs y hy hq
  apply scalarDerivative_tailoringRoundedDefiningFunction_pos_of_collars I hφ β s K A hR m hm
    (hmd.trans hδA) (hmd.trans hδR) _ _ y hy hq
  · intro z hlo hhi
    exact hpot β hβa s hs z (by dsimp [A] at hlo; linarith only [hlo]) hhi K
      (hKstar.le.trans hK)
  · intro z hz hn
    exact hb K hK s hs z hz hn

/-- Construct the actual rounded native Liouville domains using the
uniformly produced coefficient and width. Their carrier, native primitive
and field are the literal normalized ones. -/
theorem tailoringFamily_exists_uniform_rounded_domains
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K ≥ Kstar, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ E : LiouvilleDomain (2 * n), E.domain.extension = lgManifold n ∧
        HEq E.domain.carrier (tailoringRoundedDomain I φ β s R (D ^ 2 * β ^ 2 / 2) m) ∧
        HEq E.liouville.primitive ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) ∧
        HEq E.liouville.field ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K)) ∧
        HEq (frontier E.domain.carrier)
          {y : LGSpace n | tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m y = 0} := by
  obtain ⟨Bo, _hBo, ho⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  obtain ⟨Bω, _hBω, hω⟩ := tailoringFamily_exists_uniform_symplectic I hφ hc hU hlower hupper
  let β₀ := max 1 (max Bo Bω)
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβo : Bo ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβω : Bω ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨Kstar, hKstar, hout⟩ := ho β hβo
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK s hs
  let A := D ^ 2 * β ^ 2 / 2
  let ρ := tailoringRoundedDefiningFunction I φ β s R A m
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K
  have hρ := contMDiff_tailoringRoundedDefiningFunction I hφ β s R A m
  have hcompact := isCompact_tailoringRoundedDomain I hφ β s A hR m
    (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hREnd heq A)
  have hα := (lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
    (contMDiff_tailoringFamily_lgManifold I β s) K
  have hαω := hω β hβω s hs K (hKstar.le.trans hK)
  have hp : ∀ y : (lgManifold n).Point, ρ y = 0 →
      0 < (lgManifold n).scalarDerivative ρ y ((lgManifold n).liouvilleVector α y) := by
    intro y hy
    exact hout m hm hmd K hK s hs y
      (tailoringRoundedDomain_subset I φ β s A hR m (show y ∈ tailoringRoundedDomain I φ β s R A m from hy.le)).1
      hy.ge
  let E := regularSublevelLiouvilleDomain (lgManifold n) ρ hρ hcompact α hα hαω hp
  exact ⟨E, rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    heq_of_eq (regularSublevelLiouvilleDomain_frontier (lgManifold n) ρ hρ hcompact α hα hαω hp)⟩

end FsFltz
