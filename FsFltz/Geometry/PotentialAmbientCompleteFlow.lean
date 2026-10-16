import FsFltz.Geometry.PotentialFiberCompleteFlowNative
import FsFltz.Analysis.OriginalFieldGrowth

/-!
# Complete ambient flow for the retained positive-Hessian potential

Source: `geometric-part-fsf-proof.tex`, `eq:holoexhaustion`, lines 716–723,
and `lem:originalends`, lines 798–818. The actual native rank-two field
has a proper shifted potential exhaustion with a linear derivative bound.
The proper-exhaustion continuation theorem constructs its all-real flow.
This is the holomorphic ambient, before the nonholomorphic tailoring step.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff ComplexConjugate
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The homogeneous rank-two numerator has an exhaustion bound independent
of the nonnegative base coefficient. -/
theorem rankTwo_potential_exhaustion_abs_bound {r a D K : ℝ} {f b : ℂ}
    (hr : 0 ≤ r) (ha : 0 < a) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hb : ‖b‖ ≤ Real.sqrt r * Real.sqrt a)
    (hf : ‖f‖ ≤ D * Real.sqrt a) :
    |(r + K * (r * a - Complex.normSq b + (conj f * b).re / 2)) / (1 + K * a)| ≤
      (1 + D / 2) * (1 + r) := by
  have hsqr := Real.sq_sqrt hr
  have hsqa := Real.sq_sqrt ha.le
  have hprod : 0 ≤ Real.sqrt r * Real.sqrt a := by positivity
  have hbsq : Complex.normSq b ≤ r * a := by
    rw [Complex.normSq_eq_norm_sq]
    have he : (Real.sqrt r * Real.sqrt a) ^ 2 = r * a := by
      rw [mul_pow, hsqr, hsqa]
    nlinarith [norm_nonneg b]
  have hsqrt : Real.sqrt r ≤ 1 + r := by nlinarith [Real.sqrt_nonneg r]
  have hcross : |(conj f * b).re| ≤ D * (1 + r) * a := by
    calc
      _ ≤ ‖conj f * b‖ := Complex.abs_re_le_norm _
      _ = ‖f‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ (D * Real.sqrt a) * (Real.sqrt r * Real.sqrt a) :=
        mul_le_mul hf hb (norm_nonneg b) (by positivity)
      _ = D * Real.sqrt r * a := by
        calc
          _ = D * Real.sqrt r * (Real.sqrt a) ^ 2 := by ring
          _ = _ := by rw [hsqa]
      _ ≤ D * (1 + r) * a := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hD) ha.le
  have hden : 0 < 1 + K * a := by positivity
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  apply abs_le.mpr
  obtain ⟨hclo, hchi⟩ := abs_le.mp hcross
  have hbase : 0 ≤ r * a - Complex.normSq b := sub_nonneg.mpr hbsq
  have hbasehi : r * a - Complex.normSq b ≤ r * a :=
    sub_le_self _ (Complex.normSq_nonneg b)
  have hlo := mul_le_mul_of_nonneg_left hclo hK
  have hhi := mul_le_mul_of_nonneg_left hchi hK
  have hbhi := mul_le_mul_of_nonneg_left hbasehi hK
  have hbnonneg := mul_nonneg hK hbase
  constructor <;> nlinarith

section Potential

variable {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K)

include hφ hc hlower hK

/-- Actual positive Hessians and holomorphic differentials make every
nonnegative rank-two update symplectic on the whole quotient ambient. -/
theorem isSymplecticOn_potential_W_ambient :
    (lgManifold n).IsSymplecticOn
      ((lgManifold n).exteriorDerivative
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K)) univ := by
  apply (lgManifold n).isSymplecticOn_exteriorDerivative_rankTwoPrimitive_of_nonneg
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I)
    (fun y _ => nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) ?_ hK
  intro y _
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [planePairing_W_potentialHessian hφ hc hlower I x]
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  have hp : ∀ v, 0 ≤ inner ℝ (H v) v :=
    fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)
  exact add_nonneg (inverseMetricSq_nonneg H hp _) (inverseMetricSq_nonneg H hp _)

include hEnd1 hEnds hhom hU hupper hL hend

/-- The actual holomorphic ambient primitive has a jointly smooth flow in
both time directions, for every finite nonnegative base coefficient. -/
theorem exists_potential_W_ambientCompleteLiouvilleFlow :
    Nonempty (CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K))) := by
  let M := lgManifold n
  let μ := M.rankTwoPrimitive (lambdaPotentialForm φ) (W I) K
  let Z := M.liouvilleVector μ
  have hμ := M.isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
    (contMDiff_W_lgManifold I) K
  have hsymp := isSymplecticOn_potential_W_ambient hφ hc hlower I hK
  have hZ : M.IsSmoothVectorField Z := M.isSmoothVectorField_liouvilleVector μ hμ
    (fun y => hsymp.2.2 y (mem_univ _))
  obtain ⟨d, hd, Ldom, hLdom, hdom⟩ :=
    I.coefficientPath_potentialHessian_dominant_lowerBound
      (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) hc hU hlower hupper
  let D : ℝ := (I.vertices.card : ℝ) / d
  have hD : 0 ≤ D := div_nonneg (Nat.cast_nonneg _) hd.le
  let Lbig := max L Ldom
  have hLbig : 0 < Lbig := hL.trans_le (le_max_left _ _)
  obtain ⟨S, hS, hnonneg⟩ := exists_nonnegative_potential_shift
    hφ hEnd1 hEnds hhom hc hlower hL hend
  let ρ₀ : M.Point → ℝ := fun y => φ y.1
  let ρ : M.Point → ℝ := fun y => ρ₀ y + S
  have hρ₀ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ₀ := contMDiff_potentialValue hφ
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ := hρ₀.add contMDiff_const
  have hρnonneg : ∀ y, 0 ≤ ρ y := fun y => hnonneg y.1
  have hderiv : ∀ y v, M.scalarDerivative ρ y v = M.scalarDerivative ρ₀ y v := by
    intro y v
    have hh := mfderiv_add (hρ₀.mdifferentiable (by simp) y)
      (mdifferentiableAt_const (c := S) : MDifferentiableAt
        𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun _ : M.Point => S) y)
    have he := congrArg (fun f : M.Tangent y →L[ℝ] ℝ => f v) hh
    simp only [Pi.add_def, mfderiv_const, add_zero] at he
    exact he
  have hendbound (y : M.Point)
      (hy : Lbig < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖) :
      |M.scalarDerivative ρ y (Z y)| ≤ 2 * (1 + D / 2) * (1 + ρ y) := by
    obtain ⟨x, rfl⟩ := lgCover_surjective n y
    have hx : L < ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ :=
      lt_of_le_of_lt (le_max_left _ _) hy
    have hnorm : Real.sqrt (realSquaredNorm x.1) =
        ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n)))]
      congr 1
      simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
    let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
    let aH := toricInverseMetricSq H I (lgCover x)
    have hsymm : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
      inner_fderiv_gradient_symmetric
        (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
    have hp : ∀ v, 0 ≤ inner ℝ (H v) v :=
      fun v => (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ v)
    have hg : d * maxMonomialMagnitude I (lgCover x) ≤ Real.sqrt aH := by
      have hh := hdom 0 (by constructor <;> norm_num) (lgCover x)
        (show Ldom ≤ Real.sqrt (realSquaredNorm (lgCover x).1) by
          rw [lgCover, hnorm]; exact (le_max_right _ _).trans hy.le)
      simpa only [ToricInput.alongCoefficientPath_zero, aH, H, lgCover] using hh
    have haH : 0 < aH := Real.sqrt_pos.mp
      ((mul_pos hd (I.maxMonomialMagnitude_pos (lgCover x))).trans_le hg)
    have hf : ‖W I (lgCover x)‖ ≤ D * Real.sqrt aH := by
      calc
        _ ≤ (I.vertices.card : ℝ) * maxMonomialMagnitude I (lgCover x) :=
          norm_W_le_card_mul_maxMonomialMagnitude I (lgCover x)
        _ = D * (d * maxMonomialMagnitude I (lgCover x)) := by dsimp [D]; field_simp
        _ ≤ D * Real.sqrt aH := mul_le_mul_of_nonneg_left hg hD
    have he := metricRadialSq_potential_eq_two_mul hEnd1 hEnds hhom hc hlower hL hend x.1 hx
    have hb := norm_b0_le_metric_radius_mul_sqrt_toricInverseMetricSq H hsymm hp I (lgCover x)
    have hid := (liouville_identities_potential_W_on_homogeneous_end
      hφ hc hlower hEnds hhom hL hend I x hx hK).2
    rw [hderiv]
    change |(lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x)
      ((lgManifold n).liouvilleVector
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) (lgCover x))| ≤ _
    rw [hid]
    have hbound := rankTwo_potential_exhaustion_abs_bound (hp (WithLp.toLp 2 x.1))
      haH hD hK hb hf
    change |(metricRadialSq H x.1 + K * potentialMetricMargin H I (lgCover x)) / (1 + K * aH)| ≤ _ at hbound
    apply hbound.trans
    change (1 + D / 2) * (1 + metricRadialSq H x.1) ≤ _
    change metricRadialSq H x.1 = 2 * φ x.1 at he
    rw [he]
    rw [mul_comm 2 (1 + D / 2), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 + D / 2)
    dsimp [ρ, ρ₀, lgCover]
    linarith
  obtain ⟨B, hB⟩ := (isCompact_phi0_sublevel (n := n) (Lbig ^ 2 / 2)
    (by positivity)).exists_bound_of_continuousOn
      (M.continuous_scalarDerivative_vectorField hZ ρ hρ).continuousOn
  let C : ℝ := max B (2 * (1 + D / 2))
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hbound : ∀ y, |M.scalarDerivative ρ y (Z y)| ≤ C * (1 + ρ y) := by
    intro y
    by_cases hy : Lbig < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖
    · exact (hendbound y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by linarith [hρnonneg y]))
    · have hs := (sq_le_sq₀ (norm_nonneg _) hLbig.le).mpr (le_of_not_gt hy)
      have hx : phi0 y ≤ Lbig ^ 2 / 2 := by
        have hs' : realSquaredNorm y.1 ≤ Lbig ^ 2 := by
          simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using hs
        change realSquaredNorm y.1 / 2 ≤ Lbig ^ 2 / 2
        linarith
      have hb : |M.scalarDerivative ρ y (Z y)| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB y hx
      exact hb.trans ((le_max_left _ _).trans
        (le_mul_of_one_le_right hC.le (by linarith [hρnonneg y])))
  apply M.exists_completeFlow_of_proper_exhaustion Z hZ ρ hρ hρnonneg _ hC hbound
  intro A _
  have hset : {y : M.Point | ρ y ≤ A} = {y : LGSpace n | φ y.1 ≤ A - S} := by
    ext y
    change φ y.1 + S ≤ A ↔ φ y.1 ≤ A - S
    constructor <;> intro h <;> linarith
  rw [hset]
  exact isCompact_potential_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend (A - S)

/-- The retained potential and literal polynomial determine the primitive,
native field, contraction equation, and complete ambient flow. -/
def potential_W_ambientCompletePrimitive :
    CompletePrimitive (lgManifold n)
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) where
  smooth_primitive := (lgManifold n).isSmoothForm_rankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I) K
  symplectic := isSymplecticOn_potential_W_ambient hφ hc hlower I hK
  smooth_field := (lgManifold n).isSmoothVectorField_liouvilleVector _
    ((lgManifold n).isSmoothForm_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I) K)
    (fun y => (isSymplecticOn_potential_W_ambient hφ hc hlower I hK).2.2 y (mem_univ _))
  contraction := fun y => (lgManifold n).liouvilleVector_contraction _ y
    ((lgManifold n).liouvilleEquation_exists _ y
      ((isSymplecticOn_potential_W_ambient hφ hc hlower I hK).2.2 y (mem_univ _)))
  completeFlow := Classical.choice (exists_potential_W_ambientCompleteLiouvilleFlow
    hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK)

end Potential
end FsFltz.Geometry
