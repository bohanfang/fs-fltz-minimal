import FsFltz.Analysis.OriginalFieldGrowth
import FsFltz.Geometry.CollarSmoothEvolution
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Geometry.LinearGrowthCompleteFlow
import FsFltz.Geometry.FixedAmbient

/-!
# Complete smooth flow of the original Liouville field

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 798–812;
`geoemtric-part-fsf.tex`, `thm:target`, G1, lines 356–359, and `sec:lean`,
lines 805–814. The vector field here is the actual original field: its lift
is the prescribed inverse-system solution and its pushforward is already
identified with the Liouville vector of `lambdaKForm`.

Global smoothness and linear growth are proved for this lift, including its
critical points. Generic linear-growth continuation produces all-real cover
curves. Their projection, uniqueness and smooth dependence construct the
complete quotient flow. The original primitive is therefore complete;
finite type and the inclusion-induced markings remain separate producers.
-/

noncomputable section
open scoped BigOperators ContDiff Manifold ComplexConjugate
open Set Function Topology

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

/-- The literal original vector field lifted to real logarithmic and angular
coordinates. No real angle is selected on the quotient. -/
def originalLiouvilleCoverField (I : ToricInput n) (K : ℝ) :
    TangentCoordinates n → TangentCoordinates n :=
  fun x => liouvilleCoordinates I K (lgCover x)

private theorem contDiff_monomial_lgCover (c : ℂ) (v : Lattice n) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => monomial c v (lgCover x)) := by
  simp only [lgCover, monomial_angleQuotient, pairing]
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

private theorem contDiff_G_lgCover (I : ToricInput n) (j : Fin n) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => G I (lgCover x) j) := by
  unfold G
  exact ContDiff.sum (fun v _ => (contDiff_monomial_lgCover (I.coeff v) v.val).mul contDiff_const)

private theorem contDiff_a_lgCover (I : ToricInput n) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => a I (lgCover x)) := by
  unfold a
  apply ContDiff.sum
  intro j _
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
    (contDiff_norm_sq ℝ).comp (contDiff_G_lgCover I j)

private theorem contDiff_b0_lgCover (I : ToricInput n) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates n => b0 I (lgCover x)) := by
  unfold b0
  apply ContDiff.sum
  intro j _
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp contDiff_fst)).mul
    (contDiff_G_lgCover I j)

/-- The full cover field is smooth for every nonnegative parameter, even
where `G = 0`; the inverse denominator is everywhere at least one. -/
theorem contDiff_originalLiouvilleCoverField (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K) : ContDiff ℝ ∞ (originalLiouvilleCoverField I K) := by
  have hden : ∀ x : TangentCoordinates n, 1 + K * a I (lgCover x) ≠ 0 := by
    intro x
    have ha := a_nonneg I (lgCover x)
    positivity
  have hgain : ContDiff ℝ ∞ (fun x : TangentCoordinates n => K / (1 + K * a I (lgCover x))) :=
    contDiff_const.div (contDiff_const.add (contDiff_const.mul (contDiff_a_lgCover I))) hden
  have hc (j : Fin n) : ContDiff ℝ ∞ (fun x : TangentCoordinates n =>
      star (G I (lgCover x) j) * (W I (lgCover x) / 2 - b0 I (lgCover x))) :=
    (Complex.conjCLE.contDiff.comp (contDiff_G_lgCover I j)).mul
      ((contDiff_W_lgCover I).div_const 2 |>.sub (contDiff_b0_lgCover I))
  unfold originalLiouvilleCoverField liouvilleCoordinates
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_fst).add
      (hgain.mul (Complex.reCLM.contDiff.comp (hc j)))
  · apply contDiff_pi.mpr
    intro j
    exact hgain.mul (Complex.imCLM.contDiff.comp (hc j))

/-- The cover field is invariant under every period-lattice translation. -/
theorem originalLiouvilleCoverField_periodShift (I : ToricInput n) (K : ℝ)
    (x : TangentCoordinates n) (k : Lattice n) :
    originalLiouvilleCoverField I K (x.1, periodShift x.2 k) =
      originalLiouvilleCoverField I K x := by
  simp only [originalLiouvilleCoverField, lgCover, angleQuotient_periodShift]

private theorem euclidean_radius_le_cover_norm (x : TangentCoordinates n) :
    Real.sqrt (realSquaredNorm x.1) ≤ ((n : ℝ) + 1) * ‖x‖ := by
  have hsum : realSquaredNorm x.1 ≤ (n : ℝ) * ‖x‖ ^ 2 := by
    calc
      realSquaredNorm x.1 ≤ ∑ _j : Fin n, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hj : |x.1 j| ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 j).trans (norm_fst_le x)
        nlinarith [abs_nonneg (x.1 j), sq_abs (x.1 j), norm_nonneg x]
      _ = _ := by simp
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hN : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hmul := mul_le_mul_of_nonneg_right hN (sq_nonneg ‖x‖)
  nlinarith

/-- The already proved original growth estimate supplies the standard
linear-growth hypothesis for all of Euclidean cover space. -/
theorem exists_originalLiouvilleCoverField_linear_growth (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : TangentCoordinates n,
      ‖originalLiouvilleCoverField I K x‖ ≤ C * (1 + ‖x‖) := by
  obtain ⟨C, hC, hbound⟩ := I.exists_liouvilleCoordinates_linear_growth hK
  refine ⟨C * ((n : ℝ) + 1), by positivity, ?_⟩
  intro x
  have hr := euclidean_radius_le_cover_norm x
  have hN := Nat.cast_nonneg (α := ℝ) n
  calc
    ‖originalLiouvilleCoverField I K x‖ ≤ C * (1 + Real.sqrt (realSquaredNorm x.1)) :=
      hbound (lgCover x)
    _ ≤ C * (1 + ((n : ℝ) + 1) * ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ ≤ (C * ((n : ℝ) + 1)) * (1 + ‖x‖) := by nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- Every genuine cover orbit projects to an integral curve of the actual
original quotient field. This uses the proved quotient tangent identity. -/
theorem isMIntegralCurve_lgCover_originalLiouville {I : ToricInput n} {K : ℝ}
    (hK : 0 ≤ K) {γ : ℝ → TangentCoordinates n}
    (hγ : ∀ t, HasDerivAt γ (originalLiouvilleCoverField I K (γ t)) t) :
    IsMIntegralCurve (lgCover ∘ γ)
      ((lgManifold n).liouvilleVector (lambdaKForm I K)) := by
  intro t
  have hd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentCoordinates n) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (originalLiouvilleCoverField I K (γ t))) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr (hγ t).hasFDerivAt
  have hp := ((contMDiff_lgCover n).mdifferentiable (by simp) (γ t)).hasMFDerivAt.comp t hd
  apply hp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, comp_apply, liouvilleVector_lambdaKForm_lgCover I hK,
    originalLiouvilleCoverField, lgCoverTangent]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_completeLiouvilleFlow_of_globalIntegralCurves {d : ℕ}
    (M : SmoothManifold d) (Z : (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothVectorField Z)
    (hglobal : ∀ x : M.Point, ∃ γ : ℝ → M.Point, γ 0 = x ∧ IsMIntegralCurve γ Z) :
    Nonempty (CompleteLiouvilleFlow M Z) := by
  choose γ hγ₀ hγ using hglobal
  let φ : ℝ → M.Point → M.Point := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hv := hZ.contMDiff_section
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hcomp : ∀ s t x, φ (s + t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := CollarFlow.contMDiff_joint_of_isMIntegralCurve hv φ hself hγ
  let F : Flow ℝ M.Point := ⟨φ, hs.continuous, hcomp, hself⟩
  refine ⟨⟨F, hs, ?_⟩⟩
  intro x
  exact (isMIntegralCurve_iff_chart_solves M Z _
    ((hs.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp (hγ x)

set_option backward.isDefEq.respectTransparency false in
/-- Global cover curves descend to a complete smooth flow of the specified
original field. Native uniqueness supplies independence of angle lifts and
the action law; native smooth dependence supplies joint quotient smoothness. -/
theorem exists_originalCompleteLiouvilleFlow_of_coverCurves (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K)
    (hglobal : ∀ x : TangentCoordinates n, ∃ γ : ℝ → TangentCoordinates n,
      γ 0 = x ∧ ∀ t, HasDerivAt γ (originalLiouvilleCoverField I K (γ t)) t) :
    Nonempty (CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K))) := by
  apply exists_completeLiouvilleFlow_of_globalIntegralCurves (lgManifold n)
    ((lgManifold n).liouvilleVector (lambdaKForm I K))
    (isSmoothVectorField_liouvilleVector_lambdaKForm I hK)
  intro y
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨γ, hγ₀, hγ⟩ := hglobal x
  exact ⟨lgCover ∘ γ, by simp only [comp_apply, hγ₀],
    isMIntegralCurve_lgCover_originalLiouville hK hγ⟩

/-- The original Liouville field has an actual jointly smooth flow for all
real times, for every finite nonnegative `K`. The generic continuation
theorem consumes its proved smoothness and global linear-growth estimate. -/
theorem exists_originalCompleteLiouvilleFlow (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) :
    Nonempty (CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K))) := by
  obtain ⟨C, hC, hbound⟩ := exists_originalLiouvilleCoverField_linear_growth I hK
  obtain ⟨F, _, hF⟩ := LinearGrowthCompleteFlow.exists_smooth_flow
    (contDiff_originalLiouvilleCoverField I hK) hC hbound
  apply exists_originalCompleteLiouvilleFlow_of_coverCurves I hK
  intro x
  exact ⟨fun t => F t x, by simp, hF x⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual quotient flow agrees with every projected original cover
orbit having the same initial point. In particular the action obtained by
descent does not depend on any choice of angle representative. -/
theorem originalCompleteLiouvilleFlow_lgCover (I : ToricInput n) {K : ℝ}
    (hK : 0 ≤ K)
    (F : CompleteLiouvilleFlow (lgManifold n)
      ((lgManifold n).liouvilleVector (lambdaKForm I K)))
    {x : TangentCoordinates n} {γ : ℝ → TangentCoordinates n}
    (hγ₀ : γ 0 = x)
    (hγ : ∀ t, HasDerivAt γ (originalLiouvilleCoverField I K (γ t)) t)
    (t : ℝ) : F.flow t (lgCover x) = lgCover (γ t) := by
  have hv := (isSmoothVectorField_liouvilleVector_lambdaKForm I hK).contMDiff_section
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
    (F.isMIntegralCurve (lgCover x))
    (isMIntegralCurve_lgCover_originalLiouville hK hγ)
    (by simp only [Flow.map_zero_apply, comp_apply, hγ₀])
  exact congrFun heq t

/-- The original primitive with its constructed all-real smooth flow,
on precisely the frozen original quotient manifold. This is the complete
ambient witness consumed by finite type and the initial-pair markings. -/
def originalCompletePrimitive (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) :
    CompletePrimitive (lgManifold n) (lambdaKForm I K) where
  smooth_primitive := isSmoothForm_lambdaKForm I K
  symplectic := isSymplecticOn_exteriorDerivative_lambdaKForm I hK
  smooth_field := isSmoothVectorField_liouvilleVector_lambdaKForm I hK
  contraction := by
    intro y v
    obtain ⟨x, rfl⟩ := lgCover_surjective n y
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    rw [liouvilleVector_lambdaKForm_lgCover I hK,
      exteriorDerivative_lambdaKForm_lgCover, lambdaKForm_lgCover]
    exact omegaKCoordinates_liouville I (lgCover x) hK q
  completeFlow := Classical.choice (exists_originalCompleteLiouvilleFlow I hK)

/-- Completeness of the actual original primitive holds for every finite
nonnegative `K`, without an end bound or a flow in the input. -/
theorem exists_originalCompletePrimitive (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) :
    Nonempty (CompletePrimitive (lgManifold n) (lambdaKForm I K)) :=
  ⟨originalCompletePrimitive I hK⟩

end FsFltz.Geometry
