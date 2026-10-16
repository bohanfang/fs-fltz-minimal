import FsFltz.Geometry.PotentialHamiltonian
import FsFltz.Geometry.GradingRepresentatives
import FsFltz.Geometry.MaslovHomotopy

/-!
# Prescribed logarithmic grading for a positive-Hessian potential

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 680–744,
and `lem:grading`, lines 1993–1998. The actual logarithmic complex
structure remains compatible throughout the holomorphic potential path.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

theorem logarithmicAlmostComplexField_cover (x q : TangentCoordinates n) :
    logarithmicAlmostComplexField n (lgCover x) (lgCoverTangent x q) =
      lgCoverTangent x (coordinateComplexStructure n q) := by
  apply (lgTangentCoframe_bijective (lgCover x)).1
  rw [lgTangentCoframe_almostComplex, lgTangentCoframe_lgCover,
    lgTangentCoframe_lgCover]

/-- The Hessian block form is invariant under the actual logarithmic complex field. -/
theorem logarithmicAlmostComplexField_potential_symplectic
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : (lgManifold n).Point) (v w : (lgManifold n).Tangent y) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y
      (logarithmicAlmostComplexField n y v) (logarithmicAlmostComplexField n y w) =
      evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y v w := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  obtain ⟨r, rfl⟩ := (lgCoverTangent_bijective x).2 w
  rw [logarithmicAlmostComplexField_cover, logarithmicAlmostComplexField_cover,
    exteriorDerivative_lambdaPotentialForm_euclidean hφ,
    exteriorDerivative_lambdaPotentialForm_euclidean hφ]
  simp only [coordinateComplexStructure_apply, WithLp.toLp_neg, map_neg, inner_neg_left]
  have hs := inner_fderiv_gradient_symmetric
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) (WithLp.toLp 2 x.1)
  have hs' (u v : EuclideanSpace ℝ (Fin n)) := (hs u v).trans (real_inner_comm _ _)
  rw [hs' (WithLp.toLp 2 q.2) (WithLp.toLp 2 r.1),
    hs' (WithLp.toLp 2 r.2) (WithLp.toLp 2 q.1)]
  ring

/-- Uniform Hessian positivity gives strict positivity on every native nonzero tangent. -/
theorem logarithmicAlmostComplexField_potential_positive
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y) (hv : v ≠ 0) :
    0 < evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y v
      (logarithmicAlmostComplexField n y v) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  have hq : q ≠ 0 := fun h => hv (by rw [h, map_zero])
  rw [logarithmicAlmostComplexField_cover,
    exteriorDerivative_lambdaPotentialForm_euclidean hφ]
  simp only [coordinateComplexStructure_apply, WithLp.toLp_neg, map_neg,
    inner_neg_left, sub_neg_eq_add]
  have h1 := hlower (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.1)
  have h2 := hlower (WithLp.toLp 2 x.1) (WithLp.toLp 2 q.2)
  have hne : (WithLp.toLp 2 q.1 : EuclideanSpace ℝ (Fin n)) ≠ 0 ∨
      (WithLp.toLp 2 q.2 : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    exact Prod.ext (congrArg WithLp.ofLp h.1) (congrArg WithLp.ofLp h.2)
  rcases hne with h | h
  · have hp := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr h))
    have hn := mul_nonneg hc.le (sq_nonneg ‖(WithLp.toLp 2 q.2 : EuclideanSpace ℝ (Fin n))‖)
    linarith
  · have hp := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr h))
    have hn := mul_nonneg hc.le (sq_nonneg ‖(WithLp.toLp 2 q.1 : EuclideanSpace ℝ (Fin n))‖)
    linarith

/-- Holomorphic rank-two updates preserve the prescribed complex structure. -/
theorem isCompatibleAlmostComplex_potential_holomorphic
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (f : (lgManifold n).Point → ℂ)
    (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hcomplex : ∀ y v, complexDifferential (lgManifold n) f y
      (logarithmicAlmostComplexField n y v) = Complex.I * complexDifferential (lgManifold n) f y v)
    {K : ℝ} (hK : 0 ≤ K) :
    IsCompatibleAlmostComplex (lgManifold n)
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) f K)) (logarithmicAlmostComplexField n) := by
  refine ⟨isSmoothAlmostComplexField_logarithmicAlmostComplexField n,
    logarithmicAlmostComplexField_sq, ?_, ?_⟩
  · intro y v w
    rw [(lgManifold n).evalTwo_exteriorDerivative_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) hf,
      (lgManifold n).evalTwo_exteriorDerivative_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) hf,
      logarithmicAlmostComplexField_potential_symplectic hφ,
      hcomplex, hcomplex]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    ring
  · intro y v hv
    rw [(lgManifold n).evalTwo_exteriorDerivative_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) hf, hcomplex]
    have hp := logarithmicAlmostComplexField_potential_positive hφ hc hlower y v hv
    have hn : 0 ≤ K * ((complexDifferential (lgManifold n) f y v).re ^ 2 +
        (complexDifferential (lgManifold n) f y v).im ^ 2) :=
      mul_nonneg hK (add_nonneg (sq_nonneg _) (sq_nonneg _))
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    nlinarith

/-- The actual Laurent differential intertwines the prescribed native complex structure. -/
theorem complexDifferential_W_logarithmicAlmostComplex (I : ToricInput n)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y) :
    complexDifferential (lgManifold n) (W I) y (logarithmicAlmostComplexField n y v) =
      Complex.I * complexDifferential (lgManifold n) (W I) y v := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  rw [logarithmicAlmostComplexField_cover, complexDifferential_W_lgCover,
    complexDifferential_W_lgCover, dW_eq_evaluation, dW_eq_evaluation]
  change CoordinateGeometry.evaluation _
    (tangentComplexCoordinates (complexStructureCoordinates q)) = _
  rw [tangentComplexCoordinates_complexStructure, CoordinateGeometry.evaluation_complexStructure]

/-- The prescribed representative for the actual positive-Hessian holomorphic primitive. -/
def logarithmicPotentialMaslovRepresentative (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {K : ℝ} (hK : 0 ≤ K) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (W I) K)) where
  J := logarithmicAlmostComplexField n
  tensor := logarithmicSquaredVolumeTensor n
  compatible := isCompatibleAlmostComplex_potential_holomorphic hφ hc hlower
    (W I) (contMDiff_W_lgManifold I) (complexDifferential_W_logarithmicAlmostComplex I) hK
  canonical := logarithmicSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n
  nowhereZero := logarithmicSquaredVolumeTensor_ne_zero

/-- The same prescribed fields and tensors give a native Maslov family for
any actual coefficient and positive-Hessian potential path. The pointwise
Hessian hypotheses are used only for compatibility; the fields themselves
have constant smooth extensions across both parameter endpoints. -/
def logarithmicPotentialMaslovFamily (I : ℝ → ToricInput n)
    (φ : ℝ → RealSpace n → ℝ) {c : ℝ} (hc : 0 < c)
    (hφ : ∀ t ∈ parameterInterval, ContDiff ℝ ∞ (φ t))
    (hlower : ∀ t ∈ parameterInterval, ∀ u v : EuclideanSpace ℝ (Fin n),
      c * ‖v‖ ^ 2 ≤ inner ℝ
        (fderiv ℝ (gradient (φ t ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {K : ℝ} (hK : 0 ≤ K) :
    MaslovFamily (lgManifold n) (fun t =>
      (lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm (φ t)) (W (I t)) K)) where
  J := fun _ => logarithmicAlmostComplexField n
  tensor := fun _ => logarithmicSquaredVolumeTensor n
  compatible := fun t ht => (logarithmicPotentialMaslovRepresentative (I t)
    (hφ t ht) hc (hlower t ht) hK).compatible
  canonical := fun _ _ => logarithmicSquaredVolumeTensor_canonical
  nowhereZero := fun _ _ => logarithmicSquaredVolumeTensor_ne_zero
  smoothJ := fun a => SmoothNearInterval.constant
    (chartAt (Model (2 * n)) a).open_target
    (isSmoothAlmostComplexField_logarithmicAlmostComplexField n a)
  smoothSection := fun a => SmoothNearInterval.constant
    (chartAt (Model (2 * n)) a).open_target
    (isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n a)

end FsFltz.Geometry
