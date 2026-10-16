import FsFltz.Geometry.RankTwoMaslovFamily
import FsFltz.Geometry.FixedComplexMaslov
import FsFltz.Geometry.PotentialLogarithmicGrading
import FsFltz.Geometry.TailoringCompletedGradingNative
import FsFltz.Analysis.TailoringNormalization

/-!
# The native rank-two shear and prescribed holomorphic Maslov datum

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1981–2089;
`geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244. The native shear
normalization has an explicit invertible complex-linear path to identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

section LinearAlgebra
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The normalized holomorphic shear is the composition of these two
commuting real rank-one shears. -/
def holomorphicDoubleShear (p q : E →L[ℝ] ℝ) (X : E) (J : E →L[ℝ] E) (c : ℝ) :
    E →L[ℝ] E := (rankTwoShear p X c).comp (rankTwoShear q (J X) c)

theorem holomorphicDoubleShear_apply (p q : E →L[ℝ] ℝ) (X : E) (J : E →L[ℝ] E)
    (hpJ : ∀ v, p (J v) = -q v) (hqX : q X = 0) (c : ℝ) (v : E) :
    holomorphicDoubleShear p q X J c v = v + (c * p v) • X + (c * q v) • J X := by
  have hpX : p (J X) = 0 := by rw [hpJ, hqX, neg_zero]
  simp only [holomorphicDoubleShear, ContinuousLinearMap.comp_apply, rankTwoShear_apply,
    map_add, map_smul, hpX, mul_zero]
  module

theorem holomorphicDoubleShear_intertwines (p q : E →L[ℝ] ℝ) (X : E) (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v)
    (hpJ : ∀ v, p (J v) = -q v) (hqJ : ∀ v, q (J v) = p v)
    (hqX : q X = 0) (c : ℝ) (v : E) :
    holomorphicDoubleShear p q X J c (J v) = J (holomorphicDoubleShear p q X J c v) := by
  rw [holomorphicDoubleShear_apply p q X J hpJ hqX,
    holomorphicDoubleShear_apply p q X J hpJ hqX,
    hpJ, hqJ, map_add, map_add, map_smul, map_smul, hJ]
  module

/-- The actual shear followed by its compatible-structure normalization
is exactly the endpoint of the complex-linear double-shear path. -/
theorem rankTwoShear_normalization_eq_doubleShear
    (p q : E →L[ℝ] ℝ) (X : E) (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v) (hpJ : ∀ v, p (J v) = -q v)
    (hqX : q X = 0) (K : ℝ) (hden : 1 + K * p X ≠ 0) (v : E) :
    rankTwoShear p X K
      (compatibleComplexTransport (rankTwoShearComplex p X K J) J v) =
      holomorphicDoubleShear p q X J (K / 2) v := by
  change rankTwoShear p X K ((2 : ℝ)⁻¹ •
    (v - rankTwoShearComplex p X K J (J v))) = _
  rw [map_smul, map_sub, rankTwoShearComplex_intertwines p X K hden J,
    rankTwoShear_apply, rankTwoShear_apply, map_add, map_smul, hJ, hpJ,
    holomorphicDoubleShear_apply p q X J hpJ hqX]
  module

end LinearAlgebra

namespace SmoothManifold
variable {n : ℕ} (M : SmoothManifold (2 * n))

theorem vectorInChart_almostComplex_apply (J : AlmostComplexField M)
    (X : (x : M.Point) → M.Tangent x) (a : M.Point)
    {y : Model (2 * n)} (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    M.vectorInChart a (fun x => J x (X x)) y =
      almostComplexInChart M a J y (M.vectorInChart a X y) := by
  change _ = mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
    (chartAt (Model (2 * n)) a) ((chartAt (Model (2 * n)) a).symm y)
    (J ((chartAt (Model (2 * n)) a).symm y)
      (M.inverseChartTangentMap a y (M.vectorInChart a X y)))
  rw [M.inverseChart_vectorInChart X a hy]
  rfl

theorem isSmoothVectorField_almostComplex_apply (J : AlmostComplexField M)
    (hJ : IsSmoothAlmostComplexField M J) (X : (x : M.Point) → M.Tangent x)
    (hX : M.IsSmoothVectorField X) : M.IsSmoothVectorField (fun x => J x (X x)) := by
  intro a
  exact ((hJ a).clm_apply (hX a)).congr
    (fun y hy => M.vectorInChart_almostComplex_apply J X a hy)

/-- The two actual tensor shears depend jointly smoothly on time and space,
with the original tensor and complex field expressed in the same charts. -/
theorem smoothNearInterval_holomorphicDoubleShearTensor
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (X : (x : M.Point) → M.Tangent x) (hX : M.IsSmoothVectorField X)
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J)
    (s : M.Point → SquaredCanonicalTensor n) (hs : IsSmoothSquaredTensorSection M s)
    (K : ℝ) (a : M.Point) :
    SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun z => squaredTensorInChart M a
        (fun x => rankTwoShearTensor (q x) (J x (X x)) (z.1 * K / 2)
          (rankTwoShearTensor (p x) (X x) (z.1 * K / 2) (s x))) z.2) := by
  let e := chartAt (Model (2 * n)) a
  let B : Set (ℝ × Model (2 * n)) := univ ×ˢ e.target
  let Y := fun x => J x (X x)
  have hY := M.isSmoothVectorField_almostComplex_apply J hJ X hX
  have hpc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) =>
      ((p (e.symm z.2)).comp (M.inverseChartTangentMap a z.2) : Model (2 * n) →L[ℝ] ℝ)) B :=
    (contDiffOn_covector_comp_inverseChart M p hp a).comp contDiffOn_snd (fun _ hz => hz.2)
  have hqc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) =>
      ((q (e.symm z.2)).comp (M.inverseChartTangentMap a z.2) : Model (2 * n) →L[ℝ] ℝ)) B :=
    (contDiffOn_covector_comp_inverseChart M q hq a).comp contDiffOn_snd (fun _ hz => hz.2)
  have hxc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => M.vectorInChart a X z.2) B :=
    (hX a).comp contDiffOn_snd (fun _ hz => hz.2)
  have hyc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => M.vectorInChart a Y z.2) B :=
    (hY a).comp contDiffOn_snd (fun _ hz => hz.2)
  have hsc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => squaredTensorInChart M a s z.2) B :=
    (hs a).comp contDiffOn_snd (fun _ hz => hz.2)
  have hkc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => z.1 * K / 2) B :=
    (contDiffOn_fst.mul contDiffOn_const).div_const 2
  refine ⟨B, isOpen_univ.prod e.open_target, fun z hz => ⟨mem_univ _, hz.2⟩, ?_⟩
  exact (contDiffOn_rankTwoShearTensor hqc hyc hkc
    (contDiffOn_rankTwoShearTensor hpc hxc hkc hsc)).congr (by
      intro z hz
      rw [squaredTensorInChart_rankTwoShearTensor M q Y (z.1 * K / 2) _ a hz.2,
        squaredTensorInChart_rankTwoShearTensor M p X (z.1 * K / 2) s a hz.2])

end SmoothManifold

namespace MaslovRepresentative
variable {n : ℕ} {M : SmoothManifold (2 * n)} {omega eta : M.Form 2}

/-- The actual normalized shear has a smooth tensor homotopy to the
prescribed datum when its two covectors satisfy the holomorphic equations.
The entire tensor homotopy uses the fixed target form `eta`. -/
theorem rankTwoShear_homotopic_of_holomorphic_covectors
    (s : MaslovRepresentative M omega) (homega : M.IsSmoothForm omega)
    (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (hpJ : ∀ x v, p x (s.J x v) = -q x v)
    (hqJ : ∀ x v, q x (s.J x v) = p x v)
    (K : ℝ) (hK : 0 ≤ K)
    (hden : ∀ x, 1 + K * M.rankTwoPairing omega x (hnd x) (p x) (q x) ≠ 0)
    (S r : MaslovRepresentative M eta)
    (hSJ : S.J = fun x => rankTwoShearComplex (p x)
      (M.hamiltonianVector omega x (hnd x) (q x)) K (s.J x))
    (hST : S.tensor = fun x => rankTwoShearTensor (p x)
      (M.hamiltonianVector omega x (hnd x) (q x)) K (s.tensor x))
    (hrJ : r.J = s.J) (hrT : r.tensor = s.tensor) : MaslovHomotopic S r := by
  let X := fun x => M.hamiltonianVector omega x (hnd x) (q x)
  have hX := M.isSmoothVectorField_hamiltonianVector omega homega hnd q hq
  have hqX (x) : q x (X x) = 0 :=
    SymplecticAlgebra.hamiltonianVector_self _ _ _ _
  have hpX (x) : 0 ≤ p x (X x) := by
    by_cases hx : X x = 0
    · simp [hx]
    · have h := s.compatible.2.2.2 x (X x) hx
      rw [M.hamiltonianVector_contraction omega x (hnd x) (q x), hqJ] at h
      exact le_of_lt h
  have hdc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x) :
      1 + (t * K / 2) * p x (X x) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (div_nonneg (mul_nonneg ht.1 hK) (by norm_num)) (hpX x)))
  have hdq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x) :
      1 + (t * K / 2) * q x (s.J x (X x)) ≠ 0 := by
    rw [hqJ]
    exact hdc t ht x
  let N := S.changeCompatibleStructure r.J r.compatible
  have hRN : MaslovHomotopic r N := by
    refine ⟨{
      family := {
        J := fun _ => r.J
        tensor := fun t x => rankTwoShearTensor (q x) (s.J x (X x)) (t * K / 2)
          (rankTwoShearTensor (p x) (X x) (t * K / 2) (s.tensor x))
        compatible := fun _ _ => r.compatible
        canonical := ?_
        nowhereZero := ?_
        smoothJ := fun a => SmoothNearInterval.constant
          (chartAt (Model (2 * n)) a).open_target (r.compatible.1 a)
        smoothSection := M.smoothNearInterval_holomorphicDoubleShearTensor
          p q hp hq X hX s.J s.compatible.1 s.tensor s.smooth K }
      sourceJ := rfl
      targetJ := rfl
      sourceSection := ?_
      targetSection := ?_ }⟩
    · intro t ht x
      rw [hrJ]
      convert isSquaredCanonicalTensor_comp_of_intertwines
        (holomorphicDoubleShear (p x) (q x) (X x) (s.J x) (t * K / 2)) (s.J x) (s.J x)
        (holomorphicDoubleShear_intertwines (p x) (q x) (X x) (s.J x)
          (s.compatible.2.1 x) (hpJ x) (hqJ x) (hqX x) (t * K / 2))
        (s.tensor x) (s.canonical x) using 1
      ext v
      rfl
    · intro t ht x
      exact rankTwoShearTensor_ne_zero (q x) (s.J x (X x)) (t * K / 2) (hdq t ht x) _
        (rankTwoShearTensor_ne_zero (p x) (X x) (t * K / 2) (hdc t ht x) _
          (s.nowhereZero x))
    · funext x
      simp only [zero_mul, zero_div, rankTwoShearTensor_zero, hrT]
    · funext x
      change rankTwoShearTensor (q x) (s.J x (X x)) (1 * K / 2)
        (rankTwoShearTensor (p x) (X x) (1 * K / 2) (s.tensor x)) =
        transportSquaredTensor (S.J x) (r.J x) (S.tensor x)
      rw [hSJ, hST, hrJ, one_mul]
      ext v
      apply congrArg (s.tensor x)
      funext i
      exact (rankTwoShear_normalization_eq_doubleShear (p x) (q x) (X x) (s.J x)
        (s.compatible.2.1 x) (hpJ x) (hqX x) K (hden x) (v i)).symm
  exact (S.homotopic_changeCompatibleStructure r.J r.compatible).trans hRN.symm

/-- For a holomorphic complex-valued map, the constructed native Maslov
datum of the actual primitive update is homotopic to its prescribed
complex structure and original squared tensor. No tensor-ratio or
homotopy hypothesis is supplied. -/
theorem rankTwoPrimitive_homotopic_of_holomorphic {alpha : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha)
    (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hcomplex : ∀ x v, complexDifferential M f x (s.J x v) =
      Complex.I * complexDifferential M f x v)
    (K : ℝ) (hK : 0 ≤ K)
    (hden : ∀ x, 1 + K * M.planePairing alpha f x (hnd x) ≠ 0)
    (r : MaslovRepresentative M (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)))
    (hrJ : r.J = s.J) (hrT : r.tensor = s.tensor) :
    MaslovHomotopic (s.rankTwoPrimitive halpha hnd f hf K hden) r := by
  apply s.rankTwoShear_homotopic_of_holomorphic_covectors
    (M.isSmoothForm_exteriorDerivative alpha halpha) hnd
    (fun x => Complex.reCLM.comp (complexDifferential M f x))
    (fun x => Complex.imCLM.comp (complexDifferential M f x))
    (isSmoothForm_complexDifferential_comp M hf Complex.reCLM)
    (isSmoothForm_complexDifferential_comp M hf Complex.imCLM)
    ?_ ?_ K hK hden _ r rfl rfl hrJ hrT
  · intro x v
    exact congrArg Complex.re (hcomplex x v) |>.trans (by simp)
  · intro x v
    exact congrArg Complex.im (hcomplex x v) |>.trans (by simp)

/-- The same theorem applies to the nonnegative-pairing constructor used
by the native completed-family producer. -/
theorem nonnegativeRankTwoPrimitive_homotopic_of_holomorphic {alpha : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha)
    (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hcomplex : ∀ x v, complexDifferential M f x (s.J x v) =
      Complex.I * complexDifferential M f x v)
    (hpi : ∀ x, 0 ≤ M.planePairing alpha f x (hnd x)) (K : ℝ) (hK : 0 ≤ K)
    (r : MaslovRepresentative M (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)))
    (hrJ : r.J = s.J) (hrT : r.tensor = s.tensor) :
    MaslovHomotopic (s.nonnegativeRankTwoPrimitive halpha hnd f hf hpi K hK) r :=
  s.rankTwoPrimitive_homotopic_of_holomorphic halpha hnd f hf hcomplex K hK _ r hrJ hrT

end MaslovRepresentative

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The actual zero-time tailoring map is holomorphic for the prescribed
logarithmic complex structure, including its retained exponential scale. -/
theorem complexDifferential_tailoringFamily_zero_logarithmic (I : ToricInput n) (β : ℝ)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y) :
    complexDifferential (lgManifold n) (tailoringFamily I β 0) y
      (logarithmicAlmostComplexField n y v) =
        Complex.I * complexDifferential (lgManifold n) (tailoringFamily I β 0) y v := by
  have hd : complexDifferential (lgManifold n) (tailoringFamily I β 0) y =
      Real.exp (-β) • complexDifferential (lgManifold n) (W (I.alongCoefficientPath 1)) y := by
    rw [tailoringFamily_zero_scale]
    exact (((contMDiff_W_lgManifold (I.alongCoefficientPath 1)).mdifferentiable
      (by simp) y).hasMFDerivAt.const_smul (Real.exp (-β))).mfderiv
  rw [hd]
  simp only [smul_apply, complexDifferential_W_logarithmicAlmostComplex,
    Complex.real_smul]
  ring

/-- The prescribed native datum is constructed on precisely the actual
zero-time tailoring primitive; no representative is an input. -/
def tailoringZeroPrescribedMaslov (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K) :
    MaslovRepresentative (lgManifold n)
      ((lgManifold n).exteriorDerivative ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 0) K)) where
  J := logarithmicAlmostComplexField n
  tensor := logarithmicSquaredVolumeTensor n
  compatible := isCompatibleAlmostComplex_potential_holomorphic hφ hc hlower
    (tailoringFamily I β 0) (contMDiff_tailoringFamily_lgManifold I β 0)
    (complexDifferential_tailoringFamily_zero_logarithmic I β) hK
  canonical := logarithmicSquaredVolumeTensor_canonical
  smooth := isSmoothSquaredTensorSection_logarithmicSquaredVolumeTensor n
  nowhereZero := logarithmicSquaredVolumeTensor_ne_zero

theorem isLogarithmicGrading_tailoringZeroPrescribedMaslov (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K) :
    IsLogarithmicGrading id (tailoringZeroPrescribedMaslov I hφ hc hlower β K hK) :=
  (isLogarithmicGrading_id_iff_tensor_eq _).mpr rfl

/-- Holomorphicity supplies the required nonnegative native scalar for
every real zero-time scale, without a large-scale threshold. -/
theorem tailoringFamily_zero_native_planePairing_nonneg (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ) (y : LGSpace n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) :
    0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 0) y hnd := by
  rw [show tailoringFamily I β 0 = tailoringOriginal I β from funext (tailoringFamily_zero I β)]
  exact tailoringOriginal_native_planePairing_nonneg I hφ hc hlower β y hnd

/-- Every selected native zero-time representative is actually homotopic
to the constructed prescribed representative on the identical primitive. -/
theorem tailoringNativeMaslov_zeroTime_homotopic_prescribed (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β : ℝ)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 0) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (K : ℝ) (hK : 0 ≤ K) :
    MaslovHomotopic (tailoringNativeMaslov I hφ hc hlower β 0 hπ K hK)
      (tailoringZeroPrescribedMaslov I hφ hc hlower β K hK) :=
  (potentialMaslovRepresentative hφ hc hlower).nonnegativeRankTwoPrimitive_homotopic_of_holomorphic
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (tailoringFamily I β 0) (contMDiff_tailoringFamily_lgManifold I β 0)
    (complexDifferential_tailoringFamily_zero_logarithmic I β) hπ K hK _ rfl rfl

/-- All native inputs and the prescribed representative are produced
directly from the Hessian bound and nonnegative update coefficient. -/
theorem tailoringZero_exists_prescribed_native_homotopy (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K) :
    ∃ hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 0) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y),
      MaslovHomotopic (tailoringNativeMaslov I hφ hc hlower β 0 hπ K hK)
        (tailoringZeroPrescribedMaslov I hφ hc hlower β K hK) ∧
      IsLogarithmicGrading id (tailoringZeroPrescribedMaslov I hφ hc hlower β K hK) :=
  ⟨fun y => tailoringFamily_zero_native_planePairing_nonneg I hφ hc hlower β y _,
    tailoringNativeMaslov_zeroTime_homotopic_prescribed I hφ hc hlower β _ K hK,
    isLogarithmicGrading_tailoringZeroPrescribedMaslov I hφ hc hlower β K hK⟩

end FsFltz
