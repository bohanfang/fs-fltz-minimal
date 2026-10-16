import FsFltz.Geometry.RankTwoSymplecticShear
import FsFltz.Geometry.PrescribedGradingBridge

/-!
# Smooth native Maslov data for rank-two updates

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1990–2102.
The explicit shear identifies the actual updated tangent form with the
original form. This constructs smooth compatible structures and canonical
squares on the native ambient; completed-family extension is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
namespace SmoothManifold
variable {d : ℕ} (M : SmoothManifold d)

/-- The inverse chart derivative recovers the original vector field. -/
theorem inverseChart_vectorInChart (X : (x : M.Point) → M.Tangent x) (a : M.Point)
    {y : Model d} (hy : y ∈ (chartAt (Model d) a).target) :
    M.inverseChartTangentMap a y (M.vectorInChart a X y) =
      X ((chartAt (Model d) a).symm y) := by
  let e := chartAt (Model d) a
  have hx := e.map_target hy
  have h := congrArg (fun L => L (X (e.symm y)))
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx)
  change M.inverseChartTangentMap a (e (e.symm y))
    (M.vectorInChart a X y) = X (e.symm y) at h
  erw [e.right_inv hy] at h
  exact h

/-- Chart contraction for the actual Hamiltonian field of any smooth
covector, independently of whether it is exact. -/
theorem hamiltonianVector_chart_contraction (omega : M.Form 2)
    (hnd : ∀ x, M.Nondegenerate omega x)
    (q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (a : M.Point) {y : Model d} (hy : y ∈ (chartAt (Model d) a).target) :
    (M.formInChart a omega y).curryLeft
      (M.vectorInChart a (fun x => M.hamiltonianVector omega x (hnd x) (q x)) y) =
        M.formInChart a (covectorForm M q) y := by
  ext vs
  have hv : vs = ![vs 0] := by funext i; fin_cases i; rfl
  rw [hv]
  change omega ((chartAt (Model d) a).symm y)
    ((M.inverseChartTangentMap a y) ∘
      ![M.vectorInChart a (fun x => M.hamiltonianVector omega x (hnd x) (q x)) y, vs 0]) = _
  have he : (M.inverseChartTangentMap a y) ∘
      ![M.vectorInChart a (fun x => M.hamiltonianVector omega x (hnd x) (q x)) y, vs 0] =
    ![M.hamiltonianVector omega ((chartAt (Model d) a).symm y)
      (hnd _) (q _), M.inverseChartTangentMap a y (vs 0)] := by
    funext i
    fin_cases i
    · exact M.inverseChart_vectorInChart
        (fun x => M.hamiltonianVector omega x (hnd x) (q x)) a hy
    · rfl
  rw [he]
  exact M.hamiltonianVector_contraction omega _ (hnd _) (q _) _

/-- Smoothness of Hamiltonian vectors comes from the actual contraction
operator and its inverse, rather than from an additional field certificate. -/
theorem isSmoothVectorField_hamiltonianVector (omega : M.Form 2)
    (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hq : M.IsSmoothForm (covectorForm M q)) :
    M.IsSmoothVectorField (fun x => M.hamiltonianVector omega x (hnd x) (q x)) := by
  intro a
  let A : Model d → Model d →L[ℝ] Model d :=
    fun y => chartContraction (M.formInChart a omega y)
  let b : Model d → Model d :=
    fun y => (chartOneFormEquiv d).symm (M.formInChart a (covectorForm M q) y)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A (chartAt (Model d) a).target :=
    contDiffOn_const.clm_comp (hcur.comp_contDiffOn (homega a))
  have hb : ContDiffOn ℝ ∞ b (chartAt (Model d) a).target :=
    (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn (hq a)
  have hinv (y) (hy : y ∈ (chartAt (Model d) a).target) : (A y).IsInvertible :=
    chartContraction_invertible _ (M.nondegenerate_formInChart omega a hy (hnd _))
  have hAi : ContDiffOn ℝ ∞ (fun y => (A y).inverse) (chartAt (Model d) a).target := by
    intro y hy
    exact (hinv y hy).contDiffAt_map_inverse.comp_contDiffWithinAt y (hA y hy)
  apply (hAi.clm_apply hb).congr
  intro y hy
  symm
  apply (hinv y hy).inverse_apply_eq.mpr
  exact congrArg (chartOneFormEquiv d).symm
    (M.hamiltonianVector_chart_contraction omega hnd q a hy).symm

end SmoothManifold

theorem rankTwoShearComplex_map
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (G : E →L[ℝ] F) (p : E →L[ℝ] ℝ) (q : F →L[ℝ] ℝ) (X : E) (Y : F)
    (J : E →L[ℝ] E) (L : F →L[ℝ] F)
    (hp : ∀ v, p v = q (G v)) (hX : G X = Y)
    (hJ : ∀ v, G (J v) = L (G v)) (K : ℝ) (v : E) :
    G (rankTwoShearComplex p X K J v) = rankTwoShearComplex q Y K L (G v) := by
  have hT (c : ℝ) (w : E) : G (rankTwoShear p X c w) = rankTwoShear q Y c (G w) := by
    rw [rankTwoShear_apply, map_add, map_smul, hX, hp, rankTwoShear_apply]
  change G (rankTwoShear p X (-K / (1 + K * p X)) (J (rankTwoShear p X K v))) = _
  rw [hT, hJ, hT, hp X, hX]
  rfl

section NativeShear
variable {n : ℕ} (M : SmoothManifold (2 * n))
  (p : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
  (X : (x : M.Point) → M.Tangent x) (K : ℝ)

/-- Chart transport of the shear uses the actual covector and vector
coordinate expressions. -/
theorem inverseChart_rankTwoShear (a : M.Point) {y : Model (2 * n)}
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) (v : Model (2 * n)) :
    M.inverseChartTangentMap a y
      (rankTwoShear ((p ((chartAt (Model (2 * n)) a).symm y)).comp
        (M.inverseChartTangentMap a y)) (M.vectorInChart a X y) K v) =
      rankTwoShear (p ((chartAt (Model (2 * n)) a).symm y))
        (X ((chartAt (Model (2 * n)) a).symm y)) K (M.inverseChartTangentMap a y v) := by
  rw [rankTwoShear_apply, map_add, map_smul, M.inverseChart_vectorInChart X a hy,
    rankTwoShear_apply]
  rfl

theorem almostComplexInChart_rankTwoShearComplex (J : AlmostComplexField M)
    (a : M.Point) {y : Model (2 * n)}
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    almostComplexInChart M a (fun x => rankTwoShearComplex (p x) (X x) K (J x)) y =
      rankTwoShearComplex
        ((p ((chartAt (Model (2 * n)) a).symm y)).comp (M.inverseChartTangentMap a y))
        (M.vectorInChart a X y) K (almostComplexInChart M a J y) := by
  ext v : 1
  apply (inverseChartTangentMap_isInvertible M a y hy).injective
  rw [inverseChartTangentMap_almostComplexInChart M a _ y hy]
  symm
  exact rankTwoShearComplex_map (M.inverseChartTangentMap a y) _ _ _ _ _ _
    (fun _ => rfl) (M.inverseChart_vectorInChart X a hy)
    (inverseChartTangentMap_almostComplexInChart M a J y hy) K v

theorem isSmoothAlmostComplexField_rankTwoShearComplex
    (hp : M.IsSmoothForm (covectorForm M p)) (hX : M.IsSmoothVectorField X)
    (hden : ∀ x, 1 + K * p x (X x) ≠ 0)
    (J : AlmostComplexField M) (hJ : IsSmoothAlmostComplexField M J) :
    IsSmoothAlmostComplexField M (fun x => rankTwoShearComplex (p x) (X x) K (J x)) := by
  intro a
  have hc : ∀ y ∈ (chartAt (Model (2 * n)) a).target,
      1 + K * ((p ((chartAt (Model (2 * n)) a).symm y)).comp
        (M.inverseChartTangentMap a y)) (M.vectorInChart a X y) ≠ 0 := by
    intro y hy
    change 1 + K * p _ (M.inverseChartTangentMap a y (M.vectorInChart a X y)) ≠ 0
    rw [M.inverseChart_vectorInChart X a hy]
    exact hden _
  exact (contDiffOn_rankTwoShearComplex
    (contDiffOn_covector_comp_inverseChart M p hp a) (hX a) contDiffOn_const (hJ a) hc).congr
      (fun y hy => almostComplexInChart_rankTwoShearComplex M p X K J a hy)

theorem squaredTensorInChart_rankTwoShearTensor
    (s : M.Point → SquaredCanonicalTensor n) (a : M.Point) {y : Model (2 * n)}
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    squaredTensorInChart M a (fun x => rankTwoShearTensor (p x) (X x) K (s x)) y =
      rankTwoShearTensor
        ((p ((chartAt (Model (2 * n)) a).symm y)).comp (M.inverseChartTangentMap a y))
        (M.vectorInChart a X y) K (squaredTensorInChart M a s y) := by
  ext v
  apply congrArg (s ((chartAt (Model (2 * n)) a).symm y))
  funext i
  exact (inverseChart_rankTwoShear M p X K a hy (v i)).symm

theorem isSmoothSquaredTensorSection_rankTwoShearTensor
    (hp : M.IsSmoothForm (covectorForm M p)) (hX : M.IsSmoothVectorField X)
    (s : M.Point → SquaredCanonicalTensor n) (hs : IsSmoothSquaredTensorSection M s) :
    IsSmoothSquaredTensorSection M (fun x => rankTwoShearTensor (p x) (X x) K (s x)) := by
  intro a
  exact (contDiffOn_rankTwoShearTensor
    (contDiffOn_covector_comp_inverseChart M p hp a) (hX a) contDiffOn_const (hs a)).congr
      (fun y hy => squaredTensorInChart_rankTwoShearTensor M p X K s a hy)

end NativeShear

namespace MaslovRepresentative
variable {n : ℕ} {M : SmoothManifold (2 * n)} {omega : M.Form 2}

/-- An actual smooth native Maslov representative for the rank-two form,
constructed from the original representative and the two smooth covectors. -/
def rankTwo (s : MaslovRepresentative M omega) (homega : M.IsSmoothForm omega)
    (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (K : ℝ) (hden : ∀ x, 1 + K * M.rankTwoPairing omega x (hnd x) (p x) (q x) ≠ 0) :
    MaslovRepresentative M (M.rankTwoForm omega p q K) := by
  let X := fun x => M.hamiltonianVector omega x (hnd x) (q x)
  have hX := M.isSmoothVectorField_hamiltonianVector omega homega hnd q hq
  refine
    { J := fun x => rankTwoShearComplex (p x) (X x) K (s.J x)
      tensor := fun x => rankTwoShearTensor (p x) (X x) K (s.tensor x)
      compatible := ⟨isSmoothAlmostComplexField_rankTwoShearComplex M p X K hp hX hden
        s.J s.compatible.1, ?_, ?_, ?_⟩
      canonical := fun x => rankTwoShearTensor_canonical (p x) (X x) K (hden x)
        (s.J x) (s.tensor x) (s.canonical x)
      smooth := isSmoothSquaredTensorSection_rankTwoShearTensor M p X K hp hX s.tensor s.smooth
      nowhereZero := fun x => rankTwoShearTensor_ne_zero (p x) (X x) K (hden x)
        (s.tensor x) (s.nowhereZero x) }
  · intro x v
    exact rankTwoShearComplex_sq (p x) (X x) K (hden x) (s.J x) (s.compatible.2.1 x) v
  · intro x v w
    exact (rankTwoShearComplex_compatible
      (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
      (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
      (p x) (q x) (X x) (M.hamiltonianVector_contraction omega x (hnd x) (q x))
      K (hden x) (s.J x) (s.compatible.2.2.1 x) (s.compatible.2.2.2 x)).1 v w
  · intro x v hv
    exact (rankTwoShearComplex_compatible
      (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
      (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
      (p x) (q x) (X x) (M.hamiltonianVector_contraction omega x (hnd x) (q x))
      K (hden x) (s.J x) (s.compatible.2.2.1 x) (s.compatible.2.2.2 x)).2 v hv

end MaslovRepresentative

namespace SmoothManifold
variable {d : ℕ} (M : SmoothManifold d)

/-- Equality of the full native two-forms, rather than only scalar evaluations. -/
theorem exteriorDerivative_rankTwoPrimitive_eq (alpha : M.Form 1) (f : M.Point → ℂ)
    (halpha : M.IsSmoothForm alpha) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (K : ℝ) :
    M.exteriorDerivative (M.rankTwoPrimitive alpha f K) =
      M.rankTwoForm (M.exteriorDerivative alpha)
        (fun x => Complex.reCLM.comp (complexDifferential M f x))
        (fun x => Complex.imCLM.comp (complexDifferential M f x)) K := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]
  exact M.evalTwo_exteriorDerivative_rankTwoPrimitive halpha hf K x _ _

end SmoothManifold

namespace MaslovRepresentative
variable {n : ℕ} {M : SmoothManifold (2 * n)} {alpha : M.Form 1}

/-- The concrete native datum for the actual primitive update by an
arbitrary smooth complex-valued map. No holomorphic hypothesis is used. -/
def rankTwoPrimitive (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (K : ℝ) (hden : ∀ x, 1 + K * M.planePairing alpha f x (hnd x) ≠ 0) :
    MaslovRepresentative M (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) := by
  let S := s.rankTwo (M.isSmoothForm_exteriorDerivative alpha halpha) hnd
      (fun x => Complex.reCLM.comp (complexDifferential M f x))
      (fun x => Complex.imCLM.comp (complexDifferential M f x))
      (isSmoothForm_complexDifferential_comp M hf Complex.reCLM)
      (isSmoothForm_complexDifferential_comp M hf Complex.imCLM) K hden
  exact { J := S.J, tensor := S.tensor
          compatible := by
            rw [M.exteriorDerivative_rankTwoPrimitive_eq alpha f halpha hf K]
            exact S.compatible
          canonical := S.canonical, smooth := S.smooth, nowhereZero := S.nowhereZero }

/-- Nonnegative Poisson pairing supplies every nonnegative coefficient;
the original native Maslov datum is the sole grading input. -/
def nonnegativeRankTwoPrimitive (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hpi : ∀ x, 0 ≤ M.planePairing alpha f x (hnd x)) (K : ℝ) (hK : 0 ≤ K) :
    MaslovRepresentative M (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) :=
  s.rankTwoPrimitive halpha hnd f hf K (fun x =>
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK (hpi x))))

end MaslovRepresentative
end FsFltz.Geometry
