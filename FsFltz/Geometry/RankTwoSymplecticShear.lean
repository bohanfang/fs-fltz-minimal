import FsFltz.Geometry.RankTwoLiouville
import FsFltz.Geometry.CompatibleComplexTransport

/-!
# An explicit tangent identification for the rank-two family

Source: `geometric-part-fsf-proof.tex`, `eq:ranktwo`, lines 1119–1150,
and `lem:grading`, lines 1990–2102. On native tangent fibers the map
`v ↦ v + K dA(v) X_B` pulls the original two-form back to the updated
one. Its explicit inverse supplies compatible complex structures and
nonzero canonical tensors without a pointwise polar decomposition.
This is tangent data; transport over the completed family remains separate.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

section Shear
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The rank-one linear shear associated with one covector and one vector. -/
def rankTwoShear (p : E →L[ℝ] ℝ) (X : E) (K : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + K • p.smulRight X

@[simp] theorem rankTwoShear_apply (p : E →L[ℝ] ℝ) (X : E) (K : ℝ) (v : E) :
    rankTwoShear p X K v = v + (K * p v) • X := by
  simp [rankTwoShear, smul_smul]

@[simp] theorem rankTwoShear_zero (p : E →L[ℝ] ℝ) (X : E) :
    rankTwoShear p X 0 = ContinuousLinearMap.id ℝ E := by
  simp [rankTwoShear]

/-- The inverse coefficient is defined wherever the rank-two denominator
is nonzero, including negative coefficients satisfying that condition. -/
theorem rankTwoShear_inverse_apply (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) (v : E) :
    rankTwoShear p X (-K / (1 + K * p X)) (rankTwoShear p X K v) = v := by
  rw [rankTwoShear_apply, rankTwoShear_apply]
  rw [map_add, map_smul, smul_eq_mul, add_assoc, ← add_smul]
  have hc : K * p v + (-K / (1 + K * p X)) * (p v + K * p v * p X) = 0 := by
    field_simp [h]
    ring
  rw [hc, zero_smul, add_zero]

theorem rankTwoShear_apply_inverse (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) (v : E) :
    rankTwoShear p X K (rankTwoShear p X (-K / (1 + K * p X)) v) = v := by
  rw [rankTwoShear_apply, rankTwoShear_apply]
  rw [map_add, map_smul, smul_eq_mul, add_assoc, ← add_smul]
  have hc : (-K / (1 + K * p X)) * p v +
      K * (p v + (-K / (1 + K * p X)) * p v * p X) = 0 := by
    field_simp [h]
    ring
  rw [hc, zero_smul, add_zero]

/-- The shear is a continuous linear equivalence with an explicit inverse. -/
def rankTwoShearEquiv (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { (rankTwoShear p X K).toLinearMap with
      invFun := rankTwoShear p X (-K / (1 + K * p X))
      left_inv := rankTwoShear_inverse_apply p X K h
      right_inv := rankTwoShear_apply_inverse p X K h }
  continuous_toFun := (rankTwoShear p X K).continuous
  continuous_invFun := (rankTwoShear p X (-K / (1 + K * p X))).continuous

theorem rankTwoShear_isInvertible (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) : (rankTwoShear p X K).IsInvertible :=
  ⟨rankTwoShearEquiv p X K h, rfl⟩

/-- The shear exactly realizes the rank-two change of alternating form. -/
theorem rankTwoShear_form (omega : LinearMap.BilinForm ℝ E) (homega : omega.IsAlt)
    (p q : E →L[ℝ] ℝ) (X : E) (hX : ∀ w, omega X w = q w)
    (K : ℝ) (v w : E) :
    omega (rankTwoShear p X K v) (rankTwoShear p X K w) =
      omega v w + K * (p v * q w - q v * p w) := by
  have hright : omega v X = -q v := by
    rw [← LinearMap.IsAlt.neg homega, hX]
  simp only [rankTwoShear_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hX, hright]
  have hzero : q X = 0 := (hX X).symm.trans (homega X)
  rw [hzero]
  ring

end Shear

section ComplexShear
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Pull the original complex structure back through the explicit shear. -/
def rankTwoShearComplex (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (J : E →L[ℝ] E) : E →L[ℝ] E :=
  (rankTwoShear p X (-K / (1 + K * p X))).comp (J.comp (rankTwoShear p X K))

theorem rankTwoShearComplex_intertwines (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) (J : E →L[ℝ] E) (v : E) :
    rankTwoShear p X K (rankTwoShearComplex p X K J v) = J (rankTwoShear p X K v) :=
  rankTwoShear_apply_inverse p X K h _

theorem rankTwoShearComplex_sq (p : E →L[ℝ] ℝ) (X : E) (K : ℝ)
    (h : 1 + K * p X ≠ 0) (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v)
    (v : E) : rankTwoShearComplex p X K J (rankTwoShearComplex p X K J v) = -v := by
  apply (rankTwoShearEquiv p X K h).injective
  change rankTwoShear p X K (rankTwoShearComplex p X K J (rankTwoShearComplex p X K J v)) = _
  rw [rankTwoShearComplex_intertwines p X K h, rankTwoShearComplex_intertwines p X K h,
    hJ, map_neg]
  rfl

@[simp] theorem rankTwoShearComplex_zero (p : E →L[ℝ] ℝ) (X : E) (J : E →L[ℝ] E) :
    rankTwoShearComplex p X 0 J = J := by
  simp [rankTwoShearComplex]

/-- Both compatibility inequalities transport through this concrete
identification of forms; no compatible structure for the update is assumed. -/
theorem rankTwoShearComplex_compatible (omega : LinearMap.BilinForm ℝ E)
    (homega : omega.IsAlt) (p q : E →L[ℝ] ℝ) (X : E)
    (hX : ∀ w, omega X w = q w) (K : ℝ) (hden : 1 + K * p X ≠ 0)
    (J : E →L[ℝ] E) (hpres : ∀ v w, omega (J v) (J w) = omega v w)
    (hpos : ∀ v, v ≠ 0 → 0 < omega v (J v)) :
    (∀ v w,
      omega (rankTwoShearComplex p X K J v) (rankTwoShearComplex p X K J w) +
        K * (p (rankTwoShearComplex p X K J v) * q (rankTwoShearComplex p X K J w) -
          q (rankTwoShearComplex p X K J v) * p (rankTwoShearComplex p X K J w)) =
      omega v w + K * (p v * q w - q v * p w)) ∧
    ∀ v, v ≠ 0 → 0 < omega v (rankTwoShearComplex p X K J v) +
      K * (p v * q (rankTwoShearComplex p X K J v) -
        q v * p (rankTwoShearComplex p X K J v)) := by
  constructor
  · intro v w
    rw [← rankTwoShear_form omega homega p q X hX,
      rankTwoShearComplex_intertwines p X K hden,
      rankTwoShearComplex_intertwines p X K hden, hpres,
      rankTwoShear_form omega homega p q X hX]
  · intro v hv
    rw [← rankTwoShear_form omega homega p q X hX,
      rankTwoShearComplex_intertwines p X K hden]
    exact hpos _ (fun hz => hv ((rankTwoShearEquiv p X K hden).injective
      (hz.trans (map_zero _).symm)))

end ComplexShear

/-- Pull every tangent slot of the canonical square through the same shear. -/
def rankTwoShearTensor {n : ℕ} (p : Model (2 * n) →L[ℝ] ℝ)
    (X : Model (2 * n)) (K : ℝ) (s : SquaredCanonicalTensor n) : SquaredCanonicalTensor n :=
  s.compContinuousLinearMap (fun _ => rankTwoShear p X K)

theorem rankTwoShearTensor_canonical {n : ℕ} (p : Model (2 * n) →L[ℝ] ℝ)
    (X : Model (2 * n)) (K : ℝ) (hden : 1 + K * p X ≠ 0)
    (J : Model (2 * n) →L[ℝ] Model (2 * n))
    (s : SquaredCanonicalTensor n) (hs : IsSquaredCanonicalTensor J s) :
    IsSquaredCanonicalTensor (rankTwoShearComplex p X K J) (rankTwoShearTensor p X K s) :=
  isSquaredCanonicalTensor_comp_of_intertwines _ _ _
    (rankTwoShearComplex_intertwines p X K hden J) s hs

theorem rankTwoShearTensor_ne_zero {n : ℕ} (p : Model (2 * n) →L[ℝ] ℝ)
    (X : Model (2 * n)) (K : ℝ) (hden : 1 + K * p X ≠ 0)
    (s : SquaredCanonicalTensor n) (hs : s ≠ 0) : rankTwoShearTensor p X K s ≠ 0 := by
  intro hz
  apply hs
  ext v
  have he := congrArg (fun t : SquaredCanonicalTensor n =>
    t (fun i => rankTwoShear p X (-K / (1 + K * p X)) (v i))) hz
  simpa only [rankTwoShearTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    rankTwoShear_apply_inverse p X K hden, zero_apply] using he

@[simp] theorem rankTwoShearTensor_zero {n : ℕ} (p : Model (2 * n) →L[ℝ] ℝ)
    (X : Model (2 * n)) (s : SquaredCanonicalTensor n) : rankTwoShearTensor p X 0 s = s := by
  ext v
  simp [rankTwoShearTensor]

section SmoothShear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set F}
  {p : F → E →L[ℝ] ℝ} {X : F → E} {K : F → ℝ}

/-- The shear is jointly smooth in its covector, Hamiltonian vector and
base coefficient, with no restriction on the parameter dimension. -/
theorem contDiffOn_rankTwoShear (hp : ContDiffOn ℝ ∞ p U)
    (hX : ContDiffOn ℝ ∞ X U) (hK : ContDiffOn ℝ ∞ K U) :
    ContDiffOn ℝ ∞ (fun z => rankTwoShear (p z) (X z) (K z)) U :=
  contDiffOn_const.add (hK.smul (hp.smulRight hX))

theorem contDiffOn_rankTwoShearComplex {J : F → E →L[ℝ] E}
    (hp : ContDiffOn ℝ ∞ p U) (hX : ContDiffOn ℝ ∞ X U)
    (hK : ContDiffOn ℝ ∞ K U) (hJ : ContDiffOn ℝ ∞ J U)
    (hden : ∀ z ∈ U, 1 + K z * p z (X z) ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => rankTwoShearComplex (p z) (X z) (K z) (J z)) U :=
  (contDiffOn_rankTwoShear hp hX
    (hK.neg.div (contDiffOn_const.add (hK.mul (hp.clm_apply hX))) hden)).clm_comp
      (hJ.clm_comp (contDiffOn_rankTwoShear hp hX hK))

theorem contDiffOn_rankTwoShearTensor {n : ℕ}
    {p : F → Model (2 * n) →L[ℝ] ℝ} {X : F → Model (2 * n)}
    {s : F → SquaredCanonicalTensor n}
    (hp : ContDiffOn ℝ ∞ p U) (hX : ContDiffOn ℝ ∞ X U)
    (hK : ContDiffOn ℝ ∞ K U) (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (fun z => rankTwoShearTensor (p z) (X z) (K z) (s z)) U := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ⊕ Fin n => Model (2 * n))
    (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ
  have hC : ContDiff ℝ ∞ (fun L => C L) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (F := SquaredCanonicalTensor n →L[ℝ] SquaredCanonicalTensor n) C
  exact (hC.comp_contDiffOn
    (contDiffOn_pi.mpr (fun _ => contDiffOn_rankTwoShear hp hX hK))).clm_apply hs

end SmoothShear

namespace SmoothManifold
variable {d : ℕ} (M : SmoothManifold d)

/-- The actual Hamiltonian of the imaginary differential defines the
native tangent shear for the prescribed rank-two update. -/
def rankTwoTangentShear (omega : M.Form 2) (x : M.Point)
    (homega : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ) (K : ℝ) :
    M.Tangent x →L[ℝ] M.Tangent x :=
  rankTwoShear p (M.hamiltonianVector omega x homega q) K

theorem rankTwoTangentShear_form (omega : M.Form 2)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) (K : ℝ)
    (x : M.Point) (homega : M.Nondegenerate omega x) (v w : M.Tangent x) :
    evalTwo omega x (M.rankTwoTangentShear omega x homega (p x) (q x) K v)
      (M.rankTwoTangentShear omega x homega (p x) (q x) K w) =
        evalTwo (M.rankTwoForm omega p q K) x v w :=
  rankTwoShear_form (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    (p x) (q x) _ (M.hamiltonianVector_contraction omega x homega (q x)) K v w

theorem rankTwoTangentShear_isInvertible (omega : M.Form 2) (x : M.Point)
    (homega : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ) (K : ℝ)
    (hden : 1 + K * M.rankTwoPairing omega x homega p q ≠ 0) :
    (M.rankTwoTangentShear omega x homega p q K).IsInvertible :=
  rankTwoShear_isInvertible p _ K hden

/-- The shear identifies the actual exterior derivative of the updated
primitive, for arbitrary smooth complex maps, including the tailored map. -/
theorem rankTwoTangentShear_primitive (alpha : M.Form 1) (f : M.Point → ℂ)
    (halpha : M.IsSmoothForm alpha) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (K : ℝ) (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (v w : M.Tangent x) :
    let p := Complex.reCLM.comp (complexDifferential M f x)
    let q := Complex.imCLM.comp (complexDifferential M f x)
    evalTwo (M.exteriorDerivative alpha) x
      (M.rankTwoTangentShear (M.exteriorDerivative alpha) x hnd p q K v)
      (M.rankTwoTangentShear (M.exteriorDerivative alpha) x hnd p q K w) =
        evalTwo (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) x v w := by
  dsimp only
  rw [M.rankTwoTangentShear_form (M.exteriorDerivative alpha)
    (fun y => Complex.reCLM.comp (complexDifferential M f y))
    (fun y => Complex.imCLM.comp (complexDifferential M f y)),
    M.evalTwo_rankTwoForm, M.evalTwo_exteriorDerivative_rankTwoPrimitive halpha hf]
  rfl

end SmoothManifold
end FsFltz.Geometry
