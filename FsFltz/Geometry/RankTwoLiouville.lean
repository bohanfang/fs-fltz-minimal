import FsFltz.Geometry.SymplecticBasis
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Geometry.FormScalarDerivative

/-!
# Rank-two perturbations and the actual Liouville vector

Source: `geometric-part-fsf-proof.tex`, lines 1119–1150,
`eq:ranktwo`, `eq:rankbase`, and `eq:rankphi`.
Hamiltonian vectors are obtained from the nondegenerate alternating form,
using Mathlib's equivalence with its dual. The perturbation and all
contraction formulas use the actual linear forms on the tangent fiber.
-/

noncomputable section

open scoped Manifold ContDiff

namespace FsFltz.Geometry
namespace SymplecticAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (omega : LinearMap.BilinForm ℝ E)

/-- Alternation converts native left nondegeneracy into Mathlib's two-sided
nondegeneracy; no auxiliary symplectic structure is introduced. -/
theorem nondegenerate_of_isAlt_separatingLeft (homega : omega.IsAlt) (hnd : omega.SeparatingLeft) :
    omega.Nondegenerate := by
  refine ⟨hnd, ?_⟩
  intro v hv
  apply hnd v
  intro w
  rw [← LinearMap.IsAlt.neg homega, hv w, neg_zero]

variable [FiniteDimensional ℝ E]

/-- The Hamiltonian vector with convention `omega(X_p,·)=p`, determined by the
actual nondegenerate bilinear interpretation of the alternating form. -/
def hamiltonianVector (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p : E →ₗ[ℝ] ℝ) : E :=
  (omega.toDual (nondegenerate_of_isAlt_separatingLeft omega homega hnd)).symm p

@[simp] theorem hamiltonianVector_contraction (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p : E →ₗ[ℝ] ℝ) (v : E) :
    omega (hamiltonianVector omega homega hnd p) v = p v :=
  LinearMap.BilinForm.apply_toDual_symm_apply p v

@[simp] theorem hamiltonianVector_self (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p : E →ₗ[ℝ] ℝ) : p (hamiltonianVector omega homega hnd p) = 0 := by
  rw [← hamiltonianVector_contraction omega homega hnd]
  exact homega _

theorem hamiltonianVector_cross (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) :
    q (hamiltonianVector omega homega hnd p) = -p (hamiltonianVector omega homega hnd q) := by
  rw [← hamiltonianVector_contraction omega homega hnd q,
    ← hamiltonianVector_contraction omega homega hnd p]
  exact (LinearMap.IsAlt.neg homega _ _).symm

/-- The Poisson scalar in the source's contraction convention. -/
def rankTwoPairing (homega : omega.IsAlt) (hnd : omega.SeparatingLeft) (p q : E →ₗ[ℝ] ℝ) : ℝ :=
  p (hamiltonianVector omega homega hnd q)

/-- Exact nondegeneracy criterion for the rank-two update `omega+K p∧q`. -/
theorem rankTwo_nondegenerate_iff (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) (K : ℝ) :
    (∀ v : E, (∀ w, omega v w + K * (p v * q w - q v * p w) = 0) → v = 0) ↔
      1 + K * rankTwoPairing omega homega hnd p q ≠ 0 := by
  let Xp := hamiltonianVector omega homega hnd p
  let Xq := hamiltonianVector omega homega hnd q
  have hp : ∀ w, omega Xp w = p w := hamiltonianVector_contraction omega homega hnd p
  have hq : ∀ w, omega Xq w = q w := hamiltonianVector_contraction omega homega hnd q
  have hpp : p Xp = 0 := hamiltonianVector_self omega homega hnd p
  have hqq : q Xq = 0 := hamiltonianVector_self omega homega hnd q
  have hqp : q Xp = -p Xq := hamiltonianVector_cross omega homega hnd p q
  change _ ↔ 1 + K * p Xq ≠ 0
  constructor
  · intro h hzero
    have hpX : p Xq ≠ 0 := by
      intro hp0
      rw [hp0] at hzero
      norm_num at hzero
    have hXp0 : Xp ≠ 0 := by
      intro hx
      have h := hp Xq
      rw [hx, map_zero, LinearMap.zero_apply] at h
      exact hpX h.symm
    apply hXp0
    apply h Xp
    intro w
    rw [hp w, hpp, hqp]
    calc
      p w + K * (0 * q w - -p Xq * p w) = (1 + K * p Xq) * p w := by ring
      _ = 0 := by rw [hzero, zero_mul]
  · intro hden v hv
    have hvXp := hv Xp
    have hvXq := hv Xq
    rw [← LinearMap.IsAlt.neg homega, hp v, hpp, hqp] at hvXp
    rw [← LinearMap.IsAlt.neg homega, hq v, hqq] at hvXq
    have hpv : p v = 0 := by
      have hmul : (1 + K * p Xq) * p v = 0 := by nlinarith [hvXp]
      exact (mul_eq_zero.mp hmul).resolve_left hden
    have hqv : q v = 0 := by
      have hmul : (1 + K * p Xq) * q v = 0 := by nlinarith [hvXq]
      exact (mul_eq_zero.mp hmul).resolve_left hden
    apply hnd v
    intro w
    simpa [hpv, hqv] using hv w

/-- The literal rank-two Liouville formula in the source. -/
def rankTwoLiouvilleVector (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) (A B K : ℝ) (Z₀ : E) : E :=
  Z₀ + (K / (1 + K * rankTwoPairing omega homega hnd p q)) •
    ((q Z₀ - B / 2) • hamiltonianVector omega homega hnd p +
      (A / 2 - p Z₀) • hamiltonianVector omega homega hnd q)

/-- The displayed vector solves the contraction equation for the actual
rank-two form and the primitive increment `K(Aq−Bp)/2`. -/
theorem rankTwoLiouvilleVector_contraction (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) (A B K : ℝ) (Z₀ w : E)
    (hden : 1 + K * rankTwoPairing omega homega hnd p q ≠ 0) :
    omega (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) w +
        K * (p (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) * q w -
          q (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) * p w) =
      omega Z₀ w + K / 2 * (A * q w - B * p w) := by
  have hcross := hamiltonianVector_cross omega homega hnd p q
  simp only [rankTwoLiouvilleVector, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hamiltonianVector_contraction,
    hamiltonianVector_self, hcross]
  unfold rankTwoPairing at hden ⊢
  field_simp
  ring

/-- `eq:rankphi` for any actual scalar covector, with the source numerator. -/
theorem rankTwoLiouvilleVector_covector (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q r : E →ₗ[ℝ] ℝ) (A B K : ℝ) (Z₀ : E)
    (hden : 1 + K * rankTwoPairing omega homega hnd p q ≠ 0) :
    r (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) =
      (r Z₀ + K * (r Z₀ * rankTwoPairing omega homega hnd p q +
        (q Z₀ - B / 2) * r (hamiltonianVector omega homega hnd p) +
        (A / 2 - p Z₀) * r (hamiltonianVector omega homega hnd q))) /
        (1 + K * rankTwoPairing omega homega hnd p q) := by
  simp only [rankTwoLiouvilleVector, map_add, map_smul, smul_eq_mul]
  field_simp
  ring

/-- The real part of `eq:rankbase`, with the exact denominator. -/
theorem rankTwoLiouvilleVector_first (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) (A B K : ℝ) (Z₀ : E)
    (hden : 1 + K * rankTwoPairing omega homega hnd p q ≠ 0) :
    p (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) =
      (p Z₀ + K * rankTwoPairing omega homega hnd p q * A / 2) /
        (1 + K * rankTwoPairing omega homega hnd p q) := by
  rw [rankTwoLiouvilleVector_covector omega homega hnd p q p A B K Z₀ hden,
    hamiltonianVector_self]
  unfold rankTwoPairing
  congr 1
  ring

/-- The imaginary part of `eq:rankbase`, with the same denominator. -/
theorem rankTwoLiouvilleVector_second (homega : omega.IsAlt) (hnd : omega.SeparatingLeft)
    (p q : E →ₗ[ℝ] ℝ) (A B K : ℝ) (Z₀ : E)
    (hden : 1 + K * rankTwoPairing omega homega hnd p q ≠ 0) :
    q (rankTwoLiouvilleVector omega homega hnd p q A B K Z₀) =
      (q Z₀ + K * rankTwoPairing omega homega hnd p q * B / 2) /
        (1 + K * rankTwoPairing omega homega hnd p q) := by
  rw [rankTwoLiouvilleVector_covector omega homega hnd p q q A B K Z₀ hden,
    hamiltonianVector_self, hamiltonianVector_cross omega homega hnd p q]
  unfold rankTwoPairing
  congr 1
  ring

end SymplecticAlgebra

section CovectorWedge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The literal native wedge of two continuous covectors. -/
def covectorWedge (p q : E →L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := p (v 0) * q (v 1) - q (v 0) * p (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add] <;> ring
  map_update_smul' v i c x := by
    fin_cases i <;> simp [map_smul, smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all <;> ring
  cont := ((p.continuous.comp (continuous_apply 0)).mul
      (q.continuous.comp (continuous_apply 1))).sub
    ((q.continuous.comp (continuous_apply 0)).mul (p.continuous.comp (continuous_apply 1)))

@[simp] theorem covectorWedge_apply (p q : E →L[ℝ] ℝ) (v w : E) :
    covectorWedge p q ![v, w] = p v * q w - q v * p w := rfl

end CovectorWedge

namespace SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- The rank-two updated two-form, in the project's native form fibers. -/
def rankTwoForm (omega : M.Form 2)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) (K : ℝ) : M.Form 2 :=
  fun x => omega x + K • covectorWedge (p x) (q x)

@[simp] theorem evalTwo_rankTwoForm (omega : M.Form 2)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) (K : ℝ)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.rankTwoForm omega p q K) x v w =
      evalTwo omega x v w + K * (p x v * q x w - q x v * p x w) := rfl

/-- The native Hamiltonian vector is produced from actual nondegeneracy. -/
def hamiltonianVector (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p : M.Tangent x →L[ℝ] ℝ) : M.Tangent x :=
  SymplecticAlgebra.hamiltonianVector
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap) hnd p.toLinearMap

@[simp] theorem hamiltonianVector_contraction (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p : M.Tangent x →L[ℝ] ℝ) (v : M.Tangent x) :
    evalTwo omega x (M.hamiltonianVector omega x hnd p) v = p v :=
  SymplecticAlgebra.hamiltonianVector_contraction
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap) hnd p.toLinearMap v

/-- The actual source scalar `dA(X_B)` at a native tangent fiber. -/
def rankTwoPairing (omega : M.Form 2) (x : M.Point) (hnd : M.Nondegenerate omega x)
    (p q : M.Tangent x →L[ℝ] ℝ) : ℝ :=
  p (M.hamiltonianVector omega x hnd q)

/-- Exact nondegeneracy criterion for the actual updated two-form. -/
theorem nondegenerate_rankTwoForm_iff (omega : M.Form 2)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ) (K : ℝ)
    (x : M.Point) (hnd : M.Nondegenerate omega x) :
    M.Nondegenerate (M.rankTwoForm omega p q K) x ↔
      1 + K * M.rankTwoPairing omega x hnd (p x) (q x) ≠ 0 := by
  simp only [Nondegenerate, evalTwo_rankTwoForm]
  exact SymplecticAlgebra.rankTwo_nondegenerate_iff
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd (p x).toLinearMap (q x).toLinearMap K

/-- Native form of the displayed rank-two Liouville vector. -/
def rankTwoLiouvilleVector (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ)
    (A B K : ℝ) (Z₀ : M.Tangent x) : M.Tangent x :=
  SymplecticAlgebra.rankTwoLiouvilleVector
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd p.toLinearMap q.toLinearMap A B K Z₀

theorem rankTwoLiouvilleVector_formula (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ)
    (A B K : ℝ) (Z₀ : M.Tangent x) :
    M.rankTwoLiouvilleVector omega x hnd p q A B K Z₀ =
      Z₀ + (K / (1 + K * M.rankTwoPairing omega x hnd p q)) •
        ((q Z₀ - B / 2) • M.hamiltonianVector omega x hnd p +
          (A / 2 - p Z₀) • M.hamiltonianVector omega x hnd q) := rfl

/-- The actual native updated form contracts with the literal source vector
to give the literal plane-primitive increment. -/
theorem rankTwoLiouvilleVector_contraction (omega : M.Form 2)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (x : M.Point) (hnd : M.Nondegenerate omega x) (A B K : ℝ)
    (Z₀ w : M.Tangent x)
    (hden : 1 + K * M.rankTwoPairing omega x hnd (p x) (q x) ≠ 0) :
    evalTwo (M.rankTwoForm omega p q K) x
        (M.rankTwoLiouvilleVector omega x hnd (p x) (q x) A B K Z₀) w =
      evalTwo omega x Z₀ w + K / 2 * (A * q x w - B * p x w) :=
  SymplecticAlgebra.rankTwoLiouvilleVector_contraction
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd (p x).toLinearMap (q x).toLinearMap A B K Z₀ w hden

/-- The literal pullback of the standard plane primitive by an arbitrary
complex map. Its definition uses the actual real manifold differential. -/
def planePullbackForm (f : M.Point → ℂ) : M.Form 1 :=
  fun x => (planeLambda (f x)).compContinuousLinearMap (complexDifferential M f x)

@[simp] theorem evalOne_planePullbackForm (f : M.Point → ℂ)
    (x : M.Point) (v : M.Tangent x) :
    evalOne (M.planePullbackForm f) x v =
      (1 / 2 : ℝ) * ((f x).re * (complexDifferential M f x v).im -
        (f x).im * (complexDifferential M f x v).re) := by
  simp [planePullbackForm, evalOne, planeLambda_apply]

/-- The plane pullback primitive is smooth for any smooth real complex-valued
map; no holomorphic hypothesis is used. -/
theorem isSmoothForm_planePullbackForm {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) :
    M.IsSmoothForm (M.planePullbackForm f) := by
  have hre := Complex.reCLM.contDiff.contMDiff.comp hf
  have him := Complex.imCLM.contDiff.contMDiff.comp hf
  have hp := isSmoothForm_complexDifferential_comp M hf Complex.reCLM
  have hq := isSmoothForm_complexDifferential_comp M hf Complex.imCLM
  convert ((hq.function_smul hre).sub (hp.function_smul him)).smul (1 / 2 : ℝ) using 1
  funext x
  ext vs
  simp [planePullbackForm, planeLambda, covectorForm]

/-- In a native chart, the plane pullback is precisely the Euclidean pullback
of the same plane primitive, with the actual derivative of the chart expression. -/
theorem formInChart_planePullbackForm {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (a : M.Point) (y : Model d) (hy : y ∈ (chartAt (Model d) a).target) :
    M.formInChart a (M.planePullbackForm f) y =
      (planeLambda ((f ∘ (chartAt (Model d) a).symm) y)).compContinuousLinearMap
        (fderiv ℝ (f ∘ (chartAt (Model d) a).symm) y) := by
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp y (hf.mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy)]
  ext vs
  rfl

/-- The native chart derivative of a complex map, applied to the chart
tangent image, is its actual manifold differential. -/
theorem fderiv_complex_in_chart {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (a x : M.Point) (hx : x ∈ (chartAt (Model d) a).source) (v : M.Tangent x) :
    fderiv ℝ (f ∘ (chartAt (Model d) a).symm) (chartAt (Model d) a x)
      (M.chartTangentMap a x v) = complexDifferential M f x v := by
  let c := chartAt (Model d) a
  have hy := c.map_source hx
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (c x) (hf.mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy),
    c.left_inv hx]
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) f x)
    ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c.symm (c x))
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) c x) v)) = _
  exact congrArg (fun u => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) f x u)
    (congrArg (fun L => L v)
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).symm_comp_deriv hx))

/-- The actual differential of the plane pullback primitive is `dA∧dB`,
proved by native chart pullback calculus for every smooth nonholomorphic map. -/
theorem evalTwo_exteriorDerivative_planePullbackForm {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (M.planePullbackForm f)) x v w =
      (complexDifferential M f x v).re * (complexDifferential M f x w).im -
        (complexDifferential M f x v).im * (complexDifferential M f x w).re := by
  let c := chartAt (Model d) x
  have hx : x ∈ c.source := mem_chart_source _ _
  have hy := c.map_source hx
  have hci : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm (c x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := x)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hfc : ContDiffAt ℝ ∞ (f ∘ c.symm) (c x) :=
    (hf.contMDiffAt.comp (c x) hci).contDiffAt
  have he : M.formInChart x (M.planePullbackForm f) =ᶠ[nhds (c x)]
      fun y => (planeLambda ((f ∘ c.symm) y)).compContinuousLinearMap
        (fderiv ℝ (f ∘ c.symm) y) := by
    filter_upwards [c.open_target.mem_nhds hy] with y hyt
    exact M.formInChart_planePullbackForm hf x y hyt
  change extDeriv (M.formInChart x (M.planePullbackForm f)) (c x)
    (M.chartTangentMap x x ∘ ![v, w]) = _
  rw [he.extDeriv_eq,
    extDeriv_pullback (contDiff_planeLambda.differentiable (by simp) _) hfc (by simp)]
  have hpair : (fderiv ℝ (f ∘ c.symm) (c x)) ∘ M.chartTangentMap x x ∘ ![v, w] =
      ![complexDifferential M f x v, complexDifferential M f x w] := by
    ext i
    fin_cases i <;> exact M.fderiv_complex_in_chart hf x x hx _
  change extDeriv planeLambda ((f ∘ c.symm) (c x))
    ((fderiv ℝ (f ∘ c.symm) (c x)) ∘ M.chartTangentMap x x ∘ ![v, w]) = _
  rw [hpair, extDeriv_planeLambda]

/-- The prescribed primitive update by the pullback of the plane primitive. -/
def rankTwoPrimitive (alpha : M.Form 1) (f : M.Point → ℂ) (K : ℝ) : M.Form 1 :=
  alpha + K • M.planePullbackForm f

/-- Smoothness of the actual updated primitive. -/
theorem isSmoothForm_rankTwoPrimitive {alpha : M.Form 1} {f : M.Point → ℂ}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ) :
    M.IsSmoothForm (M.rankTwoPrimitive alpha f K) :=
  halpha.add ((M.isSmoothForm_planePullbackForm hf).smul K)

@[simp] theorem evalOne_rankTwoPrimitive (alpha : M.Form 1) (f : M.Point → ℂ)
    (K : ℝ) (x : M.Point) (v : M.Tangent x) :
    evalOne (M.rankTwoPrimitive alpha f K) x v =
      evalOne alpha x v + K / 2 * ((f x).re * (complexDifferential M f x v).im -
        (f x).im * (complexDifferential M f x v).re) := by
  change evalOne alpha x v + K * evalOne (M.planePullbackForm f) x v = _
  rw [M.evalOne_planePullbackForm]
  ring

/-- The actual exterior derivative of the updated primitive has the rank-two
expression for every smooth map, without any differential certificate. -/
theorem evalTwo_exteriorDerivative_rankTwoPrimitive {alpha : M.Form 1} {f : M.Point → ℂ}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) x v w =
      evalTwo (M.exteriorDerivative alpha) x v w +
        K * ((complexDifferential M f x v).re * (complexDifferential M f x w).im -
          (complexDifferential M f x v).im * (complexDifferential M f x w).re) := by
  have hx : chartAt (Model d) x x ∈ (chartAt (Model d) x).target :=
    (chartAt (Model d) x).map_source (mem_chart_source _ _)
  have ha := ((halpha x).contDiffAt
    ((chartAt (Model d) x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hb := (((M.isSmoothForm_planePullbackForm hf) x).contDiffAt
    ((chartAt (Model d) x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have he : M.exteriorDerivative (M.rankTwoPrimitive alpha f K) x =
      M.exteriorDerivative alpha x + K • M.exteriorDerivative (M.planePullbackForm f) x := by
    unfold exteriorDerivative rankTwoPrimitive
    rw [formInChart_add, formInChart_smul, extDeriv_add ha (hb.const_smul K), extDeriv_smul]
    ext vs
    rfl
  rw [show evalTwo (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) x v w =
      evalTwo (M.exteriorDerivative alpha) x v w +
        K * evalTwo (M.exteriorDerivative (M.planePullbackForm f)) x v w from
      congrArg (fun beta => beta ![v, w]) he]
  rw [M.evalTwo_exteriorDerivative_planePullbackForm hf]

/-- The Poisson scalar of an actual complex map for the given primitive. -/
def planePairing (alpha : M.Form 1) (f : M.Point → ℂ) (x : M.Point)
    (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x) : ℝ :=
  M.rankTwoPairing (M.exteriorDerivative alpha) x hnd
    (Complex.reCLM.comp (complexDifferential M f x))
    (Complex.imCLM.comp (complexDifferential M f x))

/-- The exact source criterion, now for the actual exterior derivative of
the actual primitive rather than a supplied perturbation formula. -/
theorem nondegenerate_exteriorDerivative_rankTwoPrimitive_iff
    {alpha : M.Form 1} {f : M.Point → ℂ}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x) :
    M.Nondegenerate (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) x ↔
      1 + K * M.planePairing alpha f x hnd ≠ 0 := by
  simp only [Nondegenerate, M.evalTwo_exteriorDerivative_rankTwoPrimitive halpha hf]
  exact SymplecticAlgebra.rankTwo_nondegenerate_iff
    (SymplecticAlgebra.twoFormBilin (M.exteriorDerivative alpha x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (M.exteriorDerivative alpha x).toAlternatingMap)
    hnd (Complex.reCLM.comp (complexDifferential M f x)).toLinearMap
    (Complex.imCLM.comp (complexDifferential M f x)).toLinearMap K

/-- `eq:ranktwo` for the actual form-determined native Liouville vector. -/
theorem liouvilleVector_rankTwoPrimitive {alpha : M.Form 1} {f : M.Point → ℂ}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hden : 1 + K * M.planePairing alpha f x hnd ≠ 0) :
    M.liouvilleVector (M.rankTwoPrimitive alpha f K) x =
      M.rankTwoLiouvilleVector (M.exteriorDerivative alpha) x hnd
        (Complex.reCLM.comp (complexDifferential M f x))
        (Complex.imCLM.comp (complexDifferential M f x)) (f x).re (f x).im K
        (M.liouvilleVector alpha x) := by
  apply M.liouvilleVector_eq (M.rankTwoPrimitive alpha f K) x
    ((M.nondegenerate_exteriorDerivative_rankTwoPrimitive_iff halpha hf K x hnd).mpr hden)
  intro w
  rw [M.evalTwo_exteriorDerivative_rankTwoPrimitive halpha hf,
    M.evalOne_rankTwoPrimitive]
  have he := M.rankTwoLiouvilleVector_contraction (M.exteriorDerivative alpha)
    (fun y => Complex.reCLM.comp (complexDifferential M f y))
    (fun y => Complex.imCLM.comp (complexDifferential M f y)) x hnd
    (f x).re (f x).im K (M.liouvilleVector alpha x) w hden
  rw [M.evalTwo_rankTwoForm] at he
  rw [M.liouvilleVector_contraction alpha x (M.liouvilleEquation_exists alpha x hnd) w] at he
  exact he

/-- `eq:rankbase` for the actual complex manifold differential and actual
updated Liouville vector, with no holomorphic-map hypothesis. -/
theorem complexDifferential_liouvilleVector_rankTwoPrimitive
    {alpha : M.Form 1} {f : M.Point → ℂ}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hden : 1 + K * M.planePairing alpha f x hnd ≠ 0) :
    complexDifferential M f x (M.liouvilleVector (M.rankTwoPrimitive alpha f K) x) =
      (complexDifferential M f x (M.liouvilleVector alpha x) +
        (K * M.planePairing alpha f x hnd / 2) • f x) /
          ((1 + K * M.planePairing alpha f x hnd : ℝ) : ℂ) := by
  rw [M.liouvilleVector_rankTwoPrimitive halpha hf K x hnd hden]
  apply Complex.ext
  · simp only [Complex.div_ofReal_re, Complex.add_re, Complex.smul_re, smul_eq_mul]
    convert SymplecticAlgebra.rankTwoLiouvilleVector_first
      (SymplecticAlgebra.twoFormBilin (M.exteriorDerivative alpha x).toAlternatingMap)
      (SymplecticAlgebra.twoFormBilin_isAlt (M.exteriorDerivative alpha x).toAlternatingMap)
      hnd (Complex.reCLM.comp (complexDifferential M f x)).toLinearMap
      (Complex.imCLM.comp (complexDifferential M f x)).toLinearMap
      (f x).re (f x).im K (M.liouvilleVector alpha x) hden using 1
    · rfl
    · change _ = (((complexDifferential M f x) (M.liouvilleVector alpha x)).re +
        K * M.planePairing alpha f x hnd * (f x).re / 2) /
          (1 + K * M.planePairing alpha f x hnd)
      ring
  · simp only [Complex.div_ofReal_im, Complex.add_im, Complex.smul_im, smul_eq_mul]
    convert SymplecticAlgebra.rankTwoLiouvilleVector_second
      (SymplecticAlgebra.twoFormBilin (M.exteriorDerivative alpha x).toAlternatingMap)
      (SymplecticAlgebra.twoFormBilin_isAlt (M.exteriorDerivative alpha x).toAlternatingMap)
      hnd (Complex.reCLM.comp (complexDifferential M f x)).toLinearMap
      (Complex.imCLM.comp (complexDifferential M f x)).toLinearMap
      (f x).re (f x).im K (M.liouvilleVector alpha x) hden using 1
    · rfl
    · change _ = (((complexDifferential M f x) (M.liouvilleVector alpha x)).im +
        K * M.planePairing alpha f x hnd * (f x).im / 2) /
          (1 + K * M.planePairing alpha f x hnd)
      ring

/-- `eq:rankphi` for the actual scalar manifold derivative evaluated on the
actual updated Liouville vector. The source's `B_f` is expanded literally. -/
theorem scalarDerivative_liouvilleVector_rankTwoPrimitive
    {alpha : M.Form 1} {f : M.Point → ℂ} (φ : M.Point → ℝ)
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (K : ℝ)
    (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hden : 1 + K * M.planePairing alpha f x hnd ≠ 0) :
    let Z₀ := M.liouvilleVector alpha x
    let π := M.planePairing alpha f x hnd
    let X_A := M.hamiltonianVector (M.exteriorDerivative alpha) x hnd
      (Complex.reCLM.comp (complexDifferential M f x))
    let X_B := M.hamiltonianVector (M.exteriorDerivative alpha) x hnd
      (Complex.imCLM.comp (complexDifferential M f x))
    let C₀ := M.scalarDerivative φ x Z₀
    let B_f := C₀ * π +
      ((complexDifferential M f x Z₀).im - (f x).im / 2) * M.scalarDerivative φ x X_A +
      ((f x).re / 2 - (complexDifferential M f x Z₀).re) * M.scalarDerivative φ x X_B
    M.scalarDerivative φ x (M.liouvilleVector (M.rankTwoPrimitive alpha f K) x) =
      (C₀ + K * B_f) / (1 + K * π) := by
  dsimp only
  rw [M.liouvilleVector_rankTwoPrimitive halpha hf K x hnd hden]
  exact SymplecticAlgebra.rankTwoLiouvilleVector_covector
    (SymplecticAlgebra.twoFormBilin (M.exteriorDerivative alpha x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (M.exteriorDerivative alpha x).toAlternatingMap)
    hnd (Complex.reCLM.comp (complexDifferential M f x)).toLinearMap
    (Complex.imCLM.comp (complexDifferential M f x)).toLinearMap
    (differentialCovector M φ x).toLinearMap (f x).re (f x).im K
    (M.liouvilleVector alpha x) hden

/-- Nonnegative Poisson scalar gives actual symplecticity for every
nonnegative base coefficient, once the original differential is symplectic.
Smoothness and closedness are supplied by the proved native exterior calculus. -/
theorem isSymplecticOn_exteriorDerivative_rankTwoPrimitive_of_nonneg
    {alpha : M.Form 1} {f : M.Point → ℂ} {s : Set M.Point}
    (halpha : M.IsSmoothForm alpha)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (hnd : ∀ x ∈ s, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hpi : ∀ x, ∀ hx : x ∈ s, 0 ≤ M.planePairing alpha f x (hnd x hx))
    {K : ℝ} (hK : 0 ≤ K) :
    M.IsSymplecticOn (M.exteriorDerivative (M.rankTwoPrimitive alpha f K)) s := by
  apply (M.isSymplecticOn_exteriorDerivative_iff _
    (M.isSmoothForm_rankTwoPrimitive halpha hf K) s).mpr
  intro x hx
  apply (M.nondegenerate_exteriorDerivative_rankTwoPrimitive_iff
    halpha hf K x (hnd x hx)).mpr
  exact ne_of_gt (zero_lt_one.trans_le (le_add_of_nonneg_right (mul_nonneg hK (hpi x hx))))

end SmoothManifold

/-- The generic plane pullback is literally the project's existing prescribed
superpotential plane primitive. -/
theorem planePullbackForm_W {n : ℕ} (I : ToricInput n) :
    (lgManifold n).planePullbackForm (W I) = superpotentialPlaneForm I := by
  funext y
  ext vs
  simp [SmoothManifold.planePullbackForm, planeLambda, superpotentialPlaneForm, covectorForm]

/-- The generic update recovers the existing original primitive exactly. -/
theorem rankTwoPrimitive_lambda0Form {n : ℕ} (I : ToricInput n) (K : ℝ) :
    (lgManifold n).rankTwoPrimitive (lambda0Form n) (W I) K = lambdaKForm I K := by
  simp only [SmoothManifold.rankTwoPrimitive, planePullbackForm_W, lambdaKForm]

end FsFltz.Geometry
