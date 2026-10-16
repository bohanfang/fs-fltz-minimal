import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Finite toric inputs, quotient characters, and the literal FLTZ link

This is the first foundation layer of `geoemtric-part-fsf.tex`, Section
`sec:data` (lines 57–115), and handoff `sec:lean` (lines 778–782).
The basis of the lattice identifies its real space and the real dual with
coordinate vectors. The torus has period `2 * Real.pi`; no real-valued angle
function on the torus is chosen. These definitions do not assert fan
smoothness/completeness, smooth descent of differential forms, or the target
geometric existence theorem.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

/-- The based lattice `N ≃ ℤⁿ` in `sec:data`, line 57. -/
abbrev Lattice (n : ℕ) := Fin n → ℤ

/-- Basis coordinates for `N_ℝ` and `M_ℝ`. -/
abbrev RealSpace (n : ℕ) := Fin n → ℝ

/-- The quotient `M_ℝ / (2π M)`, componentwise in the fixed dual basis. -/
abbrev Torus (n : ℕ) := Fin n → AddCircle (2 * Real.pi)

/-- The logarithmic Landau–Ginzburg ambient `Y = M_ℝ × T`. -/
abbrev LGSpace (n : ℕ) := RealSpace n × Torus n

/-- Basis presentation of the cotangent bundle `T* T = T × N_ℝ`. -/
abbrev Cotangent (n : ℕ) := Torus n × RealSpace n

/-- Scalar extension of a lattice vector. -/
def latticeReal {n : ℕ} (v : Lattice n) : RealSpace n := fun j => v j

/-- Lattice/dual pairing in the fixed bases. -/
def pairing {n : ℕ} (v : Lattice n) (u : RealSpace n) : ℝ :=
  ∑ j, (v j : ℝ) * u j

/-- Quotient map on angle coordinates. -/
def angleQuotient {n : ℕ} (θ : RealSpace n) : Torus n := fun j => θ j

/-- Integral characters are first valued in the additive quotient circle. -/
def integralAngle {n : ℕ} (v : Lattice n) (θ : Torus n) : AddCircle (2 * Real.pi) :=
  ∑ j, v j • θ j

/-- The associated unit-circle character. -/
def character {n : ℕ} (v : Lattice n) (θ : Torus n) : Circle :=
  AddCircle.toCircle (integralAngle v θ)

/-- A Laurent monomial, defined directly on `Y`, as in `sec:data`, line 70. -/
def monomial {n : ℕ} (c : ℂ) (v : Lattice n) (y : LGSpace n) : ℂ :=
  c * Complex.exp (pairing v y.1) * (character v y.2 : ℂ)

/-- The integral pairing descends exactly to the quotient angle. -/
theorem integralAngle_angleQuotient {n : ℕ} (v : Lattice n) (θ : RealSpace n) :
    integralAngle v (angleQuotient θ) = (pairing v θ : AddCircle (2 * Real.pi)) := by
  simp only [integralAngle, angleQuotient, pairing, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  exact (QuotientAddGroup.mk_sum _ _).symm

/-- On representatives the quotient character is `exp(i⟨v,θ⟩)`. -/
theorem character_angleQuotient {n : ℕ} (v : Lattice n) (θ : RealSpace n) :
    (character v (angleQuotient θ) : ℂ) =
      Complex.exp ((pairing v θ : ℂ) * Complex.I) := by
  rw [character, integralAngle_angleQuotient, AddCircle.toCircle_apply_mk]
  simp [Real.pi_ne_zero, Circle.coe_exp]

/-- The defining quotient monomial has the literal exponential formula. -/
theorem monomial_angleQuotient {n : ℕ} (c : ℂ) (v : Lattice n)
    (u θ : RealSpace n) :
    monomial c v (u, angleQuotient θ) =
      c * Complex.exp ((pairing v u : ℂ) + (pairing v θ : ℂ) * Complex.I) := by
  rw [monomial, character_angleQuotient, Complex.exp_add]
  exact mul_assoc _ _ _

/-- The period lattice acts on real representative coordinates. -/
def periodShift {n : ℕ} (θ : RealSpace n) (k : Lattice n) : RealSpace n :=
  fun j => θ j + (k j : ℝ) * (2 * Real.pi)

/-- All lattice period shifts give literally the same torus point. -/
theorem angleQuotient_periodShift {n : ℕ} (θ : RealSpace n) (k : Lattice n) :
    angleQuotient (periodShift θ k) = angleQuotient θ := by
  funext j
  simp [angleQuotient, periodShift, ← zsmul_eq_mul]

/-- Every torus point has real representative coordinates. -/
theorem angleQuotient_surjective {n : ℕ} :
    Function.Surjective (angleQuotient : RealSpace n → Torus n) := by
  intro θ
  choose a ha using fun j => QuotientAddGroup.mk_surjective (θ j)
  exact ⟨a, funext ha⟩

/-- The componentwise model identifies exactly the prescribed period lattice,
so it is a quotient by `2π M`, rather than just a periodic parametrization. -/
theorem angleQuotient_eq_iff {n : ℕ} (θ η : RealSpace n) :
    angleQuotient θ = angleQuotient η ↔ ∃ k : Lattice n, θ = periodShift η k := by
  constructor
  · intro h
    have hcoord : ∀ j, ∃ k : ℤ, θ j = η j + (k : ℝ) * (2 * Real.pi) := by
      intro j
      have hs := sub_eq_zero.mpr (congrFun h j)
      change (θ j : AddCircle (2 * Real.pi)) - (η j : AddCircle (2 * Real.pi)) = 0 at hs
      rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at hs
      obtain ⟨k, hk⟩ := hs
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul] at hk
      linarith
    choose k hk using hcoord
    exact ⟨k, funext hk⟩
  · rintro ⟨k, rfl⟩
    exact angleQuotient_periodShift η k

/-- The period-`2π` condition used in the annihilator torus has its usual
representative formula, with an actual integer witness. -/
theorem integralAngle_eq_zero_iff {n : ℕ} (v : Lattice n) (θ : RealSpace n) :
    integralAngle v (angleQuotient θ) = 0 ↔
      ∃ k : ℤ, pairing v θ = (k : ℝ) * (2 * Real.pi) := by
  rw [integralAngle_angleQuotient, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, eq_comm]

/-- The polytope generated by a specified finite lattice vertex set. -/
def latticePolytope {n : ℕ} (V : Finset (Lattice n)) : Set (RealSpace n) :=
  convexHull ℝ (latticeReal '' (V : Set (Lattice n)))

/-- A face is exactly the subset of vertices lying on a supporting hyperplane.
For a polytope these are its exposed faces, including the empty and full face.
No list of faces is supplied independently of the actual polytope. -/
def IsPolytopeFace {n : ℕ} (V s : Finset (Lattice n)) : Prop :=
  s ⊆ V ∧ ∃ ℓ : RealSpace n →ₗ[ℝ] ℝ, ∃ a : ℝ,
    (∀ v ∈ V, ℓ (latticeReal v) ≤ a) ∧
    (∀ v ∈ V, v ∈ s ↔ ℓ (latticeReal v) = a)

/-- A facet is a maximal proper nonempty supporting face. -/
def IsPolytopeFacet {n : ℕ} (V s : Finset (Lattice n)) : Prop :=
  IsPolytopeFace V s ∧ s.Nonempty ∧ s ≠ V ∧
    ∀ t, IsPolytopeFace V t → t ≠ V → s ⊆ t → t = s

/-- The genuine finite input from `sec:data`, lines 57–70.
Zero interior gives the specified full dimension. The extreme-point equality
ensures the coefficient support is exactly the vertices, with no extra monomials.
Every actual facet's vertices form an integral basis. -/
structure ToricInput (n : ℕ) where
  positive_rank : 1 ≤ n
  vertices : Finset (Lattice n)
  vertices_exact : latticeReal '' (vertices : Set (Lattice n)) =
    (latticePolytope vertices).extremePoints ℝ
  zero_interior : (0 : RealSpace n) ∈ interior (latticePolytope vertices)
  facet_basis : ∀ s, IsPolytopeFacet vertices s →
    ∃ b : Module.Basis {v : Lattice n // v ∈ s} ℤ (Lattice n), ∀ v, b v = v.val
  coeff : {v : Lattice n // v ∈ vertices} → ℂ
  coeff_ne_zero : ∀ v, coeff v ≠ 0

/-- The superpotential contains precisely the monomials at the input vertices. -/
def W {n : ℕ} (I : ToricInput n) (y : LGSpace n) : ℂ :=
  ∑ v : {v : Lattice n // v ∈ I.vertices}, monomial (I.coeff v) v.val y

/-- The quotient-defined Laurent superpotential agrees with the source formula. -/
theorem W_angleQuotient {n : ℕ} (I : ToricInput n) (u θ : RealSpace n) :
    W I (u, angleQuotient θ) =
      ∑ v : {v : Lattice n // v ∈ I.vertices}, I.coeff v *
        Complex.exp ((pairing v.val u : ℂ) + (pairing v.val θ : ℂ) * Complex.I) := by
  simp only [W, monomial_angleQuotient]

/-- Periodicity of `W` follows from its quotient definition. -/
theorem W_periodShift {n : ℕ} (I : ToricInput n) (u θ : RealSpace n) (k : Lattice n) :
    W I (u, angleQuotient (periodShift θ k)) = W I (u, angleQuotient θ) := by
  rw [angleQuotient_periodShift]

/-- The positive cone generated by a finite vertex set. -/
def positiveCone {n : ℕ} (s : Finset (Lattice n)) : Set (RealSpace n) :=
  {p | ∃ a : Lattice n → ℝ, (∀ v ∈ s, 0 ≤ a v) ∧
    p = ∑ v ∈ s, a v • latticeReal v}

/-- The fan is zero together with cones over all nonempty proper faces.
Its fan axioms remain a foundational theorem to prove from the input. -/
def faceFan {n : ℕ} (I : ToricInput n) : Set (Set (RealSpace n)) :=
  {σ | σ = {0} ∨ ∃ s, IsPolytopeFace I.vertices s ∧ s.Nonempty ∧
    s ≠ I.vertices ∧ σ = positiveCone s}

/-- Literal annihilator torus from `eq:link`, lines 105–106. -/
def coneTorus {n : ℕ} (σ : Set (RealSpace n)) : Set (Torus n) :=
  {θ | ∀ v : Lattice n, latticeReal v ∈ σ → integralAngle v θ = 0}

/-- The quotient annihilator is exactly the period condition in `eq:link`. -/
theorem mem_coneTorus_angleQuotient {n : ℕ} (σ : Set (RealSpace n))
    (θ : RealSpace n) :
    angleQuotient θ ∈ coneTorus σ ↔ ∀ v : Lattice n, latticeReal v ∈ σ →
      ∃ k : ℤ, pairing v θ = (k : ℝ) * (2 * Real.pi) := by
  simp only [coneTorus, Set.mem_ofPred_eq, integralAngle_eq_zero_iff]

/-- The Euclidean unit cotangent boundary in the fixed basis.
The ordinary norm on `Fin n → ℝ` would be the supremum norm, so this formula
explicitly uses the Euclidean sum of squares. -/
def cosphere {n : ℕ} : Set (Cotangent n) :=
  {x | ∑ j, (x.2 j) ^ 2 = 1}

/-- Positive-cone, period-`2π` FLTZ link, literally a subset of the cotangent
boundary (`eq:link`, lines 99–109). -/
def fltzLink {n : ℕ} (I : ToricInput n) : Set (Cotangent n) :=
  {x | x ∈ cosphere ∧ ∃ σ ∈ faceFan I, σ ≠ {0} ∧
    x.1 ∈ coneTorus σ ∧ x.2 ∈ σ}

/-- The specified link is literally contained in the chosen cotangent boundary. -/
theorem fltzLink_subset_cosphere {n : ℕ} (I : ToricInput n) :
    fltzLink I ⊆ cosphere := fun _ hx => hx.1

end FsFltz
