import FsFltz.Geometry.RankTwoLiouville
import FsFltz.Geometry.RegularFiberManifold

/-!
# Intrinsic symplectic projection for a nonholomorphic fiber

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1198–1237,
especially the projection and intrinsic-field formulas at lines 1208–1220.
The two Hamiltonian vectors give the actual projection to the common kernel
of the real and imaginary differentials. Nonzero Poisson pairing implies
nondegeneracy of the restricted form. This is the algebraic producer for the
tailored intrinsic field; it does not assume holomorphicity or completeness.
-/

noncomputable section

namespace FsFltz.Geometry.SymplecticAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  (omega : LinearMap.BilinForm ℝ E) (homega : omega.IsAlt)
  (hnd : omega.SeparatingLeft) (p q : E →ₗ[ℝ] ℝ)

/-- Symplectic projection to the two-covector kernel, with the source signs. -/
def rankTwoFiberProjection (v : E) : E :=
  v + (q v / rankTwoPairing omega homega hnd p q) •
    hamiltonianVector omega homega hnd p -
    (p v / rankTwoPairing omega homega hnd p q) •
      hamiltonianVector omega homega hnd q

/-- The projection kills both defining covectors. -/
theorem rankTwoFiberProjection_mem_kernel
    (hpi : rankTwoPairing omega homega hnd p q ≠ 0) (v : E) :
    p (rankTwoFiberProjection omega homega hnd p q v) = 0 ∧
      q (rankTwoFiberProjection omega homega hnd p q v) = 0 := by
  have hcross := hamiltonianVector_cross omega homega hnd p q
  simp only [rankTwoFiberProjection, map_sub, map_add, map_smul,
    smul_eq_mul, hamiltonianVector_self, hcross]
  unfold rankTwoPairing at hpi ⊢
  constructor <;> field_simp <;> ring

/-- Kernel vectors are fixed, so the formula is a projection onto the whole kernel. -/
theorem rankTwoFiberProjection_eq_self (v : E) (hp : p v = 0) (hq : q v = 0) :
    rankTwoFiberProjection omega homega hnd p q v = v := by
  simp [rankTwoFiberProjection, hp, hq]

/-- The normal correction is symplectically orthogonal to every fiber tangent. -/
theorem rankTwoFiberProjection_contraction (v w : E) (hp : p w = 0) (hq : q w = 0) :
    omega (rankTwoFiberProjection omega homega hnd p q v) w = omega v w := by
  simp [rankTwoFiberProjection, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hamiltonianVector_contraction, hp, hq]

/-- Nonzero Poisson pairing makes the actual common kernel symplectic. -/
theorem separatingLeft_on_rankTwo_kernel
    (hpi : rankTwoPairing omega homega hnd p q ≠ 0)
    (v : E) (hp : p v = 0) (hq : q v = 0)
    (hzero : ∀ w, p w = 0 → q w = 0 → omega v w = 0) : v = 0 := by
  apply hnd v
  intro w
  obtain ⟨hpw, hqw⟩ := rankTwoFiberProjection_mem_kernel omega homega hnd p q hpi w
  have hz := hzero _ hpw hqw
  rw [← LinearMap.IsAlt.neg homega] at hz ⊢
  rw [rankTwoFiberProjection_contraction omega homega hnd p q w v hp hq] at hz
  exact hz

end FsFltz.Geometry.SymplecticAlgebra

open scoped Manifold ContDiff

namespace FsFltz.Geometry.SmoothManifold

variable {d e : ℕ} (M : SmoothManifold d)

/-- The projection on an actual native tangent fiber. -/
def rankTwoFiberProjection (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ)
    (v : M.Tangent x) : M.Tangent x :=
  SymplecticAlgebra.rankTwoFiberProjection
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd p.toLinearMap q.toLinearMap v

theorem rankTwoFiberProjection_mem_kernel (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ)
    (hpi : M.rankTwoPairing omega x hnd p q ≠ 0) (v : M.Tangent x) :
    p (M.rankTwoFiberProjection omega x hnd p q v) = 0 ∧
      q (M.rankTwoFiberProjection omega x hnd p q v) = 0 :=
  SymplecticAlgebra.rankTwoFiberProjection_mem_kernel
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd p.toLinearMap q.toLinearMap hpi v

theorem rankTwoFiberProjection_contraction (omega : M.Form 2) (x : M.Point)
    (hnd : M.Nondegenerate omega x) (p q : M.Tangent x →L[ℝ] ℝ)
    (v w : M.Tangent x) (hp : p w = 0) (hq : q w = 0) :
    evalTwo omega x (M.rankTwoFiberProjection omega x hnd p q v) w =
      evalTwo omega x v w :=
  SymplecticAlgebra.rankTwoFiberProjection_contraction
    (SymplecticAlgebra.twoFormBilin (omega x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (omega x).toAlternatingMap)
    hnd p.toLinearMap q.toLinearMap v w hp hq

/-- A native embedded fiber inherits nondegeneracy from its nonzero Poisson pairing.
The tangent-image hypothesis is the conclusion of the regular-level theorem. -/
theorem nondegenerate_pullback_of_rankTwo_kernel (N : SmoothManifold e)
    (j : N.SmoothEmbedding M) (alpha : M.Form 1) (hs : M.IsSmoothForm alpha)
    (x : N.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) (j.map x))
    (p q : M.Tangent (j.map x) →L[ℝ] ℝ)
    (hpi : M.rankTwoPairing (M.exteriorDerivative alpha) (j.map x) hnd p q ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j.map x).range =
      p.ker ⊓ q.ker) :
    N.Nondegenerate (N.exteriorDerivative (N.pullback M j.map alpha)) x := by
  intro v hzero
  rw [N.exteriorDerivative_pullback M j.map alpha hs] at hzero
  let D := mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j.map x
  have hvker : p (D v) = 0 ∧ q (D v) = 0 := by
    have hv : D v ∈ D.range := ⟨v, rfl⟩
    rw [hkernel] at hv
    exact hv
  have hvzero : D v = 0 := by
    apply SymplecticAlgebra.separatingLeft_on_rankTwo_kernel
      (SymplecticAlgebra.twoFormBilin
        ((M.exteriorDerivative alpha) (j.map x)).toAlternatingMap)
      (SymplecticAlgebra.twoFormBilin_isAlt
        ((M.exteriorDerivative alpha) (j.map x)).toAlternatingMap)
      hnd p.toLinearMap q.toLinearMap hpi (D v) hvker.1 hvker.2
    intro w hpw hqw
    have hwmem : w ∈ D.range := by
      rw [hkernel]
      exact ⟨hpw, hqw⟩
    obtain ⟨u, hu⟩ := hwmem
    change D u = w at hu
    have hz := hzero u
    change (M.exteriorDerivative alpha (j.map x)) (D ∘ ![v, u]) = 0 at hz
    have htuple : D ∘ ![v, u] = ![D v, D u] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, hu] at hz
    exact hz
  exact j.immersion x (hvzero.trans D.map_zero.symm)

/-- The actual intrinsic Liouville field pushes forward to the displayed
symplectic projection of the actual ambient Liouville field. -/
theorem liouvilleVector_pullback_eq_rankTwoFiberProjection (N : SmoothManifold e)
    (j : N.SmoothEmbedding M) (alpha : M.Form 1) (hs : M.IsSmoothForm alpha)
    (x : N.Point) (hnd : M.Nondegenerate (M.exteriorDerivative alpha) (j.map x))
    (p q : M.Tangent (j.map x) →L[ℝ] ℝ)
    (hpi : M.rankTwoPairing (M.exteriorDerivative alpha) (j.map x) hnd p q ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j.map x).range =
      p.ker ⊓ q.ker) :
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j.map x
        (N.liouvilleVector (N.pullback M j.map alpha) x) =
      M.rankTwoFiberProjection (M.exteriorDerivative alpha) (j.map x) hnd p q
        (M.liouvilleVector alpha (j.map x)) := by
  let D := mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model d) j.map x
  let z := M.rankTwoFiberProjection (M.exteriorDerivative alpha) (j.map x) hnd p q
    (M.liouvilleVector alpha (j.map x))
  have hzker : p z = 0 ∧ q z = 0 :=
    M.rankTwoFiberProjection_mem_kernel _ _ hnd p q hpi _
  have hzrange : z ∈ D.range := by
    rw [hkernel]
    exact hzker
  obtain ⟨v, hv⟩ := hzrange
  change D v = z at hv
  have heq : N.LiouvilleEquation (N.pullback M j.map alpha) x v := by
    intro w
    rw [N.exteriorDerivative_pullback M j.map alpha hs]
    change (M.exteriorDerivative alpha (j.map x)) (D ∘ ![v, w]) =
      alpha (j.map x) (D ∘ fun _ => w)
    have htuple : D ∘ ![v, w] = ![D v, D w] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, hv]
    have hwker : p (D w) = 0 ∧ q (D w) = 0 := by
      have hw : D w ∈ D.range := ⟨w, rfl⟩
      rw [hkernel] at hw
      exact hw
    change evalTwo (M.exteriorDerivative alpha) (j.map x) z (D w) =
      evalOne alpha (j.map x) (D w)
    rw [M.rankTwoFiberProjection_contraction _ _ hnd p q _ _ hwker.1 hwker.2]
    exact M.liouvilleVector_contraction alpha (j.map x)
      (M.liouvilleEquation_exists alpha (j.map x) hnd) (D w)
  rw [N.liouvilleVector_eq _ x
    (M.nondegenerate_pullback_of_rankTwo_kernel N j alpha hs x hnd p q hpi hkernel) heq]
  exact hv

end FsFltz.Geometry.SmoothManifold

namespace FsFltz.Geometry.SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- Nonzero Poisson pairing proves regularity of the actual complex map. -/
theorem complexDifferential_surjective_of_planePairing_ne_zero
    (alpha : M.Form 1) (f : M.Point → ℂ) (x : M.Point)
    (hnd : M.Nondegenerate (M.exteriorDerivative alpha) x)
    (hpi : M.planePairing alpha f x hnd ≠ 0) :
    Function.Surjective (complexDifferential M f x) := by
  let L := complexDifferential M f x
  let p := Complex.reCLM.comp L
  let q := Complex.imCLM.comp L
  let omega := SymplecticAlgebra.twoFormBilin
    ((M.exteriorDerivative alpha) x).toAlternatingMap
  have homega := SymplecticAlgebra.twoFormBilin_isAlt
    ((M.exteriorDerivative alpha) x).toAlternatingMap
  let Xp := SymplecticAlgebra.hamiltonianVector omega homega hnd p.toLinearMap
  let Xq := SymplecticAlgebra.hamiltonianVector omega homega hnd q.toLinearMap
  have hpp : p Xp = 0 := SymplecticAlgebra.hamiltonianVector_self _ _ _ _
  have hqq : q Xq = 0 := SymplecticAlgebra.hamiltonianVector_self _ _ _ _
  have hqp : q Xp = -p Xq := SymplecticAlgebra.hamiltonianVector_cross _ _ _ _ _
  have hpi' : p Xq ≠ 0 := hpi
  intro z
  refine ⟨(z.re / p Xq) • Xq - (z.im / p Xq) • Xp, ?_⟩
  apply Complex.ext
  · change p ((z.re / p Xq) • Xq - (z.im / p Xq) • Xp) = z.re
    simp only [map_sub, map_smul, smul_eq_mul, hpp, mul_zero, sub_zero]
    field_simp
  · change q ((z.re / p Xq) • Xq - (z.im / p Xq) • Xp) = z.im
    simp only [map_sub, map_smul, smul_eq_mul, hqq, hqp, mul_zero, zero_sub]
    field_simp

/-- The complex tangent kernel is literally the intersection of its two real kernels. -/
theorem complexDifferential_ker_eq_real_inf_imag (f : M.Point → ℂ) (x : M.Point) :
    (complexDifferential M f x).ker =
      (Complex.reCLM.comp (complexDifferential M f x)).ker ⊓
        (Complex.imCLM.comp (complexDifferential M f x)).ker := by
  ext v
  change complexDifferential M f x v = 0 ↔
    (complexDifferential M f x v).re = 0 ∧ (complexDifferential M f x v).im = 0
  constructor
  · intro h
    simp [h]
  · rintro ⟨hr, hi⟩
    exact Complex.ext hr hi

/-- Nonzero pairing on a whole level constructs its actual smooth symplectic
fiber, with the literal level as image and the restricted ambient primitive.
This includes zero-dimensional fibers. -/
theorem exists_planeFiber_symplecticEmbedding
    (alpha : M.Form 1) (hs : M.IsSmoothForm alpha)
    (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (w : ℂ)
    (hpi : ∀ x, f x = w → M.planePairing alpha f x (hnd x) ≠ 0) :
    ∃ (N : SmoothManifold (d - 2)) (j : N.SmoothEmbedding M),
      Set.range j.map = {x | f x = w} ∧
        N.IsSymplecticOn (N.exteriorDerivative (N.pullback M j.map alpha)) Set.univ := by
  have hreg : ∀ x, f x = w → Function.Surjective (complexDifferential M f x) :=
    fun x hx => M.complexDifferential_surjective_of_planePairing_ne_zero
      alpha f x (hnd x) (hpi x hx)
  have hex := exists_regularLevel_embedding M f w hf hreg
  rw [Complex.finrank_real_complex] at hex
  obtain ⟨N, j, himage⟩ := hex
  refine ⟨N, j, himage, ?_⟩
  apply (N.isSymplecticOn_exteriorDerivative_iff (N.pullback M j.map alpha)
    (N.isSmoothForm_pullback_one M j.map alpha hs) Set.univ).mpr
  intro x _
  have hx : f (j.map x) = w := by
    have hm : j.map x ∈ Set.range j.map := ⟨x, rfl⟩
    rw [himage] at hm
    exact hm
  apply M.nondegenerate_pullback_of_rankTwo_kernel N j alpha hs x (hnd (j.map x))
    (Complex.reCLM.comp (complexDifferential M f (j.map x)))
    (Complex.imCLM.comp (complexDifferential M f (j.map x))) (hpi _ hx)
  rw [← M.complexDifferential_ker_eq_real_inf_imag]
  have htan := @regularLevel_embedding_tangent_range d M ℂ
    inferInstance inferInstance inferInstance f w hf hreg
  rw [Complex.finrank_real_complex] at htan
  exact htan j himage x

end FsFltz.Geometry.SmoothManifold
