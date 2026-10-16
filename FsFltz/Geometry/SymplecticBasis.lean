import FsFltz.Geometry.BoundaryContactDistribution
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Symplectic coordinates of the actual boundary contact hyperplane

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–160,
and `sec:lean`, lines 783–814. The actual boundary differential is already
nondegenerate on the primitive kernel. The algebra here splits off a normalized
symplectic pair, preserves nondegeneracy on the explicit complement, and iterates
this splitting to construct a full symplectic coordinate equivalence. The
boundary consumer proves the standard pairings for its actual differential,
including the zero-dimensional kernel. `ContactVolume.lean` consumes these
coordinates to prove nonvanishing of the existing signed contact-volume sum.
-/

noncomputable section

namespace FsFltz.Geometry

namespace SymplecticAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E)

theorem twoForm_swap (β : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (v w : E) :
    β ![v, w] = -β ![w, v] := by
  have hs : (![w, v] : Fin 2 → E) ∘ Equiv.swap 0 1 = ![v, w] := by
    ext i
    fin_cases i <;> simp
  simpa only [hs] using β.map_swap ![w, v] (i := 0) (j := 1) (by decide)

/-- The native bilinear interpretation of an alternating two-form. -/
def twoFormBilin (β : E [⋀^Fin 2]→ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w => β ![v, w])
    (fun v w z => β.map_vecCons_add ![z] v w)
    (fun s v w => β.map_vecCons_smul ![w] s v)
    (fun v w z => by
      rw [twoForm_swap β, β.map_vecCons_add, twoForm_swap β w v, twoForm_swap β z v]
      ring)
    (fun s v w => by
      rw [twoForm_swap β, β.map_vecCons_smul, twoForm_swap β w v]
      simp only [smul_eq_mul]
      ring)

@[simp] theorem twoFormBilin_apply (β : E [⋀^Fin 2]→ₗ[ℝ] ℝ) (v w : E) :
    twoFormBilin β v w = β ![v, w] := rfl

theorem twoFormBilin_isAlt (β : E [⋀^Fin 2]→ₗ[ℝ] ℝ) : (twoFormBilin β).IsAlt := by
  intro v
  exact β.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)

/-- The simultaneous orthogonal complement to a specified pair. -/
def pairComplement (e f : E) : Submodule ℝ E :=
  LinearMap.ker (B e) ⊓ LinearMap.ker (B f)

@[simp] theorem mem_pairComplement (e f w : E) :
    w ∈ pairComplement B e f ↔ B e w = 0 ∧ B f w = 0 := Iff.rfl

/-- Subtract the two symplectic coordinates of a vector. -/
def pairRemainder (e f w : E) : E := w - B w f • e + B w e • f

theorem pairRemainder_mem (hB : B.IsAlt) {e f : E} (hpair : B e f = 1) (w : E) :
    pairRemainder B e f w ∈ pairComplement B e f := by
  have hfe : B f e = -1 := by rw [← LinearMap.IsAlt.neg hB, hpair]
  change B e (pairRemainder B e f w) = 0 ∧ B f (pairRemainder B e f w) = 0
  constructor
  · simp only [pairRemainder, map_add, map_sub, map_smul, hB e, hpair,
      smul_eq_mul, mul_zero, sub_zero, mul_one]
    rw [← LinearMap.IsAlt.neg hB e w]
    ring
  · simp only [pairRemainder, map_add, map_sub, map_smul, hB f, hfe,
      smul_eq_mul, mul_zero, add_zero, mul_neg_one]
    rw [← LinearMap.IsAlt.neg hB f w]
    ring

theorem pair_decomposition (e f w : E) :
    B w f • e + (-B w e) • f + pairRemainder B e f w = w := by
  simp only [pairRemainder, neg_smul]
  abel

/-- Addition from the normalized pair and its native complementary submodule. -/
def pairSum (e f : E) : ((ℝ × ℝ) × pairComplement B e f) →ₗ[ℝ] E where
  toFun p := p.1.1 • e + p.1.2 • f + p.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_smul,
      RingHom.id_apply, smul_eq_mul]

@[simp] theorem pairSum_apply (e f : E) (p : (ℝ × ℝ) × pairComplement B e f) :
    pairSum B e f p = p.1.1 • e + p.1.2 • f + p.2 := rfl

theorem pairSum_injective (hB : B.IsAlt) {e f : E} (hpair : B e f = 1) :
    Function.Injective (pairSum B e f) := by
  have hfe : B f e = -1 := by rw [← LinearMap.IsAlt.neg hB, hpair]
  intro p q hpq
  have hp := (mem_pairComplement B e f (p.2 : E)).mp p.2.property
  have hq := (mem_pairComplement B e f (q.2 : E)).mp q.2.property
  have ha : p.1.1 = q.1.1 := by
    have h := congrArg (fun w => B f w) hpq
    simp only [pairSum_apply, map_add, map_smul, smul_eq_mul, hfe,
      hB f, hp.2, hq.2, mul_zero, mul_neg_one, add_zero] at h
    linarith
  have hb : p.1.2 = q.1.2 := by
    have h := congrArg (fun w => B e w) hpq
    simpa only [pairSum_apply, map_add, map_smul, smul_eq_mul, hpair,
      hB e, hp.1, hq.1, mul_zero, mul_one, zero_add, add_zero] using h
  apply Prod.ext
  · exact Prod.ext ha hb
  · apply Subtype.ext
    simp only [pairSum_apply, ha, hb] at hpq
    exact add_left_cancel hpq

theorem pairSum_surjective (hB : B.IsAlt) {e f : E} (hpair : B e f = 1) :
    Function.Surjective (pairSum B e f) := by
  intro w
  exact ⟨((B w f, -B w e), ⟨pairRemainder B e f w, pairRemainder_mem B hB hpair w⟩),
    pair_decomposition B e f w⟩

/-- Splitting by a normalized symplectic pair, with no assumed splitting data. -/
def pairEquiv (hB : B.IsAlt) {e f : E} (hpair : B e f = 1) :
    ((ℝ × ℝ) × pairComplement B e f) ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (pairSum B e f)
    ⟨pairSum_injective B hB hpair, pairSum_surjective B hB hpair⟩

@[simp] theorem pairEquiv_apply (hB : B.IsAlt) {e f : E} (hpair : B e f = 1)
    (p : (ℝ × ℝ) × pairComplement B e f) :
    pairEquiv B hB hpair p = p.1.1 • e + p.1.2 • f + p.2 := rfl

/-- Every nonzero vector in a nondegenerate alternating space has a normalized
symplectic partner. This produces the pair used by the dimension induction. -/
theorem exists_normalized_partner (hnd : B.SeparatingLeft) {e : E} (he : e ≠ 0) :
    ∃ f : E, B e f = 1 := by
  classical
  have h : ∃ w, B e w ≠ 0 := by
    by_contra! h
    exact he (hnd e h)
  obtain ⟨w, hw⟩ := h
  refine ⟨(B e w)⁻¹ • w, ?_⟩
  simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

/-- A normalized pair removes exactly two dimensions. -/
theorem pairComplement_finrank_add_two [FiniteDimensional ℝ E]
    (hB : B.IsAlt) {e f : E} (hpair : B e f = 1) :
    Module.finrank ℝ (pairComplement B e f) + 2 = Module.finrank ℝ E := by
  have h := (pairEquiv B hB hpair).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h

/-- Nondegeneracy survives on the actual complementary submodule. -/
theorem pairComplement_separatingLeft (hB : B.IsAlt) (hnd : B.SeparatingLeft)
    {e f : E} (hpair : B e f = 1) :
    (B.restrict (pairComplement B e f)).SeparatingLeft := by
  intro v hv
  apply Subtype.ext
  apply hnd (v : E)
  intro w
  obtain ⟨p, rfl⟩ := (pairEquiv B hB hpair).surjective w
  have hve : B (v : E) e = 0 := by
    rw [← LinearMap.IsAlt.neg hB, (mem_pairComplement B e f (v : E)).mp v.property |>.1,
      neg_zero]
  have hvf : B (v : E) f = 0 := by
    rw [← LinearMap.IsAlt.neg hB, (mem_pairComplement B e f (v : E)).mp v.property |>.2,
      neg_zero]
  have hvp : B (v : E) (p.2 : E) = 0 := hv p.2
  simp only [pairEquiv_apply, map_add, map_smul, smul_eq_mul, hve, hvf, hvp,
    mul_zero, zero_add]

theorem pairComplement_isAlt (hB : B.IsAlt) (e f : E) :
    (B.restrict (pairComplement B e f)).IsAlt := fun v => hB (v : E)

/-- The splitting is a symplectic direct sum, with the standard two-plane
form and the actual restricted form on the complement. -/
theorem pairEquiv_pairing (hB : B.IsAlt) {e f : E} (hpair : B e f = 1)
    (p q : (ℝ × ℝ) × pairComplement B e f) :
    B (pairEquiv B hB hpair p) (pairEquiv B hB hpair q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + B (p.2 : E) (q.2 : E) := by
  have hp := (mem_pairComplement B e f (p.2 : E)).mp p.2.property
  have hq := (mem_pairComplement B e f (q.2 : E)).mp q.2.property
  have hpe : B (p.2 : E) e = 0 := by rw [← LinearMap.IsAlt.neg hB, hp.1, neg_zero]
  have hpf : B (p.2 : E) f = 0 := by rw [← LinearMap.IsAlt.neg hB, hp.2, neg_zero]
  have hfe : B f e = -1 := by rw [← LinearMap.IsAlt.neg hB, hpair]
  simp only [pairEquiv_apply, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hB e, hB f, hpair, hfe,
    hq.1, hq.2, hpe, hpf]
  ring

/-- Separating off the first pair is a linear equivalence of coordinate spaces. -/
def pairCoordinatesSucc (m : ℕ) :
    (Fin (m + 1) → ℝ × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × (Fin m → ℝ × ℝ)) where
  toFun u := (u 0, fun i => u i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv u := Fin.cons_self_tail u
  right_inv p := by ext i <;> simp
  map_add' u v := rfl
  map_smul' c u := rfl

@[simp] theorem pairCoordinatesSucc_apply (m : ℕ) (u : Fin (m + 1) → ℝ × ℝ) :
    pairCoordinatesSucc m u = (u 0, fun i => u i.succ) := rfl

open scoped BigOperators

/-- A finite-dimensional nondegenerate alternating form of dimension `2m`
has an actual symplectic coordinate equivalence, including the zero space.
The coordinate pairing is proved, rather than supplied as certificate data. -/
theorem exists_symplecticEquiv [FiniteDimensional ℝ E]
    (m : ℕ) (hdim : Module.finrank ℝ E = 2 * m)
    (hB : B.IsAlt) (hnd : B.SeparatingLeft) :
    ∃ S : (Fin m → ℝ × ℝ) ≃ₗ[ℝ] E,
      ∀ u v, B (S u) (S v) = ∑ i : Fin m, ((u i).1 * (v i).2 - (u i).2 * (v i).1) := by
  induction m generalizing E with
  | zero =>
    have : Subsingleton E := Module.finrank_zero_iff.mp (by simpa using hdim)
    let S : (Fin 0 → ℝ × ℝ) ≃ₗ[ℝ] E :=
      LinearEquiv.ofBijective 0 ⟨fun _ _ _ => Subsingleton.elim _ _,
        fun w => ⟨0, Subsingleton.elim _ _⟩⟩
    refine ⟨S, ?_⟩
    intro u v
    have hu : S u = 0 := Subsingleton.elim _ _
    simp only [hu, map_zero, LinearMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
  | succ m ih =>
    have : Nontrivial E := (Module.finrank_pos_iff (R := ℝ) (M := E)).mp (by omega)
    obtain ⟨e, he⟩ := exists_ne (0 : E)
    obtain ⟨f, hpair⟩ := exists_normalized_partner B hnd he
    let W := pairComplement B e f
    have hW : Module.finrank ℝ W = 2 * m := by
      have h := pairComplement_finrank_add_two B hB hpair
      dsimp [W]
      omega
    obtain ⟨T, hT⟩ := ih (B := B.restrict W) hW
      (pairComplement_isAlt B hB e f) (pairComplement_separatingLeft B hB hnd hpair)
    let S : (Fin (m + 1) → ℝ × ℝ) ≃ₗ[ℝ] E :=
      (pairCoordinatesSucc m).trans
        ((LinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr T) |>.trans (pairEquiv B hB hpair)
    refine ⟨S, ?_⟩
    intro u v
    change B (pairEquiv B hB hpair (u 0, T (fun i => u i.succ)))
      (pairEquiv B hB hpair (v 0, T (fun i => v i.succ))) = _
    rw [pairEquiv_pairing]
    have ht := hT (fun i => u i.succ) (fun i => v i.succ)
    change B (T (fun i => u i.succ) : E) (T (fun i => v i.succ) : E) = _ at ht
    rw [ht, Fin.sum_univ_succ]

end SymplecticAlgebra

namespace LiouvilleStructure

open SmoothManifold
open scoped BigOperators

/-- The actual differential on the actual boundary primitive kernel admits
symplectic coordinates. All pairings come from the existing boundary
nondegeneracy theorem, with no basis or contact-volume hypothesis. -/
theorem boundary_contactHyperplane_symplecticEquiv {m : ℕ}
    {D : CompactDomain (2 * m + 2)} (L : LiouvilleStructure D) (x : D.boundary.Point) :
    ∃ S : (Fin m → ℝ × ℝ) ≃ₗ[ℝ]
        D.boundary.contactHyperplane (D.boundaryForm L.primitive) x,
      ∀ u v,
        D.boundary.contactHyperplaneDifferential (D.boundaryForm L.primitive) x ![S u, S v] =
          ∑ i : Fin m, ((u i).1 * (v i).2 - (u i).2 * (v i).1) := by
  let β := (D.boundary.contactHyperplaneDifferential
    (D.boundaryForm L.primitive) x).toAlternatingMap
  let B := SymplecticAlgebra.twoFormBilin β
  have hdim : Module.finrank ℝ
      (D.boundary.contactHyperplane (D.boundaryForm L.primitive) x) = 2 * m := by
    rw [L.boundary_contactHyperplane_finrank]
    omega
  have hnd : B.SeparatingLeft := by
    intro v hv
    exact L.boundary_contactHyperplaneDifferential_nondegenerate x v hv
  exact SymplecticAlgebra.exists_symplecticEquiv B m hdim
    (SymplecticAlgebra.twoFormBilin_isAlt β) hnd

end LiouvilleStructure
end FsFltz.Geometry
