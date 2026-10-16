import FsFltz.Geometry.SymplecticBasis
import FsFltz.Geometry.SymplecticPermutation

/-!
# Top contact volume from the actual symplectic kernel

Source: `geoemtric-part-fsf.tex`, conventions and `def:pair`, lines 119–160,
and `sec:lean`, lines 783–814. Symplectic coordinates on the actual boundary
primitive kernel give an interleaved tangent frame. The standard signed
permutation calculation applies to the existing `contactVolume` formula.
-/

noncomputable section
open scoped BigOperators

namespace FsFltz.Geometry

namespace SymplecticAlgebra

/-- A canonical coordinate vector in the paired coordinate space. -/
def pairedCoordinateVector {m : ℕ} (p : Fin m × Fin 2) : Fin m → ℝ × ℝ :=
  Pi.single p.1 (if p.2 = 0 then (1, 0) else (0, 1))

theorem pairedCoordinateVector_pairing {m : ℕ} (p q : Fin m × Fin 2) :
    (∑ i : Fin m, ((pairedCoordinateVector p i).1 * (pairedCoordinateVector q i).2 -
      (pairedCoordinateVector p i).2 * (pairedCoordinateVector q i).1)) =
      standardPairEntry p q := by
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  fin_cases k <;> fin_cases l
  all_goals
    by_cases hij : i = j
    · subst j
      simp [pairedCoordinateVector, standardPairEntry, Pi.single_apply, apply_ite]
    · simp [pairedCoordinateVector, standardPairEntry, Pi.single_apply, apply_ite, hij,
        Ne.symm hij]

/-- The option indexing sends the contact direction to zero and the two slots
of pair `i` to `2i+1` and `2i+2`, exactly as in `contactVolume`. -/
def contactIndexEquiv (m : ℕ) : Option (Fin m × Fin 2) ≃ Fin (2 * m + 1) :=
  (Equiv.optionCongr (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2))).trans
    ((finSuccEquiv (m * 2)).symm.trans (finCongr (by omega)))

@[simp] theorem contactIndexEquiv_none (m : ℕ) : contactIndexEquiv m none = 0 := by
  apply Fin.ext
  simp [contactIndexEquiv]

theorem contactIndexEquiv_some_val {m : ℕ} (p : Fin m × Fin 2) :
    (contactIndexEquiv m (some p)).val = 2 * p.1.val + p.2.val + 1 := by
  simp [contactIndexEquiv, finProdFinEquiv_apply_val, Nat.add_comm]

@[simp] theorem contactIndexEquiv_some_zero {m : ℕ} (i : Fin m) :
    contactIndexEquiv m (some (i, 0)) = Fin.ofNat (2 * m + 1) (2 * i.val + 1) := by
  apply Fin.ext
  rw [contactIndexEquiv_some_val, Fin.val_ofNat]
  simp only [Fin.val_zero, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]

@[simp] theorem contactIndexEquiv_some_one {m : ℕ} (i : Fin m) :
    contactIndexEquiv m (some (i, 1)) = Fin.ofNat (2 * m + 1) (2 * i.val + 2) := by
  apply Fin.ext
  rw [contactIndexEquiv_some_val, Fin.val_ofNat]
  simp only [Fin.val_one]
  rw [Nat.mod_eq_of_lt (by omega)]

end SymplecticAlgebra

namespace SmoothManifold

open SymplecticAlgebra

/-- Actual symplectic coordinates on the primitive kernel give a tangent tuple
with positive value of the existing raw contact-volume formula. -/
theorem exists_contactVolume_pos_of_symplecticEquiv {d m : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (x : M.Point) (u₀ : M.Tangent x) (hu₀ : evalOne α x u₀ = 1)
    (S : (Fin m → ℝ × ℝ) ≃ₗ[ℝ] M.contactHyperplane α x)
    (hS : ∀ u v, M.contactHyperplaneDifferential α x ![S u, S v] =
      ∑ i : Fin m, ((u i).1 * (v i).2 - (u i).2 * (v i).1)) :
    ∃ v : Fin (2 * m + 1) → M.Tangent x, 0 < M.contactVolume α m x v := by
  let V : Option (Fin m × Fin 2) → M.Tangent x
    | none => u₀
    | some p => S (pairedCoordinateVector p)
  let a : Option (Fin m × Fin 2) → ℝ := fun p => evalOne α x (V p)
  let b : Option (Fin m × Fin 2) → Option (Fin m × Fin 2) → ℝ :=
    fun p q => evalTwo (M.exteriorDerivative α) x (V p) (V q)
  have ha : a none = 1 := hu₀
  have ha' (p : Fin m × Fin 2) : a (some p) = 0 :=
    (M.mem_contactHyperplane α x _).mp (S (pairedCoordinateVector p)).property
  have hb (p q : Fin m × Fin 2) : b (some p) (some q) = standardPairEntry p q := by
    change evalTwo (M.exteriorDerivative α) x
      (S (pairedCoordinateVector p)) (S (pairedCoordinateVector q)) = _
    rw [← contactHyperplaneDifferential_apply]
    exact (hS (pairedCoordinateVector p) (pairedCoordinateVector q)).trans
      (pairedCoordinateVector_pairing p q)
  have hpos := contactPermutationVolume_pos a b ha ha' hb
  let e := contactIndexEquiv m
  let v : Fin (2 * m + 1) → M.Tangent x := V ∘ e.symm
  refine ⟨v, ?_⟩
  unfold contactVolume
  rw [← e.permCongr.sum_comp]
  have he₀ : e.symm 0 = none := by
    rw [← contactIndexEquiv_none m]
    exact e.symm_apply_apply none
  have he₁ (i : Fin m) : e.symm (Fin.ofNat (2 * m + 1) (2 * i.val + 1)) = some (i, 0) := by
    rw [← contactIndexEquiv_some_zero i]
    exact e.symm_apply_apply _
  have he₂ (i : Fin m) : e.symm (Fin.ofNat (2 * m + 1) (2 * i.val + 2)) = some (i, 1) := by
    rw [← contactIndexEquiv_some_one i]
    exact e.symm_apply_apply _
  simpa only [v, Function.comp_apply, Equiv.Perm.sign_permCongr, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, he₀, he₁, he₂, a, b] using hpos

end SmoothManifold

namespace LiouvilleStructure

open SmoothManifold

/-- The Liouville boundary primitive has a nonzero top contact volume in every
positive even ambient dimension. The tangent tuple is constructed from the actual
nondegenerate boundary kernel; no contact or volume hypothesis is supplied. -/
theorem boundary_contactVolume_pos {m : ℕ} {D : CompactDomain (2 * m + 2)}
    (L : LiouvilleStructure D) (x : D.boundary.Point) :
    ∃ v : Fin (2 * m + 1) → D.boundary.Tangent x,
      0 < D.boundary.contactVolume (D.boundaryForm L.primitive) m x v := by
  obtain ⟨u, hu⟩ := L.boundaryForm_exists_eval_ne_zero x
  let u₀ := (evalOne (D.boundaryForm L.primitive) x u)⁻¹ • u
  have hu₀ : evalOne (D.boundaryForm L.primitive) x u₀ = 1 := by
    rw [evalOne_smul]
    exact inv_mul_cancel₀ hu
  obtain ⟨S, hS⟩ := L.boundary_contactHyperplane_symplecticEquiv x
  exact D.boundary.exists_contactVolume_pos_of_symplecticEquiv
    (D.boundaryForm L.primitive) x u₀ hu₀ S hS

/-- The restricted primitive of a Liouville domain is a contact form, in the
defined top-volume sense and including the dimension-one boundary case. -/
theorem boundaryForm_isContactForm {m : ℕ} {D : CompactDomain (2 * m + 2)}
    (L : LiouvilleStructure D) :
    D.boundary.IsContactForm (D.boundaryForm L.primitive) m := by
  refine ⟨by omega, ?_, ?_⟩
  · exact D.boundary.isSmoothForm_pullback_one D.extension D.boundaryInclusion.map
      L.primitive L.smooth_primitive
  · intro x
    obtain ⟨v, hv⟩ := L.boundary_contactVolume_pos x
    exact ⟨v, ne_of_gt hv⟩

end LiouvilleStructure
end FsFltz.Geometry
