import FsFltz.ToricIntrinsicFaces
import FsFltz.SmoothTorus
import FsFltz.Regularity

/-!
# Generator equations for the literal face annihilator torus

Source: `geometric-part-fsf-proof.tex`, `sec:parameters`, lines 529–538,
and `prop:morsebott`, lines 1529–1531. Integral facet coordinates identify
the generator character equations with the annihilator of every lattice
point of the same positive cone. The consumers are critical-torus
classification and the radial FLTZ section.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Every literal cone annihilator is closed in the quotient torus. -/
theorem isClosed_coneTorus (σ : Set (RealSpace n)) : IsClosed (coneTorus σ) := by
  unfold coneTorus
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (continuous_integralAngle v) continuous_const

/-- Compactness comes from the actual quotient torus, for any cone. -/
theorem isCompact_coneTorus (σ : Set (RealSpace n)) : IsCompact (coneTorus σ) := by
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  exact (isClosed_coneTorus σ).isCompact

/-- The integral angle pairing is linear in the lattice argument. -/
def integralAngleLinear (θ : Torus n) : Lattice n →ₗ[ℤ] AddCircle (2 * Real.pi) where
  toFun v := integralAngle v θ
  map_add' v w := by simp [integralAngle, add_smul, Finset.sum_add_distrib]
  map_smul' k v := by simp [integralAngle, mul_smul, Finset.smul_sum]

/-- Integral facet coordinates of a cone point vanish off its face and
are nonnegative on it. -/
theorem basis_coordinates_of_mem_positiveCone {s t : Finset (Lattice n)}
    (hst : s ⊆ t) (b : Module.Basis t ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) {v : Lattice n}
    (hv : latticeReal v ∈ positiveCone s) :
    (∀ w, 0 ≤ b.repr v w) ∧ (∀ w, w.val ∉ s → b.repr v w = 0) := by
  classical
  rw [positiveCone_eq_nonneg_basisSum hst b hb] at hv
  obtain ⟨a, ha, hoff, he⟩ := hv
  have hcoord (w : t) : (b.repr v w : ℝ) = a w := by
    let L : Lattice n →ₗ[ℤ] ℝ := (Int.castAddHom ℝ).toIntLinearMap.comp (b.coord w)
    have h := congrArg (realExtension L) he
    simp only [map_sum, map_smul, realExtension_latticeReal] at h
    simpa [L, Module.Basis.coord_apply, Finsupp.single_apply] using h
  constructor
  · intro w
    exact_mod_cast (hcoord w ▸ ha w)
  · intro w hw
    exact_mod_cast ((hcoord w).trans (hoff w hw))

/-- The literal cone annihilator is determined by its integral generators. -/
theorem ToricInput.mem_coneTorus_positiveCone_iff_integralAngle (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (θ : Torus n) :
    θ ∈ coneTorus (positiveCone s) ↔ ∀ v ∈ s, integralAngle v θ = 0 := by
  constructor
  · intro h v hv
    exact h v (latticeReal_mem_positiveCone hv)
  · intro h v hv
    obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hsne hsproper
    have hoff := (basis_coordinates_of_mem_positiveCone hst b hb hv).2
    change integralAngleLinear θ v = 0
    rw [← b.sum_repr v, map_sum]
    apply Finset.sum_eq_zero
    intro w _
    rw [map_smul]
    by_cases hw : w.val ∈ s
    · change b.repr v w • integralAngle (b w) θ = 0
      rw [hb w, h w.val hw, smul_zero]
    · rw [hoff w hw, zero_smul]

/-- Generator character equations identify the same period-`2π` torus as
the literal FLTZ definition. -/
theorem ToricInput.mem_coneTorus_positiveCone_iff (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) (θ : Torus n) :
    θ ∈ coneTorus (positiveCone s) ↔ ∀ v ∈ s, (character v θ : ℂ) = 1 := by
  rw [I.mem_coneTorus_positiveCone_iff_integralAngle hs hsne hsproper]
  have hc (v : Lattice n) : integralAngle v θ = 0 ↔ (character v θ : ℂ) = 1 := by
    constructor
    · intro h
      simp [character, h]
    · intro h
      apply angleCircleHomeomorph.injective
      rw [angleCircleHomeomorph_eq_toCircle, angleCircleHomeomorph_eq_toCircle]
      apply Subtype.ext
      simpa [character] using h
  simp only [hc]

/-- Evaluating a lattice-linear circle-valued map on the coordinate basis
recovers the corresponding point of the quotient torus. -/
def torusOfLatticeLinear (L : Lattice n →ₗ[ℤ] AddCircle (2 * Real.pi)) : Torus n :=
  fun j => L ((Pi.basisFun ℤ (Fin n)) j)

theorem integralAngle_torusOfLatticeLinear
    (L : Lattice n →ₗ[ℤ] AddCircle (2 * Real.pi)) (v : Lattice n) :
    integralAngle v (torusOfLatticeLinear L) = L v := by
  have h := congrArg L ((Pi.basisFun ℤ (Fin n)).sum_repr v)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, integralAngle,
    torusOfLatticeLinear] using h

/-- The literal face annihilator is connected, using the same integral
facet basis as the generator-equation bridge. -/
theorem ToricInput.isConnected_coneTorus_positiveCone (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    IsConnected (coneTorus (positiveCone s)) := by
  classical
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hsne hsproper
  let P : (t → AddCircle (2 * Real.pi)) → Torus n := fun a =>
    torusOfLatticeLinear (b.constr ℤ fun w => if w.val ∈ s then 0 else a w)
  have hP : Continuous P := by
    apply continuous_pi
    intro j
    change Continuous (fun a : t → AddCircle (2 * Real.pi) =>
      (b.constr ℤ fun w => if w.val ∈ s then 0 else a w) ((Pi.basisFun ℤ (Fin n)) j))
    simp only [Module.Basis.constr_apply_fintype]
    apply continuous_finsetSum
    intro w _
    by_cases hw : w.val ∈ s
    · simp only [hw, ite_true, smul_zero]
      exact continuous_const
    · simp only [hw, ite_false]
      exact (continuous_apply w).zsmul _
  have hrange : Set.range P = coneTorus (positiveCone s) := by
    ext θ
    rw [I.mem_coneTorus_positiveCone_iff_integralAngle hs hsne hsproper]
    constructor
    · rintro ⟨a, rfl⟩ v hv
      change integralAngle v (torusOfLatticeLinear _) = 0
      rw [integralAngle_torusOfLatticeLinear]
      have he : v = b ⟨v, hst hv⟩ := (hb ⟨v, hst hv⟩).symm
      rw [he, Module.Basis.constr_basis]
      simp only [hv, ite_true]
    · intro h
      let a : t → AddCircle (2 * Real.pi) := fun w => integralAngle w.val θ
      refine ⟨a, ?_⟩
      have hL : (b.constr ℤ fun w => if w.val ∈ s then 0 else a w) =
          integralAngleLinear θ := by
        apply b.ext
        intro w
        rw [Module.Basis.constr_basis]
        change (if w.val ∈ s then 0 else a w) = integralAngle (b w) θ
        rw [hb w]
        by_cases hw : w.val ∈ s
        · simp [hw, h w.val hw]
        · simp [hw, a]
      change torusOfLatticeLinear _ = θ
      rw [hL]
      funext j
      simp [torusOfLatticeLinear, integralAngleLinear, integralAngle, Pi.basisFun_apply]
  rw [← hrange]
  exact isConnected_range hP

end FsFltz
