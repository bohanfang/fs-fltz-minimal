import FsFltz.ToricFan
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Powerset

/-!
# Integral basis presentations of proper face cones

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 61–66, and `sec:lean`,
lines 778–782. Every actual facet has its vertices as an integral basis.
Finite maximality places every nonempty proper supporting face in a facet,
so its vertices form a subset of that same integral basis. Every nonzero
member of the original `faceFan` is literally the corresponding nonnegative
basis sum supported on that subset, the integral-basis presentation of a
smooth cone.

These are foundational basis presentations and linear-independence results.
They do not prove closure under arbitrary intrinsic cone faces or the
geometric existence target `thm:target`.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Every nonempty proper supporting face is contained in an actual facet.
The proper-face family is finite because all supports lie in `V.powerset`. -/
theorem IsPolytopeFace.exists_isPolytopeFacet {V s : Finset (Lattice n)}
    (hs : IsPolytopeFace V s) (hne : s.Nonempty) (hproper : s ≠ V) :
    ∃ t, IsPolytopeFacet V t ∧ s ⊆ t := by
  classical
  let S : Set (Finset (Lattice n)) := {t | IsPolytopeFace V t ∧ t ≠ V}
  have hfinite : S.Finite := V.powerset.finite_toSet.subset (by
    intro t ht
    exact Finset.mem_powerset.mpr ht.1.1)
  obtain ⟨t, hst, ht⟩ := hfinite.exists_le_maximal (show s ∈ S from ⟨hs, hproper⟩)
  refine ⟨t, ⟨ht.1.1, hne.mono hst, ht.1.2, ?_⟩, hst⟩
  intro u hu hup htu
  exact Finset.Subset.antisymm (ht.2 ⟨hu, hup⟩ htu) htu

/-- The input facet basis supplies a genuine integral basis containing
every vertex of a prescribed nonempty proper face. -/
theorem ToricInput.exists_facet_basis_containing_face (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices) :
    ∃ t, IsPolytopeFacet I.vertices t ∧ s ⊆ t ∧
      ∃ b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n),
        ∀ v, b v = v.val := by
  obtain ⟨t, ht, hst⟩ := hs.exists_isPolytopeFacet hne hproper
  exact ⟨t, ht, hst, I.facet_basis t ht⟩

/-- The actual lattice vertices of every nonempty proper face are
linearly independent over the integers, by restriction of its facet basis. -/
theorem ToricInput.linearIndependent_face (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices) :
    LinearIndependent ℤ (fun v : {v : Lattice n // v ∈ s} => v.val) := by
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
  let f : {v : Lattice n // v ∈ s} → {v : Lattice n // v ∈ t} :=
    fun v => ⟨v.val, hst v.property⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun z : {v : Lattice n // v ∈ t} => z.val) he)
  simpa only [Function.comp_def, hb, f] using b.linearIndependent.comp f hf

/-- For a subset of exact lattice basis vectors, the finite cone is
literally the set of nonnegative basis sums supported on that subset. -/
theorem positiveCone_eq_nonneg_basisSum {s t : Finset (Lattice n)}
    (hst : s ⊆ t) (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) :
    positiveCone s = {p | ∃ a : {v : Lattice n // v ∈ t} → ℝ,
      (∀ v, 0 ≤ a v) ∧ (∀ v, v.val ∉ s → a v = 0) ∧
        p = ∑ v, a v • latticeReal (b v)} := by
  classical
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun v => if v.val ∈ s then a v.val else 0, ?_, ?_, ?_⟩
    · intro v
      dsimp
      split_ifs with hv
      · exact ha v.val hv
      · exact le_refl _
    · intro v hv
      simp [hv]
    · simp only [hb]
      rw [Finset.sum_coe_sort t (fun v => (if v ∈ s then a v else 0) • latticeReal v)]
      symm
      calc
        ∑ v ∈ t, (if v ∈ s then a v else 0) • latticeReal v =
            ∑ v ∈ s, (if v ∈ s then a v else 0) • latticeReal v := by
          symm
          exact Finset.sum_subset hst (fun v _ hv => by simp [hv])
        _ = ∑ v ∈ s, a v • latticeReal v := by
          apply Finset.sum_congr rfl
          intro v hv
          simp only [ite_eq_left hv]
  · rintro ⟨a, ha, hoff, hp⟩
    let A : Lattice n → ℝ := fun v => if hv : v ∈ t then a ⟨v, hv⟩ else 0
    have hA : ∀ v : {v : Lattice n // v ∈ t}, A v.val = a v := by
      intro v
      simp [A, v.property]
    refine ⟨A, ?_, ?_⟩
    · intro v hv
      have hvt := hst hv
      simpa only [A, dite_eq_left hvt] using ha ⟨v, hvt⟩
    · calc
        p = ∑ v, a v • latticeReal (b v) := hp
        _ = ∑ v : {v : Lattice n // v ∈ t}, A v.val • latticeReal v.val := by
          simp only [hb, hA]
        _ = ∑ v ∈ t, A v • latticeReal v :=
          Finset.sum_coe_sort t (fun v => A v • latticeReal v)
        _ = ∑ v ∈ s, A v • latticeReal v := by
          symm
          apply Finset.sum_subset hst
          intro v hvt hvs
          simp only [A, dite_eq_left hvt, hoff ⟨v, hvt⟩ hvs, zero_smul]

/-- Every nonempty proper face cone has the exact nonnegative-sum
presentation on a subset of an integral facet basis furnished by the input. -/
theorem ToricInput.exists_positiveCone_basis (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices) :
    ∃ t, IsPolytopeFacet I.vertices t ∧ s ⊆ t ∧
      ∃ b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n),
        (∀ v, b v = v.val) ∧
        positiveCone s = {p | ∃ a : {v : Lattice n // v ∈ t} → ℝ,
          (∀ v, 0 ≤ a v) ∧ (∀ v, v.val ∉ s → a v = 0) ∧
            p = ∑ v, a v • latticeReal (b v)} := by
  obtain ⟨t, ht, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
  exact ⟨t, ht, hst, b, hb, positiveCone_eq_nonneg_basisSum hst b hb⟩

/-- Every actual nonzero fan member has a nonnegative-sum presentation
on a subset of an actual integral facet basis. The conclusion concerns
the same literal cone `σ` used in the prescribed FLTZ link. -/
theorem ToricInput.exists_basis_presentation_of_mem_faceFan (I : ToricInput n)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hnonzero : σ ≠ {0}) :
    ∃ s t, IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices ∧
      IsPolytopeFacet I.vertices t ∧ s ⊆ t ∧
      ∃ b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n),
        (∀ v, b v = v.val) ∧
        σ = {p | ∃ a : {v : Lattice n // v ∈ t} → ℝ,
          (∀ v, 0 ≤ a v) ∧ (∀ v, v.val ∉ s → a v = 0) ∧
            p = ∑ v, a v • latticeReal (b v)} := by
  rcases hσ with hzero | ⟨s, hs, hne, hproper, rfl⟩
  · exact (hnonzero hzero).elim
  obtain ⟨t, ht, hst, b, hb, heq⟩ := I.exists_positiveCone_basis hs hne hproper
  exact ⟨s, t, hs, hne, hproper, ht, hst, b, hb, heq⟩

end FsFltz
