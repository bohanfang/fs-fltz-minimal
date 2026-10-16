import FsFltz.ToricFanSmoothness
import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# Native faces of the source-defined fan

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 61–66, and `sec:lean`,
lines 778–782. Subsets of facet vertices are exposed using the actual
integral facet basis and a perturbation of the facet supporting functional.
Native cone faces are then recovered from precisely the generators they
contain. The resulting cones belong to the original literal `faceFan`.

This is a foundational cone-face closure result. Arbitrary convex extreme
faces of the polytope and the geometric target `thm:target` remain separate.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Extend a lattice-linear functional to the real coordinate space using
the fixed coordinate basis. -/
def realExtension (L : Lattice n →ₗ[ℤ] ℝ) : RealSpace n →ₗ[ℝ] ℝ :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ fun j => L ((Pi.basisFun ℤ (Fin n)) j)

/-- The real extension agrees with the original functional on every lattice
vector, rather than only on the coordinates used to construct it. -/
@[simp]
theorem realExtension_latticeReal (L : Lattice n →ₗ[ℤ] ℝ) (v : Lattice n) :
    realExtension L (latticeReal v) = L v := by
  rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (latticeReal v)]
  simp only [map_sum, map_smul, realExtension, Module.Basis.constr_basis,
    Pi.basisFun_repr, latticeReal, smul_eq_mul]
  have h := congrArg L ((Pi.basisFun ℤ (Fin n)).sum_repr v)
  simp only [map_sum, map_smul, Pi.basisFun_repr] at h
  simpa only [zsmul_eq_mul] using h

/-- A linear functional selecting a subset of the vertices of a supporting
face can be combined with the supporting functional to expose that subset
in the entire finite polytope. Strict gaps at the finitely many other
vertices determine the perturbation size explicitly. -/
theorem IsPolytopeFace.of_selector {V t s : Finset (Lattice n)}
    (ht : IsPolytopeFace V t) (hst : s ⊆ t)
    (h : RealSpace n →ₗ[ℝ] ℝ)
    (hh : ∀ v ∈ t, h (latticeReal v) = if v ∈ s then 0 else -1) :
    IsPolytopeFace V s := by
  classical
  obtain ⟨htV, ℓ, a, hle, heq⟩ := ht
  let R : Lattice n → ℝ := fun v => (h (latticeReal v) + 1) / (a - ℓ (latticeReal v))
  let B : ℝ := 1 + ∑ v ∈ V, |R v|
  have hgap : ∀ v ∈ V, v ∉ t →
      B * ℓ (latticeReal v) + h (latticeReal v) < B * a := by
    intro v hv hvt
    have hlt : ℓ (latticeReal v) < a :=
      lt_of_le_of_ne (hle v hv) (fun he => hvt ((heq v hv).mpr he))
    have hden : 0 < a - ℓ (latticeReal v) := sub_pos.mpr hlt
    have hR : R v < B := by
      have hsum := Finset.single_le_sum (fun w (_ : w ∈ V) => abs_nonneg (R w)) hv
      have habs := le_abs_self (R v)
      dsimp [B]
      linarith
    have hg : h (latticeReal v) + 1 < B * (a - ℓ (latticeReal v)) :=
      (div_lt_iff₀ hden).mp hR
    nlinarith
  refine ⟨hst.trans htV, B • ℓ + h, B * a, ?_, ?_⟩
  · intro v hv
    change B * ℓ (latticeReal v) + h (latticeReal v) ≤ B * a
    by_cases hvt : v ∈ t
    · rw [(heq v hv).mp hvt, hh v hvt]
      split_ifs <;> linarith
    · exact (hgap v hv hvt).le
  · intro v hv
    change v ∈ s ↔ B * ℓ (latticeReal v) + h (latticeReal v) = B * a
    by_cases hvt : v ∈ t
    · rw [(heq v hv).mp hvt, hh v hvt]
      split_ifs with hvs
      · exact ⟨fun _ => by ring, fun _ => hvs⟩
      · constructor
        · exact fun hs => (hvs hs).elim
        · intro he
          linarith
    · constructor
      · exact fun hs => (hvt (hst hs)).elim
      · intro he
        exact (ne_of_lt (hgap v hv hvt) he).elim

/-- Every subset of the vertices of a basis-supported face is again an
actual supporting face of the whole polytope, including the empty subset. -/
theorem IsPolytopeFace.subset_of_basis {V t s : Finset (Lattice n)}
    (ht : IsPolytopeFace V t) (hst : s ⊆ t)
    (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) : IsPolytopeFace V s := by
  classical
  let f : {v : Lattice n // v ∈ t} → ℝ := fun v => if v.val ∈ s then 0 else -1
  apply ht.of_selector hst (realExtension ((b.constr ℝ) f))
  intro v hv
  rw [realExtension_latticeReal]
  simpa only [hb, f] using b.constr_basis ℝ f ⟨v, hv⟩

/-- Subsets of proper face supports are source-defined supporting faces,
using the containing facet's actual integral basis. -/
theorem ToricInput.isPolytopeFace_subset (I : ToricInput n)
    {s r : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) (hrs : r ⊆ s) :
    IsPolytopeFace I.vertices r := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hr : r = ∅ := Finset.subset_empty.mp hrs
    simpa only [hr] using isPolytopeFace_empty I.vertices
  · obtain ⟨t, ht, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
    exact ht.1.subset_of_basis (hrs.trans hst) b hb

/-- The literal finite cone as a native Mathlib pointed cone. Its carrier
is definitionally the original `positiveCone`, without new face data. -/
def positivePointedCone (s : Finset (Lattice n)) : PointedCone ℝ (RealSpace n) where
  carrier := positiveCone s
  zero_mem' := zero_mem_positiveCone s
  add_mem' := add_mem_positiveCone
  smul_mem' c _ hx := smul_mem_positiveCone c.property hx

@[simp]
theorem coe_positivePointedCone (s : Finset (Lattice n)) :
    (positivePointedCone s : Set (RealSpace n)) = positiveCone s := rfl

/-- Every native face of a finite positive cone is exactly the cone on the
original generators lying in that face. A positive summand of a point of
the face lies in the face by Mathlib's native face law. -/
theorem eq_positiveCone_faceVertexSupport_of_isFaceOf
    {s : Finset (Lattice n)} {F : PointedCone ℝ (RealSpace n)}
    (hF : F.IsFaceOf (positivePointedCone s)) :
    (F : Set (RealSpace n)) = positiveCone (faceVertexSupport s F) := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨a, ha, hpa⟩ := hF.le hp
    have hsum : (∑ v : {v : Lattice n // v ∈ s}, a v.val • latticeReal v.val) ∈ F := by
      rw [Finset.sum_coe_sort s (fun v => a v • latticeReal v), ← hpa]
      exact hp
    have hzero : ∀ v ∈ s, latticeReal v ∉ F → a v = 0 := by
      intro v hv hvF
      rcases eq_or_lt_of_le (ha v hv) with he | hpos
      · exact he.symm
      · exact (hvF (hF.mem_of_sum_smul_mem
          (fun w : {v : Lattice n // v ∈ s} => latticeReal_mem_positiveCone w.property)
          (fun w => ha w.val w.property) hsum ⟨v, hv⟩ hpos)).elim
    refine ⟨a, fun v hv => ha v (mem_faceVertexSupport.mp hv).1, ?_⟩
    rw [hpa]
    symm
    apply Finset.sum_subset (faceVertexSupport_subset s F)
    intro v hv hvnot
    have hvF : latticeReal v ∉ F := by
      intro hvF
      exact hvnot (mem_faceVertexSupport.mpr ⟨hv, hvF⟩)
    rw [hzero v hv hvF, zero_smul]
  · rintro p ⟨a, ha, rfl⟩
    apply F.sum_mem
    intro v hv
    exact PointedCone.smul_mem F (ha v hv) (mem_faceVertexSupport.mp hv).2

/-- The original fan contains every subcone generated by a subset of the
vertices of one of its nonzero face cones, with the empty subset giving
the prescribed zero cone. -/
theorem ToricInput.positiveCone_subset_mem_faceFan (I : ToricInput n)
    {s r : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) (hrs : r ⊆ s) :
    positiveCone r ∈ faceFan I := by
  rcases r.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl positiveCone_empty
  · refine Or.inr ⟨r, I.isPolytopeFace_subset hs hproper hrs, hne, ?_, rfl⟩
    intro he
    apply hproper
    exact Finset.Subset.antisymm hs.1 (he ▸ hrs)

/-- Every native face of a proper source face cone belongs to the original
literal `faceFan`, proved by recovery of its actual vertex support. -/
theorem ToricInput.mem_faceFan_of_isFaceOf_positivePointedCone (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) {F : PointedCone ℝ (RealSpace n)}
    (hF : F.IsFaceOf (positivePointedCone s)) :
    (F : Set (RealSpace n)) ∈ faceFan I := by
  rw [eq_positiveCone_faceVertexSupport_of_isFaceOf hF]
  exact I.positiveCone_subset_mem_faceFan hs hproper (faceVertexSupport_subset s F)

/-- Closure under all native cone faces of every actual source fan member.
The zero member is handled separately and has only itself as a native face.
Both membership assertions concern the original literal sets. -/
theorem ToricInput.mem_faceFan_of_isFaceOf (I : ToricInput n)
    {C F : PointedCone ℝ (RealSpace n)}
    (hC : (C : Set (RealSpace n)) ∈ faceFan I) (hF : F.IsFaceOf C) :
    (F : Set (RealSpace n)) ∈ faceFan I := by
  rcases hC with hzero | ⟨s, hs, _, hproper, hcone⟩
  · apply Or.inl
    apply Set.Subset.antisymm
    · intro p hp
      rw [← hzero]
      exact hF.le hp
    · rintro p rfl
      exact F.zero_mem
  · have hCeq : C = positivePointedCone s := SetLike.coe_injective hcone
    subst C
    exact I.mem_faceFan_of_isFaceOf_positivePointedCone hs hproper hF

end FsFltz
