import FsFltz.ToricFaces
import Mathlib.Analysis.Convex.Combination

/-!
# Cones over the geometric polytope faces

The finite nonnegative sums used by `positiveCone` are identified with the
nonnegative radial cones over the actual exposed faces. The resulting face
family is consumed directly by the literal `fltzLink` formula.

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 61–64, `eq:link`, lines
99–109, and foundation handoff `sec:lean`, lines 778–782. Fan intersection,
completeness, and smoothness axioms, and `thm:target`, remain pending.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

@[simp]
theorem zero_mem_positiveCone (s : Finset (Lattice n)) :
    (0 : RealSpace n) ∈ positiveCone s := by
  exact ⟨fun _ => 0, by simp, by simp⟩

theorem latticeReal_mem_positiveCone {s : Finset (Lattice n)}
    {v : Lattice n} (hv : v ∈ s) : latticeReal v ∈ positiveCone s := by
  classical
  refine ⟨fun w => if w = v then 1 else 0, ?_, ?_⟩
  · intro w hw
    dsimp
    split_ifs <;> norm_num
  · simp [hv]

theorem add_mem_positiveCone {s : Finset (Lattice n)} {p q : RealSpace n}
    (hp : p ∈ positiveCone s) (hq : q ∈ positiveCone s) :
    p + q ∈ positiveCone s := by
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  refine ⟨fun v => a v + b v, fun v hv => add_nonneg (ha v hv) (hb v hv), ?_⟩
  simp only [add_smul, Finset.sum_add_distrib]

theorem smul_mem_positiveCone {s : Finset (Lattice n)} {p : RealSpace n}
    {t : ℝ} (ht : 0 ≤ t) (hp : p ∈ positiveCone s) :
    t • p ∈ positiveCone s := by
  obtain ⟨a, ha, rfl⟩ := hp
  refine ⟨fun v => t * a v, fun v hv => mul_nonneg ht (ha v hv), ?_⟩
  simp only [Finset.smul_sum, smul_smul]

theorem convex_positiveCone (s : Finset (Lattice n)) :
    Convex ℝ (positiveCone s) := by
  intro p hp q hq a b ha hb _
  exact add_mem_positiveCone (smul_mem_positiveCone ha hp) (smul_mem_positiveCone hb hq)

theorem latticePolytope_subset_positiveCone (s : Finset (Lattice n)) :
    latticePolytope s ⊆ positiveCone s := by
  apply convexHull_min ?_ (convex_positiveCone s)
  rintro _ ⟨v, hv, rfl⟩
  exact latticeReal_mem_positiveCone hv

/-- The radial cone includes all nonnegative multiples of points of a set.
For an empty set it is empty; cones over faces below use nonempty faces. -/
def radialCone (F : Set (RealSpace n)) : Set (RealSpace n) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ F, p = t • x}

/-- Finite nonnegative vertex sums are literally the radial cone over the
convex hull of those vertices. Nonemptiness supplies a base point at zero. -/
theorem positiveCone_eq_radialCone {s : Finset (Lattice n)} (hs : s.Nonempty) :
    positiveCone s = radialCone (latticePolytope s) := by
  classical
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    let t : ℝ := ∑ v ∈ s, a v
    have ht : 0 ≤ t := Finset.sum_nonneg ha
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · obtain ⟨v, hv⟩ := hs
      have hazero : ∀ w ∈ s, a w = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg ha).mp ht0.symm
      refine ⟨0, le_refl _, latticeReal v,
        subset_convexHull ℝ _ ⟨v, hv, rfl⟩, ?_⟩
      rw [zero_smul]
      exact Finset.sum_eq_zero fun w hw => by rw [hazero w hw, zero_smul]
    · refine ⟨t, ht, ∑ v ∈ s, (a v / t) • latticeReal v, ?_, ?_⟩
      · apply (convex_convexHull ℝ _).sum_mem
        · exact fun v hv => div_nonneg (ha v hv) ht
        · simp only [div_eq_mul_inv, ← Finset.sum_mul]
          exact mul_inv_cancel₀ (ne_of_gt htpos)
        · intro v hv
          exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
      · simp only [Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [mul_div_cancel₀ _ (ne_of_gt htpos)]
  · rintro ⟨t, ht, x, hx, rfl⟩
    exact smul_mem_positiveCone ht (latticePolytope_subset_positiveCone s hx)

/-- The cone of a geometric exposed face agrees with the finite cone on its
supporting vertices. This uses the proved face/hull correspondence. -/
theorem positiveCone_faceVertexSupport {V : Finset (Lattice n)}
    {F : Set (RealSpace n)} (hF : IsExposed ℝ (latticePolytope V) F)
    (hne : F.Nonempty) :
    positiveCone (faceVertexSupport V F) = radialCone F := by
  have hs : (faceVertexSupport V F).Nonempty :=
    (latticePolytope_nonempty_iff _).mp ((latticePolytope_faceVertexSupport hF).symm ▸ hne)
  rw [positiveCone_eq_radialCone hs, latticePolytope_faceVertexSupport hF]

/-- The encoded fan consists exactly of zero and the radial cones over all
nonempty proper geometric exposed faces of the actual input polytope. -/
theorem mem_faceFan_iff_exists_isExposed (I : ToricInput n)
    (σ : Set (RealSpace n)) :
    σ ∈ faceFan I ↔ σ = {0} ∨
      ∃ F : Set (RealSpace n), IsExposed ℝ (latticePolytope I.vertices) F ∧
        F.Nonempty ∧ F ≠ latticePolytope I.vertices ∧ σ = radialCone F := by
  constructor
  · rintro (hz | ⟨s, hs, hne, hproper, rfl⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨latticePolytope s, hs.isExposed,
        (latticePolytope_nonempty_iff s).mpr hne, ?_, positiveCone_eq_radialCone hne⟩
      exact (not_congr (hs.latticePolytope_eq_iff
        (isPolytopeFace_self I.vertices))).mpr hproper
  · rintro (hz | ⟨F, hF, hne, hproper, rfl⟩)
    · exact Or.inl hz
    · have hs := isPolytopeFace_faceVertexSupport hF
      have hsne : (faceVertexSupport I.vertices F).Nonempty :=
        (latticePolytope_nonempty_iff _).mp
          ((latticePolytope_faceVertexSupport hF).symm ▸ hne)
      refine Or.inr ⟨faceVertexSupport I.vertices F, hs, hsne, ?_,
        (positiveCone_faceVertexSupport hF hne).symm⟩
      intro he
      apply hproper
      rw [← latticePolytope_faceVertexSupport hF, he]

/-- A point of the prescribed Euclidean cotangent boundary has nonzero
cotangent coordinate, so a zero cone never contributes to its link. -/
theorem cotangent_ne_zero_of_mem_cosphere {x : Cotangent n}
    (hx : x ∈ cosphere) : x.2 ≠ 0 := by
  intro he
  simp [cosphere, he] at hx

/-- The literal FLTZ link admits the source's formula using genuine
nonnegative cones over nonempty proper geometric exposed faces, with the
same quotient annihilator and the same Euclidean boundary. -/
theorem mem_fltzLink_iff_exists_isExposed (I : ToricInput n) (x : Cotangent n) :
    x ∈ fltzLink I ↔ x ∈ cosphere ∧
      ∃ F : Set (RealSpace n), IsExposed ℝ (latticePolytope I.vertices) F ∧
        F.Nonempty ∧ F ≠ latticePolytope I.vertices ∧
        x.1 ∈ coneTorus (radialCone F) ∧ x.2 ∈ radialCone F := by
  constructor
  · rintro ⟨hx, σ, hσ, hnonzero, hθ, hp⟩
    rcases (mem_faceFan_iff_exists_isExposed I σ).mp hσ with hz | hface
    · exact (hnonzero hz).elim
    · obtain ⟨F, hF, hne, hproper, rfl⟩ := hface
      exact ⟨hx, F, hF, hne, hproper, hθ, hp⟩
  · rintro ⟨hx, F, hF, hne, hproper, hθ, hp⟩
    refine ⟨hx, radialCone F,
      (mem_faceFan_iff_exists_isExposed I _).mpr
        (Or.inr ⟨F, hF, hne, hproper, rfl⟩), ?_, hθ, hp⟩
    intro he
    apply cotangent_ne_zero_of_mem_cosphere hx
    simpa [he] using hp

end FsFltz
