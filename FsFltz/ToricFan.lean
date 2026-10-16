import FsFltz.ToricCones
import Mathlib.Topology.Order.LeftRight

/-!
# Intersections in the finite face fan

Source: `geoemtric-part-fsf.tex`, `sec:data`, lines 57–64: the fan consists
of zero and positive cones over nonempty proper faces of the input polytope.
The exact family is used in `eq:link`, lines 99–109; this is part of the
first foundation layer in `sec:lean`, lines 778–782.

The proof uses the input's interior-zero condition. A supporting level of a
proper face must be strictly positive: if it were zero, a vertex below the
supporting hyperplane and a small negative multiple of that vertex inside
the polytope would contradict the supporting inequality. If two positive
multiples of points in proper faces agree, applying both supporting
functionals bounds their scale factors in opposite directions. The factors
are therefore equal, and the two face points are equal. Intersections of
faces are supporting faces, obtained by adding their functionals. Thus
intersections of their cones are cones over their vertex intersections,
including the zero cone when the intersection is empty.

For supporting functionals and levels `(ℓ,a)` and `(m,b)`, the functional
`a m - b ℓ` is nonpositive on the first cone. Its zero slice is the common
cone, so the intersection is a native exposed face of both cones. The
proved family-intersection closure supplies common-cone witnesses directly
in the original `fltzLink`; annihilator tori are used only contravariantly.

These are proved fan-intersection foundations, not a proof of completeness,
smoothness, or the geometric existence assertion `thm:target`.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology

variable {n : ℕ}

/-- Intersecting two supporting vertex faces gives a supporting face. -/
theorem IsPolytopeFace.inter {V s t : Finset (Lattice n)}
    (hs : IsPolytopeFace V s) (ht : IsPolytopeFace V t) :
    IsPolytopeFace V (s ∩ t) := by
  classical
  obtain ⟨hsV, ℓ, a, hℓ, hs⟩ := hs
  obtain ⟨htV, m, b, hm, ht⟩ := ht
  refine ⟨fun v hv => hsV (Finset.mem_inter.mp hv).1, ℓ + m, a + b, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.add_apply]
    exact add_le_add (hℓ v hv) (hm v hv)
  · intro v hv
    simp only [Finset.mem_inter, hs v hv, ht v hv, LinearMap.add_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [h₁, h₂]
    · intro he
      constructor <;> linarith [hℓ v hv, hm v hv]

/-- The geometric hull of a face intersection is the exact intersection
of the two geometric face hulls. -/
theorem IsPolytopeFace.latticePolytope_inter {V s t : Finset (Lattice n)}
    (hs : IsPolytopeFace V s) (ht : IsPolytopeFace V t) :
    latticePolytope (s ∩ t) = latticePolytope s ∩ latticePolytope t := by
  have hF := hs.isExposed.inter ht.isExposed
  have hsupport : faceVertexSupport V (latticePolytope s ∩ latticePolytope t) = s ∩ t := by
    classical
    ext v
    simp only [mem_faceVertexSupport, Set.mem_inter_iff, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hvs, hvt⟩
      exact ⟨(hs.mem_latticePolytope_iff hv).mp hvs,
        (ht.mem_latticePolytope_iff hv).mp hvt⟩
    · rintro ⟨hvs, hvt⟩
      exact ⟨hs.1 hvs, (hs.mem_latticePolytope_iff (hs.1 hvs)).mpr hvs,
        (ht.mem_latticePolytope_iff (ht.1 hvt)).mpr hvt⟩
  rw [← hsupport]
  exact latticePolytope_faceVertexSupport hF

/-- Every proper supporting face of the actual input polytope has a
strictly positive supporting level. No fan property is assumed. -/
theorem ToricInput.face_supporting_slice_pos (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) :
    ∃ ℓ : RealSpace n →ₗ[ℝ] ℝ, ∃ a : ℝ, 0 < a ∧
      (∀ x ∈ latticePolytope I.vertices, ℓ x ≤ a) ∧
      latticePolytope s = {x ∈ latticePolytope I.vertices | ℓ x = a} := by
  classical
  obtain ⟨hsV, ℓ, a, hle, heq⟩ := hs
  have hbound := latticePolytope_le I.vertices ℓ a hle
  have hzero : 0 ≤ a := by
    simpa using hbound 0 (interior_subset I.zero_interior)
  have hmissing : ∃ v ∈ I.vertices, v ∉ s := by
    by_contra! h
    exact hproper (Finset.Subset.antisymm hsV h)
  obtain ⟨v, hv, hvs⟩ := hmissing
  have hvlt : ℓ (latticeReal v) < a :=
    lt_of_le_of_ne (hle v hv) (fun he => hvs ((heq v hv).mpr he))
  have hpos : 0 < a := by
    by_contra h
    have ha : a = 0 := le_antisymm (le_of_not_gt h) hzero
    have hnhds : latticePolytope I.vertices ∈ 𝓝 (0 : RealSpace n) :=
      mem_interior_iff_mem_nhds.mp I.zero_interior
    have hcont : ContinuousAt (fun r : ℝ => r • (-latticeReal v)) 0 :=
      continuousAt_id.smul continuousAt_const
    have hevent : ∀ᶠ r : ℝ in 𝓝 0, r • (-latticeReal v) ∈ latticePolytope I.vertices :=
      hcont.eventually_mem (by simpa using hnhds)
    obtain ⟨r, hr, hrmem⟩ := hevent.exists_gt
    have hcontr := hbound _ hrmem
    simp only [map_smul, map_neg, smul_eq_mul] at hcontr
    rw [ha] at hvlt hcontr
    nlinarith
  exact ⟨ℓ, a, hpos, hbound,
    latticePolytope_eq_supporting_slice I.vertices s ℓ a hsV hle heq⟩

@[simp]
theorem positiveCone_empty : positiveCone (∅ : Finset (Lattice n)) = {0} := by
  ext p
  simp [positiveCone]

/-- Enlarging the generator set enlarges its positive cone. -/
theorem positiveCone_mono {s t : Finset (Lattice n)} (hst : s ⊆ t) :
    positiveCone s ⊆ positiveCone t := by
  classical
  rintro p ⟨a, ha, rfl⟩
  refine ⟨fun v => if v ∈ s then a v else 0, ?_, ?_⟩
  · intro v hv
    dsimp
    split_ifs with hvs
    · exact ha v hvs
    · exact le_refl _
  · symm
    calc
      ∑ v ∈ t, (if v ∈ s then a v else 0) • latticeReal v =
          ∑ v ∈ s, (if v ∈ s then a v else 0) • latticeReal v := by
        symm
        exact Finset.sum_subset hst (fun v _ hv => by simp [hv])
      _ = ∑ v ∈ s, a v • latticeReal v := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [ite_eq_left hv]

/-- Proper face points have a unique radial scale: two nonnegative
multiples which agree have equal coefficients. -/
theorem ToricInput.face_radial_scale_eq (I : ToricInput n)
    {s t : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (ht : IsPolytopeFace I.vertices t) (hsproper : s ≠ I.vertices)
    (htproper : t ≠ I.vertices) {x y : RealSpace n}
    (hx : x ∈ latticePolytope s) (hy : y ∈ latticePolytope t)
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (he : r • x = q • y) : r = q := by
  obtain ⟨ℓ, a, ha, hℓ, hse⟩ := I.face_supporting_slice_pos hs hsproper
  obtain ⟨m, b, hb, hm, hte⟩ := I.face_supporting_slice_pos ht htproper
  rw [hse] at hx
  rw [hte] at hy
  have hℓeq : r * a = q * ℓ y := by
    simpa only [map_smul, smul_eq_mul, hx.2] using congrArg ℓ he
  have hmeq : r * m x = q * b := by
    simpa only [map_smul, smul_eq_mul, hy.2] using congrArg m he
  have hrq : r ≤ q := (mul_le_mul_iff_left₀ ha).mp
    (hℓeq.le.trans (mul_le_mul_of_nonneg_left (hℓ y hy.1) hq))
  have hqr : q ≤ r := (mul_le_mul_iff_left₀ hb).mp
    (hmeq.symm.le.trans (mul_le_mul_of_nonneg_left (hm x hx.1) hr))
  exact le_antisymm hrq hqr

/-- The intersection of the positive cones on two proper input faces is
the positive cone on their vertex intersection, including an empty face. -/
theorem ToricInput.positiveCone_inter (I : ToricInput n)
    {s t : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (ht : IsPolytopeFace I.vertices t) (hsproper : s ≠ I.vertices)
    (htproper : t ≠ I.vertices) :
    positiveCone s ∩ positiveCone t = positiveCone (s ∩ t) := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨hps, hpt⟩
    by_cases hpzero : p = 0
    · exact hpzero ▸ zero_mem_positiveCone _
    have hsne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, positiveCone_empty] at hps
      exact hpzero hps
    have htne : t.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, positiveCone_empty] at hpt
      exact hpzero hpt
    rw [positiveCone_eq_radialCone hsne] at hps
    rw [positiveCone_eq_radialCone htne] at hpt
    obtain ⟨r, hr, x, hx, hpx⟩ := hps
    obtain ⟨q, hq, y, hy, hpy⟩ := hpt
    have he : r • x = q • y := hpx.symm.trans hpy
    have hrpos : 0 < r := lt_of_le_of_ne hr (by
      intro hezero
      apply hpzero
      simpa [← hezero] using hpx)
    have hrq := I.face_radial_scale_eq hs ht hsproper htproper hx hy hr hq he
    have hxy : x = y := by
      rw [← hrq] at he
      exact smul_right_injective (RealSpace n) (ne_of_gt hrpos) he
    have hxinter : x ∈ latticePolytope (s ∩ t) := by
      rw [hs.latticePolytope_inter ht]
      exact ⟨hx, hxy ▸ hy⟩
    have hstne : (s ∩ t).Nonempty :=
      (latticePolytope_nonempty_iff _).mp ⟨x, hxinter⟩
    rw [positiveCone_eq_radialCone hstne]
    exact ⟨r, hr, x, hxinter, hpx⟩
  · intro p hp
    exact ⟨positiveCone_mono Finset.inter_subset_left hp,
      positiveCone_mono Finset.inter_subset_right hp⟩

/-- A common cone is the zero-level supporting slice of either cone.
For supporting data `(ℓ,a)` and `(m,b)`, the functional `a m - b ℓ`
is nonpositive on the first cone and vanishes exactly on the common cone. -/
theorem ToricInput.positiveCone_inter_eq_supporting_slice (I : ToricInput n)
    {s t : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (ht : IsPolytopeFace I.vertices t) (hsproper : s ≠ I.vertices)
    (htproper : t ≠ I.vertices) :
    ∃ L : RealSpace n →ₗ[ℝ] ℝ,
      (∀ p ∈ positiveCone s, L p ≤ 0) ∧
      positiveCone s ∩ positiveCone t = {p ∈ positiveCone s | L p = 0} := by
  classical
  by_cases hsne : s.Nonempty
  · obtain ⟨ℓ, a, ha, _, hse⟩ := I.face_supporting_slice_pos hs hsproper
    obtain ⟨m, b, _, hm, hte⟩ := I.face_supporting_slice_pos ht htproper
    let L : RealSpace n →ₗ[ℝ] ℝ := a • m - b • ℓ
    have hbound : ∀ p ∈ positiveCone s, L p ≤ 0 := by
      intro p hp
      rw [positiveCone_eq_radialCone hsne] at hp
      obtain ⟨r, hr, x, hx, rfl⟩ := hp
      rw [hse] at hx
      rw [map_smul, smul_eq_mul]
      apply mul_nonpos_of_nonneg_of_nonpos hr
      change a * m x - b * ℓ x ≤ 0
      rw [hx.2]
      nlinarith [mul_le_mul_of_nonneg_left (hm x hx.1) ha.le]
    refine ⟨L, hbound, ?_⟩
    ext p
    constructor
    · intro hp
      refine ⟨hp.1, ?_⟩
      have hpst : p ∈ positiveCone (s ∩ t) :=
        (I.positiveCone_inter hs ht hsproper htproper) ▸ hp
      by_cases hstne : (s ∩ t).Nonempty
      · rw [positiveCone_eq_radialCone hstne] at hpst
        obtain ⟨r, _, x, hx, rfl⟩ := hpst
        have hxs := latticePolytope_mono Finset.inter_subset_left hx
        have hxt := latticePolytope_mono Finset.inter_subset_right hx
        rw [hse] at hxs
        rw [hte] at hxt
        simp only [map_smul, smul_eq_mul]
        change r * (a * m x - b * ℓ x) = 0
        rw [hxs.2, hxt.2]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hstne, positiveCone_empty] at hpst
        change p = 0 at hpst
        simp only [hpst, map_zero]
    · rintro ⟨hp, hpL⟩
      refine ⟨hp, ?_⟩
      rw [positiveCone_eq_radialCone hsne] at hp
      obtain ⟨r, hr, x, hx, rfl⟩ := hp
      by_cases hrzero : r = 0
      · simp only [hrzero, zero_smul]
        exact zero_mem_positiveCone t
      have hxQ := hx
      rw [hse] at hxQ
      have hLx : L x = 0 := by
        rw [map_smul, smul_eq_mul] at hpL
        exact (mul_eq_zero.mp hpL).resolve_left hrzero
      have hgap : a * (m x - b) = 0 := by
        change a * m x - b * ℓ x = 0 at hLx
        rw [hxQ.2] at hLx
        nlinarith
      have hmx : m x = b :=
        sub_eq_zero.mp ((mul_eq_zero.mp hgap).resolve_left (ne_of_gt ha))
      have hxt : x ∈ latticePolytope t := by
        rw [hte]
        exact ⟨hxQ.1, hmx⟩
      exact smul_mem_positiveCone hr (latticePolytope_subset_positiveCone t hxt)
  · have hsempty := Finset.not_nonempty_iff_eq_empty.mp hsne
    refine ⟨0, by simp, ?_⟩
    ext p
    simp [hsempty, positiveCone_empty, zero_mem_positiveCone]

/-- The common cone is a native geometric exposed face of the first
cone; exchanging the two faces gives the corresponding result for the
second cone. -/
theorem ToricInput.isExposed_positiveCone_inter (I : ToricInput n)
    {s t : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (ht : IsPolytopeFace I.vertices t) (hsproper : s ≠ I.vertices)
    (htproper : t ≠ I.vertices) :
    IsExposed ℝ (positiveCone s) (positiveCone s ∩ positiveCone t) := by
  obtain ⟨L, hbound, hslice⟩ :=
    I.positiveCone_inter_eq_supporting_slice hs ht hsproper htproper
  intro _
  refine ⟨LinearMap.toContinuousLinearMap L, ?_⟩
  rw [hslice]
  ext p
  constructor
  · rintro ⟨hp, hpL⟩
    refine ⟨hp, ?_⟩
    intro q hq
    change L q ≤ L p
    rw [hpL]
    exact hbound q hq
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (hbound p hp) ?_⟩
    have hzero := hmax 0 (zero_mem_positiveCone s)
    change L 0 ≤ L p at hzero
    simpa only [map_zero] using hzero

/-- All members of the source-defined family contain the cone vertex. -/
theorem zero_mem_of_mem_faceFan (I : ToricInput n)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) : (0 : RealSpace n) ∈ σ := by
  rcases hσ with rfl | ⟨s, _, _, _, rfl⟩
  · exact Set.mem_singleton _
  · exact zero_mem_positiveCone s

/-- The actual finite face-cone family is closed under intersections.
This consumes the geometric cone-intersection theorem, not an extra
fan axiom attached to the input. -/
theorem ToricInput.inter_mem_faceFan (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I) :
    σ ∩ τ ∈ faceFan I := by
  classical
  rcases hσ with rfl | ⟨s, hs, _, hsproper, rfl⟩
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (zero_mem_of_mem_faceFan I hτ))]
    exact Or.inl rfl
  rcases hτ with rfl | ⟨t, ht, _, htproper, rfl⟩
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr (zero_mem_positiveCone s))]
    exact Or.inl rfl
  rw [I.positiveCone_inter hs ht hsproper htproper]
  by_cases hne : (s ∩ t).Nonempty
  · refine Or.inr ⟨s ∩ t, hs.inter ht, hne, ?_, rfl⟩
    intro he
    apply hsproper
    exact Finset.Subset.antisymm hs.1 (he ▸ Finset.inter_subset_left)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, positiveCone_empty]
    exact Or.inl rfl

/-- Every common cone in the source-defined fan is a geometric exposed
face of the first cone, including its distinguished zero member. -/
theorem ToricInput.isExposed_inter_faceFan (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I) :
    IsExposed ℝ σ (σ ∩ τ) := by
  rcases hσ with rfl | ⟨s, hs, hsne, hsproper, rfl⟩
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (zero_mem_of_mem_faceFan I hτ))]
  rcases hτ with rfl | ⟨t, ht, _, htproper, rfl⟩
  · have hemptyproper : (∅ : Finset (Lattice n)) ≠ I.vertices := by
      intro he
      have hneV : I.vertices.Nonempty := hsne.mono hs.1
      simp only [← he, Finset.not_nonempty_empty] at hneV
    simpa only [positiveCone_empty] using
      I.isExposed_positiveCone_inter hs (isPolytopeFace_empty I.vertices)
        hsproper hemptyproper
  · exact I.isExposed_positiveCone_inter hs ht hsproper htproper

/-- A common fan cone is a native exposed face of both intersecting
cones, the geometric intersection axiom of a fan. -/
theorem ToricInput.isExposed_inter_faceFan_both (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I) :
    IsExposed ℝ σ (σ ∩ τ) ∧ IsExposed ℝ τ (σ ∩ τ) := by
  exact ⟨I.isExposed_inter_faceFan hσ hτ,
    Set.inter_comm τ σ ▸ I.isExposed_inter_faceFan hτ hσ⟩

/-- Annihilator tori reverse inclusion of their underlying cones. -/
theorem coneTorus_antitone {σ τ : Set (RealSpace n)} (hστ : σ ⊆ τ) :
    coneTorus τ ⊆ coneTorus σ := by
  intro θ hθ v hv
  exact hθ v (hστ hv)

/-- Common cone incidence gives a witness in the exact FLTZ link formula.
The unit cotangent boundary excludes a zero common cone. -/
theorem ToricInput.mem_fltzLink_of_mem_cone_inter (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I)
    {x : Cotangent n} (hx : x ∈ cosphere)
    (hθ : x.1 ∈ coneTorus (σ ∩ τ)) (hpσ : x.2 ∈ σ) (hpτ : x.2 ∈ τ) :
    x ∈ fltzLink I := by
  refine ⟨hx, σ ∩ τ, I.inter_mem_faceFan hσ hτ, ?_, hθ, hpσ, hpτ⟩
  intro he
  apply cotangent_ne_zero_of_mem_cosphere hx
  have hp : x.2 ∈ σ ∩ τ := ⟨hpσ, hpτ⟩
  simpa only [he, Set.mem_singleton_iff] using hp

/-- The overlap of two fan strata on the unit cotangent boundary belongs
to the same literal FLTZ link, with the common cone furnished by the
proved fan-intersection producer. Only annihilator inclusion is used. -/
theorem ToricInput.fltz_strata_inter_subset (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I) :
    cosphere ∩ (coneTorus σ ×ˢ σ) ∩ (coneTorus τ ×ˢ τ) ⊆ fltzLink I := by
  rintro x ⟨⟨hx, hθσ, hpσ⟩, _, hpτ⟩
  exact I.mem_fltzLink_of_mem_cone_inter hσ hτ hx
    (coneTorus_antitone Set.inter_subset_left hθσ) hpσ hpτ

end FsFltz
