import FsFltz.Analysis.OmegaLimitLyapunov
import Mathlib.Topology.Connected.Clopen

/-!
# Connected compact limit sets of forward orbits

Source: `geometric-part-fsf-proof.tex`, `thm:core`, lines 1735–1744.
The actual forward limit set is connected, and every neighborhood of it
eventually contains the entire orbit. Together with finite critical-torus
classification these are the topological inputs to local trapping.
-/

namespace FsFltz

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem forwardOrbit_mem_closure (φ : Flow ℝ X) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    φ t x ∈ closure (φ.forwardOrbit x) := by
  apply subset_closure
  rw [φ.forwardOrbit_eq_range_nonneg]
  exact ⟨⟨t, ht⟩, rfl⟩

omit [T2Space X] in
theorem omegaLimit_subset_forwardOrbit_closure (φ : Flow ℝ X) (x : X) :
    omegaLimit atTop φ {x} ⊆ closure (φ.forwardOrbit x) := by
  apply (omegaLimit_subset_closure_image2 atTop φ {x} (Ici_mem_atTop (0 : ℝ))).trans
  apply closure_minimal ?_ isClosed_closure
  rintro y ⟨t, ht, z, hz, rfl⟩
  have hz : z = x := mem_singleton_iff.mp hz
  subst z
  exact forwardOrbit_mem_closure φ x ht

/-- Eventual containment concerns every sufficiently large real time. -/
theorem eventually_mem_of_omegaLimit_subset (φ : Flow ℝ X) {x : X}
    (hc : IsCompact (closure (φ.forwardOrbit x))) {U : Set X}
    (hU : IsOpen U) (hωU : omegaLimit atTop φ {x} ⊆ U) :
    ∀ᶠ t in atTop, φ t x ∈ U := by
  have ha : ∀ᶠ t : ℝ in atTop, MapsTo (φ t) {x} (closure (φ.forwardOrbit x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht z hz
    have hz : z = x := mem_singleton_iff.mp hz
    subst z
    exact forwardOrbit_mem_closure φ x ht
  filter_upwards [eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
    atTop φ {x} hc ha hU hωU] with t ht
  exact ht (mem_singleton x)

omit [T2Space X] in
/-- The forward limit set is nonempty and compact in the actual ambient. -/
theorem omegaLimit_nonempty_isCompact (φ : Flow ℝ X) {x : X}
    (hc : IsCompact (closure (φ.forwardOrbit x))) :
    (omegaLimit atTop φ {x}).Nonempty ∧ IsCompact (omegaLimit atTop φ {x}) := by
  refine ⟨?_, hc.of_isClosed_subset (isClosed_omegaLimit _ _ _)
    (omegaLimit_subset_forwardOrbit_closure φ x)⟩
  apply nonempty_omegaLimit_of_isCompact_absorbing atTop φ {x} hc ?_ (singleton_nonempty x)
  refine ⟨Ici (0 : ℝ), Ici_mem_atTop 0, ?_⟩
  apply closure_minimal ?_ isClosed_closure
  rintro y ⟨t, ht, z, hz, rfl⟩
  have hz : z = x := mem_singleton_iff.mp hz
  subst z
  exact forwardOrbit_mem_closure φ x ht

/-- Connected orbit tails force the compact forward limit set to be connected. -/
theorem isConnected_omegaLimit (φ : Flow ℝ X) {x : X}
    (hc : IsCompact (closure (φ.forwardOrbit x))) :
    IsConnected (omegaLimit atTop φ {x}) := by
  obtain ⟨hne, hcompact⟩ := omegaLimit_nonempty_isCompact φ hc
  refine ⟨hne, (isPreconnected_iff_subset_of_fully_disjoint_closed hcompact.isClosed).2 ?_⟩
  intro u v hu hv hcover hdisj
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hcompact.inter_right hu)
      (hcompact.inter_right hv) (hdisj.mono inter_subset_right inter_subset_right)
  have hω : omegaLimit atTop φ {x} ⊆ U ∪ V := by
    intro y hy
    rcases hcover hy with hyu | hyv
    · exact Or.inl (huU ⟨hy, hyu⟩)
    · exact Or.inr (hvV ⟨hy, hyv⟩)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_mem_of_omegaLimit_subset φ hc (hU.union hV) hω)
  let S := (fun t : ℝ => φ t x) '' Ici T
  have hS : IsPreconnected S :=
    isPreconnected_Ici.image _ (φ.continuous continuous_id continuous_const).continuousOn
  have hSU : S ⊆ U ∪ V := by
    rintro y ⟨t, ht, rfl⟩
    exact hT t ht
  have hωS : omegaLimit atTop φ {x} ⊆ closure S := by
    simpa only [S, image2_singleton_right] using
      omegaLimit_subset_closure_image2 atTop φ {x} (Ici_mem_atTop T)
  rcases hS.subset_or_subset hU hV hUV hSU with hSU | hSV
  · left
    have hcl : closure S ⊆ Vᶜ := closure_minimal
      (fun y hy => fun hyv => Set.disjoint_left.mp hUV (hSU hy) hyv) hV.isClosed_compl
    intro y hy
    rcases hcover hy with hyu | hyv
    · exact hyu
    · exact False.elim (hcl (hωS hy) (hvV ⟨hy, hyv⟩))
  · right
    have hcl : closure S ⊆ Uᶜ := closure_minimal
      (fun y hy => fun hyu => Set.disjoint_left.mp hUV hyu (hSV hy)) hU.isClosed_compl
    intro y hy
    rcases hcover hy with hyu | hyv
    · exact False.elim (hcl (hωS hy) (huU ⟨hy, hyu⟩))
    · exact hyv

omit [T2Space X] in
/-- A nonempty connected subset of a finite disjoint closed union lies in
one actual member of that union. -/
theorem IsConnected.subset_one_of_finite_disjoint_closed
    {ι : Type*} [Fintype ι] {S : Set X} (hS : IsConnected S)
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : S ⊆ ⋃ i, C i) : ∃ i, S ⊆ C i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  let D : Set X := ⋃ j ∈ Finset.univ.erase i, C j
  have hD : IsClosed D := isClosed_biUnion_finset (fun j _ => hC j)
  have hCD : Disjoint (C i) D := by
    apply Set.disjoint_left.mpr
    intro y hy hDy
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hDy
    exact Set.disjoint_left.mp (hdisj (Finset.mem_erase.mp hj).1.symm) hy hyj
  have hcov : S ⊆ C i ∪ D := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hij : j = i
    · exact Or.inl (hij ▸ hj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩, hj⟩)
  have hemp : S ∩ (C i ∩ D) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hCD, inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS.isPreconnected)
    (C i) D (hC i) hD hcov hemp with hleft | hright
  · exact ⟨i, hleft⟩
  · exact False.elim (Set.disjoint_left.mp hCD hi (hright hx))

/-- The first toric trapping input: all late points stay near one member
of the finite closed critical-locus decomposition. -/
theorem omegaLimit_subset_one_and_eventually (φ : Flow ℝ X) {x : X}
    (hc : IsCompact (closure (φ.forwardOrbit x)))
    {ι : Type*} [Fintype ι] (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : omegaLimit atTop φ {x} ⊆ ⋃ i, C i) :
    ∃ i, omegaLimit atTop φ {x} ⊆ C i ∧
      ∀ U : Set X, IsOpen U → C i ⊆ U → ∀ᶠ t in atTop, φ t x ∈ U := by
  obtain ⟨i, hi⟩ := IsConnected.subset_one_of_finite_disjoint_closed
    (isConnected_omegaLimit φ hc) C hC hdisj hcover
  exact ⟨i, hi, fun U hU hiU => eventually_mem_of_omegaLimit_subset φ hc hU (hi.trans hiU)⟩

end FsFltz
