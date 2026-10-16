import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.Opens

/-!
# Shrinking an old map domain before adjoining a new compact patch

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–161, and
`sec:lean`, lines 788–814. Smooth maps on compact carriers must extend
across the indicated boundaries. This topological producer prepares the
overlap of an existing extension with one new local chart germ; it does
not assert any geometric comparison or completion marking.
-/

open Set Topology

namespace FsFltz.Geometry

/-- Retain the already covered compact carrier `L` in a smaller old map
domain whose closure stays in `V`. If old values at the new carrier `K`
lie in an open target chart `T`, a neighborhood `O` of `K` inside its germ
domain `U` makes every value on the remaining overlap lie in `T`.

The old map is defined only on `V`; neither a total target-valued extension
nor an inhabited target is needed. The new carrier need not be compact.
Only the overlap is constrained to the target chart. -/
theorem exists_shrink_open_overlap_range
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [RegularSpace X]
    {L K : Set X} {V U : TopologicalSpace.Opens X}
    {g : V → Y} {T : Set Y}
    (hL : IsCompact L) (hLV : L ⊆ V) (hKU : K ⊆ U)
    (hg : Continuous g) (hT : IsOpen T)
    (hKT : ∀ x : V, (x : X) ∈ K → g x ∈ T) :
    ∃ W : TopologicalSpace.Opens X,
      L ⊆ W ∧ closure (W : Set X) ⊆ V ∧ IsCompact (closure (W : Set X)) ∧
      ∃ O : TopologicalSpace.Opens X,
        K ⊆ O ∧ (O : Set X) ⊆ U ∧
          ∀ x : V, (x : X) ∈ W → (x : X) ∈ O → g x ∈ T := by
  obtain ⟨W, hWo, hLW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hL V.isOpen hLV
  let r : closure W → V := fun x => ⟨x, hWV x.property⟩
  have hr : Continuous r := continuous_subtype_val.subtype_mk _
  let B : Set X := Subtype.val '' ((g ∘ r) ⁻¹' Tᶜ)
  have hBc : IsClosed B :=
    isClosed_closure.isClosedMap_subtype_val _
      (hT.isClosed_compl.preimage (hg.comp hr))
  have hKB : K ⊆ Bᶜ := by
    intro x hxK hxB
    obtain ⟨y, hy, hxy⟩ := hxB
    have hyK : (y : X) ∈ K := hxy ▸ hxK
    exact hy (hKT (r y) hyK)
  refine ⟨⟨W, hWo⟩, hLW, hWV, hWc,
    ⟨(U : Set X) ∩ Bᶜ, U.isOpen.inter hBc.isOpen_compl⟩,
    ?_, inter_subset_left, ?_⟩
  · intro x hx
    exact ⟨hKU hx, hKB hx⟩
  · intro x hxW hxO
    by_contra hxT
    apply hxO.2
    exact ⟨⟨x, subset_closure hxW⟩, hxT, rfl⟩

end FsFltz.Geometry
