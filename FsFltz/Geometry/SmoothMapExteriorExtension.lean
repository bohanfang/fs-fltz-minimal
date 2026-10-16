import FsFltz.Geometry.SmoothMapFiniteExtension

/-!
# Compact map-germ patching retaining an existing exterior map

Source: `geoemtric-part-fsf.tex`, conventions 119–122 and `sec:lean`,
788–814. Finite target-chart corrections over a compact carrier can retain
an already defined map on a region disjoint from the new patches. No
agreement of independently chosen germs outside the prescribed carrier
is assumed. The exterior region itself need not be compact.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.SmoothMapExtension

variable {E F X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace N] [ChartedSpace F N]
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ X]
  [T2Space X] [SecondCountableTopology X]

set_option backward.isDefEq.respectTransparency false

/-- One compact patch can be adjoined while keeping the old map wherever
the new chart patch has no points. Only the covered carrier is compact. -/
theorem exists_adjoin_compact_chartPatch_preserving_region
    {A : Set X} (f₀ : A → N) (p : ChartPatch (E := E) (F := F) A f₀)
    {L K B : Set X} (hL : IsCompact L) (hK : IsCompact K) (hKA : K ⊆ A)
    (hKU : K ⊆ p.domain) (hUB : Disjoint (p.domain : Set X) B)
    (V : TopologicalSpace.Opens X) (hLV : L ⊆ V)
    (f : V → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hfA : ∀ x (hxV : x ∈ V) (hxA : x ∈ A), f ⟨x, hxV⟩ = f₀ ⟨x, hxA⟩) :
    ∃ W : TopologicalSpace.Opens X, L ∪ K ⊆ W ∧
      ∃ h : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        (∀ x (hxW : x ∈ W) (hxA : x ∈ A), h ⟨x, hxW⟩ = f₀ ⟨x, hxA⟩) ∧
        ∀ x (hxW : x ∈ W), x ∈ B →
          ∃ hxV : x ∈ V, h ⟨x, hxW⟩ = f ⟨x, hxV⟩ := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  let T := p.chart.source ∩ p.chart ⁻¹' p.coordinates
  have hT : IsOpen T := p.chart.isOpen_inter_preimage p.coordinates_open
  have hKT : ∀ x : V, (x : X) ∈ K → f x ∈ T := by
    intro x hx
    rw [hfA x x.property (hKA hx), ← p.agreement x (hKU hx) (hKA hx)]
    exact p.map_range ⟨x, hKU hx⟩
  obtain ⟨V', hLV', hclV', _, U', hKU', hU'U, hgood⟩ :=
    exists_shrink_open_overlap_range hL hLV hKU hf.continuous hT hKT
  have hV'V : (V' : Set X) ⊆ V := fun _ hx => hclV' (subset_closure hx)
  let a : V' → V := TopologicalSpace.Opens.inclusion hV'V
  let b : U' → p.domain := TopologicalSpace.Opens.inclusion hU'U
  have hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f ∘ a) :=
    hf.comp (contMDiff_inclusion hV'V)
  have hg' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (p.map ∘ b) :=
    p.smooth.comp (contMDiff_inclusion hU'U)
  obtain ⟨P, hKP, hPU', h, hh, hhA, _, S, _hS, hSU', hhoutside⟩ :=
    exists_chart_patch_extension V' U' (f ∘ a) (p.map ∘ b) hf' hg'
      p.chart p.chart_mem p.coordinates p.coordinates_convex p.coordinates_target
      (fun x => p.map_range (b x)) (fun x hx => hgood (a x) x.property hx)
      A f₀ (fun x hx => hfA x.val (hV'V x.property) hx)
      (fun x hx => p.agreement x.val (hU'U x.property) hx) K hK hKU'
  refine ⟨V' ⊔ P, ?_, h, hh, fun x hx hxA => hhA ⟨x, hx⟩ hxA, ?_⟩
  · intro x hx
    exact hx.elim (fun hx => Or.inl (hLV' hx)) (fun hx => Or.inr (hKP hx))
  · intro x hx hxB
    have hxU : x ∉ U' := fun hx => Set.disjoint_left.mp hUB (hU'U hx) hxB
    have hxV' : x ∈ V' := hx.resolve_right (fun hx => hxU (hPU' hx))
    have hxS : x ∉ S := fun hx => hxU (hSU' hx)
    exact ⟨hV'V hxV', hhoutside x hxV' hxS⟩

/-- Finite compact patches enlarge an existing map while retaining it on
an arbitrary region avoided by every new patch. -/
theorem exists_finite_extension_preserving_region
    {A : Set X} (f₀ : A → N) {ι : Type*}
    (p : ι → ChartPatch (E := E) (F := F) A f₀) (K : ι → Set X)
    (s : Finset ι) (hK : ∀ i ∈ s, IsCompact (K i))
    (hKA : ∀ i ∈ s, K i ⊆ A) (hKU : ∀ i ∈ s, K i ⊆ (p i).domain)
    (B : Set X) (hUB : ∀ i ∈ s, Disjoint ((p i).domain : Set X) B)
    (L : Set X) (hL : IsCompact L) (V : TopologicalSpace.Opens X)
    (hLV : L ⊆ V) (f : V → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hfA : ∀ x (hxV : x ∈ V) (hxA : x ∈ A), f ⟨x, hxV⟩ = f₀ ⟨x, hxA⟩) :
    ∃ W : TopologicalSpace.Opens X, L ∪ (⋃ i ∈ s, K i) ⊆ W ∧
      ∃ h : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        (∀ x (hxW : x ∈ W) (hxA : x ∈ A), h ⟨x, hxW⟩ = f₀ ⟨x, hxA⟩) ∧
        ∀ x (hxW : x ∈ W), x ∈ B →
          ∃ hxV : x ∈ V, h ⟨x, hxW⟩ = f ⟨x, hxV⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨V, by simpa using hLV, f, hf, hfA, fun x hx _ => ⟨hx, rfl⟩⟩
  | @insert i s hi ih =>
    obtain ⟨V', hLV', f', hf', hf'A, hretain⟩ := ih
      (fun j hj => hK j (Finset.mem_insert_of_mem hj))
      (fun j hj => hKA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hKU j (Finset.mem_insert_of_mem hj))
      (fun j hj => hUB j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hcover, h, hh, hhA, hret⟩ :=
      exists_adjoin_compact_chartPatch_preserving_region f₀ (p i)
        (hL.union (s.isCompact_biUnion (fun j hj => hK j (Finset.mem_insert_of_mem hj))))
        (hK i (Finset.mem_insert_self i s)) (hKA i (Finset.mem_insert_self i s))
        (hKU i (Finset.mem_insert_self i s)) (hUB i (Finset.mem_insert_self i s))
        V' hLV' f' hf' hf'A
    refine ⟨W, ?_, h, hh, hhA, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact hcover (Or.inl (Or.inl hx))
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hcover (Or.inr hxj)
        · exact hcover (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)))
    · intro x hx hxB
      obtain ⟨hxV', he⟩ := hret x hx hxB
      obtain ⟨hxV, he'⟩ := hretain x hxV' hxB
      exact ⟨hxV, he.trans he'⟩

variable [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Compact local germs which match the carrier map glue onto an existing
partial extension. A closed region disjoint from that compact carrier is
retained wherever the resulting domain meets it. -/
theorem exists_extension_from_compact_germs_preserving_region
    {A K L B : Set X} (f₀ : A → N)
    (hK : IsCompact K) (hKA : K ⊆ A) (hL : IsCompact L)
    (hB : IsClosed B) (hKB : Disjoint K B)
    (V : TopologicalSpace.Opens X) (hLV : L ⊆ V) (f : V → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hfA : ∀ x (hxV : x ∈ V) (hxA : x ∈ A), f ⟨x, hxV⟩ = f₀ ⟨x, hxA⟩)
    (hlocal : ∀ x : K, ∃ U : TopologicalSpace.Opens X, (x : X) ∈ U ∧
      ∃ g : U → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyU : y ∈ U) (hyA : y ∈ A), g ⟨y, hyU⟩ = f₀ ⟨y, hyA⟩) :
    ∃ W : TopologicalSpace.Opens X, L ∪ K ⊆ W ∧
      ∃ h : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        (∀ x (hxW : x ∈ W) (hxA : x ∈ A), h ⟨x, hxW⟩ = f₀ ⟨x, hxA⟩) ∧
        ∀ x (hxW : x ∈ W), x ∈ B →
          ∃ hxV : x ∈ V, h ⟨x, hxW⟩ = f ⟨x, hxV⟩ := by
  classical
  have hp (x : K) : ∃ p : ChartPatch (E := E) (F := F) A f₀,
      (x : X) ∈ p.domain ∧ Disjoint (p.domain : Set X) B := by
    obtain ⟨p, hx⟩ := exists_chartPatch_of_local f₀ ⟨x.val, hKA x.property⟩ (hlocal x)
    let U : TopologicalSpace.Opens X := ⟨(p.domain : Set X) ∩ Bᶜ,
      p.domain.isOpen.inter hB.isOpen_compl⟩
    let a : U → p.domain := TopologicalSpace.Opens.inclusion inter_subset_left
    let q : ChartPatch (E := E) (F := F) A f₀ :=
      { p with
        domain := U
        map := p.map ∘ a
        smooth := p.smooth.comp (contMDiff_inclusion inter_subset_left)
        agreement := fun y hy hyA => p.agreement y hy.1 hyA
        map_range := fun y => p.map_range (a y) }
    refine ⟨q, ⟨hx, fun hxB => Set.disjoint_left.mp hKB x.property hxB⟩, ?_⟩
    exact Set.disjoint_left.mpr (fun _ hx hxB => hx.2 hxB)
  choose p hp hdisj using hp
  have hcover : K ⊆ ⋃ i : K, ((p i).domain : Set X) :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun i => ((p i).domain : Set X))
    (fun i => (p i).domain.isOpen) hcover
  obtain ⟨K', hK'c, hK'U, hK'eq⟩ := hK.finite_compact_cover s
    (fun i => ((p i).domain : Set X)) (fun i _ => (p i).domain.isOpen) hs
  have hK'A : ∀ i ∈ s, K' i ⊆ A := by
    intro i hi x hx
    apply hKA
    rw [hK'eq]
    exact mem_iUnion₂.mpr ⟨i, hi, hx⟩
  obtain ⟨W, hW, h, hh, hhA, hretain⟩ := exists_finite_extension_preserving_region
    f₀ p K' s (fun i _ => hK'c i) hK'A (fun i _ => hK'U i)
    B (fun i _ => hdisj i) L hL V hLV f hf hfA
  exact ⟨W, hK'eq ▸ hW, h, hh, hhA, hretain⟩

end FsFltz.Geometry.SmoothMapExtension
