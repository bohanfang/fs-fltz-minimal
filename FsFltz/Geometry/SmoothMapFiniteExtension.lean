import FsFltz.Geometry.SmoothMapExtension
import FsFltz.Geometry.SmoothMapCompactCover
import FsFltz.Geometry.CompactMapCover

/-!
# Coherent smooth maps from compact local extension germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–161, and
`sec:lean`, lines 788–814. The finite assembly preserves the given map
on its whole compact carrier. Target charts are chosen locally and may
differ between patches; no inhabited-target hypothesis is needed.
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

/-- Adjoin one chart patch while retaining the already covered compact set.
The overlap chart condition is constructed by compact shrinking, rather than
imposed on the old map's entire image. -/
theorem exists_adjoin_compact_chartPatch
    {A : Set X} (f₀ : A → N) (p : ChartPatch (E := E) (F := F) A f₀)
    {L K : Set X} (hL : IsCompact L) (hK : IsCompact K) (hKA : K ⊆ A)
    (hKU : K ⊆ p.domain) (V : TopologicalSpace.Opens X) (hLV : L ⊆ V)
    (f : V → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hfA : ∀ x (hxV : x ∈ V) (hxA : x ∈ A), f ⟨x, hxV⟩ = f₀ ⟨x, hxA⟩) :
    ∃ W : TopologicalSpace.Opens X, L ∪ K ⊆ W ∧
      ∃ h : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        ∀ x (hxW : x ∈ W) (hxA : x ∈ A), h ⟨x, hxW⟩ = f₀ ⟨x, hxA⟩ := by
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
  have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ a := contMDiff_inclusion hV'V
  have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ b := contMDiff_inclusion hU'U
  have hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f ∘ a) := hf.comp ha
  have hg' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (p.map ∘ b) := p.smooth.comp hb
  have hfrange : ∀ x : V', (x : X) ∈ U' →
      (f ∘ a) x ∈ p.chart.source ∧ p.chart ((f ∘ a) x) ∈ p.coordinates :=
    fun x hx => hgood (a x) x.property hx
  have hgrange : ∀ x : U', (p.map ∘ b) x ∈ p.chart.source ∧
      p.chart ((p.map ∘ b) x) ∈ p.coordinates := fun x => p.map_range (b x)
  have hf'A : ∀ x (hx : x ∈ V') (hxA : x ∈ A),
      (f ∘ a) ⟨x, hx⟩ = f₀ ⟨x, hxA⟩ := fun x hx hxA => hfA x (hV'V hx) hxA
  have hg'A : ∀ x (hx : x ∈ U') (hxA : x ∈ A),
      (p.map ∘ b) ⟨x, hx⟩ = f₀ ⟨x, hxA⟩ := fun x hx hxA => p.agreement x (hU'U hx) hxA
  obtain ⟨P, hKP, _, h, hh, hhA, _⟩ :=
    exists_chart_patch_extension V' U' (f ∘ a) (p.map ∘ b) hf' hg'
      p.chart p.chart_mem p.coordinates p.coordinates_convex p.coordinates_target
      hgrange hfrange A f₀ (fun x hx => hf'A x x.property hx)
      (fun x hx => hg'A x x.property hx) K hK hKU'
  refine ⟨V' ⊔ P, ?_, h, hh, fun x hx hxA => hhA ⟨x, hx⟩ hxA⟩
  intro x hx
  exact hx.elim (fun hx => Or.inl (hLV' hx)) (fun hx => Or.inr (hKP hx))

/-- Finite compact chart patches produce a coherent smooth extension of their
common carrier map. The target chart may change at every induction step. -/
theorem exists_extension_of_finite_chartPatches
    {A : Set X} (f₀ : A → N) {ι : Type*}
    (p : ι → ChartPatch (E := E) (F := F) A f₀) (K : ι → Set X)
    (s : Finset ι) (hK : ∀ i ∈ s, IsCompact (K i))
    (hKA : ∀ i ∈ s, K i ⊆ A) (hKU : ∀ i ∈ s, K i ⊆ (p i).domain) :
    ∃ W : TopologicalSpace.Opens X, (⋃ i ∈ s, K i) ⊆ W ∧
      ∃ h : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ h ∧
        ∀ x (hxW : x ∈ W) (hxA : x ∈ A), h ⟨x, hxW⟩ = f₀ ⟨x, hxA⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊥, by simp, (fun x => False.elim x.property), ?_, ?_⟩
    · intro x
      exact False.elim x.property
    · intro x hx
      exact False.elim hx
  | @insert i s hi ih =>
    obtain ⟨V, hLV, f, hf, hfA⟩ := ih
      (fun j hj => hK j (Finset.mem_insert_of_mem hj))
      (fun j hj => hKA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hKU j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hcover, h, hh, hhA⟩ := exists_adjoin_compact_chartPatch f₀ (p i)
      (s.isCompact_biUnion (fun j hj => hK j (Finset.mem_insert_of_mem hj)))
      (hK i (Finset.mem_insert_self i s)) (hKA i (Finset.mem_insert_self i s))
      (hKU i (Finset.mem_insert_self i s)) V hLV f hf hfA
    refine ⟨W, ?_, h, hh, hhA⟩
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hcover (Or.inr hxj)
    · exact hcover (Or.inl (mem_iUnion₂.mpr ⟨j, hj, hxj⟩))

/-- Actual local smooth map germs along a compact carrier glue to one smooth
map on a neighborhood. No globally shared target chart, off-carrier germ
agreement, or nonempty-target assumption is supplied. -/
theorem exists_smoothMapExtension_of_compact
    [IsManifold 𝓘(ℝ, F) ∞ N]
    {A : Set X} (hA : IsCompact A) (f : A → N)
    (hlocal : ∀ x : A, ∃ U : TopologicalSpace.Opens X, (x : X) ∈ U ∧
      ∃ g : U → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyU : y ∈ U) (hyA : y ∈ A), g ⟨y, hyU⟩ = f ⟨y, hyA⟩) :
    ∃ W : TopologicalSpace.Opens X, A ⊆ W ∧
      ∃ g : W → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyW : y ∈ W) (hyA : y ∈ A), g ⟨y, hyW⟩ = f ⟨y, hyA⟩ := by
  obtain ⟨p, s, K, hK, hKU, hcover, hKA⟩ :=
    exists_finite_compact_chart_cover_of_local hA f hlocal
  obtain ⟨W, hW, g, hg, heq⟩ := exists_extension_of_finite_chartPatches f p K s
    (fun i _ => hK i) hKA (fun i _ => hKU i)
  exact ⟨W, hcover ▸ hW, g, hg, heq⟩

end FsFltz.Geometry.SmoothMapExtension
