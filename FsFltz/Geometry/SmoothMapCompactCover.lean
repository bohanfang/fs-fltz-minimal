import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite compact chart patches from smooth map germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–161, and
`sec:lean`, lines 788–814. This foundational producer replaces arbitrary
smooth local germs along a compact carrier by finitely many compact
patches with open convex target-coordinate ranges. It supplies local data
for map extension, not a geometric comparison or completion marking.
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

/-- A smooth local extension of the carrier map, with its whole local
range in an open convex subset of a genuine smooth target chart. -/
structure ChartPatch (A : Set X) (f : A → N) where
  domain : TopologicalSpace.Opens X
  map : domain → N
  smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ map
  agreement : ∀ x (hxU : x ∈ domain) (hxA : x ∈ A), map ⟨x, hxU⟩ = f ⟨x, hxA⟩
  chart : OpenPartialHomeomorph N F
  chart_mem : chart ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N
  coordinates : Set F
  coordinates_open : IsOpen coordinates
  coordinates_convex : Convex ℝ coordinates
  coordinates_target : coordinates ⊆ chart.target
  map_range : ∀ x : domain, map x ∈ chart.source ∧ chart (map x) ∈ coordinates

/-- Any smooth germ matching a carrier map can be shrunk into an open
convex coordinate ball in the chart at that carrier value. -/
theorem exists_chartPatch_of_local
    [IsManifold 𝓘(ℝ, F) ∞ N]
    {A : Set X} (f : A → N) (x : A)
    (hlocal : ∃ U : TopologicalSpace.Opens X, (x : X) ∈ U ∧
      ∃ g : U → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyU : y ∈ U) (hyA : y ∈ A), g ⟨y, hyU⟩ = f ⟨y, hyA⟩) :
    ∃ p : ChartPatch (E := E) (F := F) A f, (x : X) ∈ p.domain := by
  obtain ⟨U, hxU, g, hg, heq⟩ := hlocal
  let e := chartAt F (f x)
  have hxsource : f x ∈ e.source := mem_chart_source F (f x)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_target.mem_nhds (e.map_source hxsource))
  let C := Metric.ball (e (f x)) r
  let T := e.source ∩ e ⁻¹' C
  have hTo : IsOpen T := e.isOpen_inter_preimage Metric.isOpen_ball
  let S : Set U := g ⁻¹' T
  have hSo : IsOpen S := hTo.preimage hg.continuous
  let W : TopologicalSpace.Opens X :=
    ⟨Subtype.val '' S, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hSo⟩
  have hWU : (W : Set X) ⊆ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  let a : W → U := fun y => ⟨y, hWU y.property⟩
  have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff U a).mp contMDiff_subtype_val
  let p : ChartPatch (E := E) (F := F) A f :=
    { domain := W
      map := g ∘ a
      smooth := hg.comp ha
      agreement := fun y hyU hyA => heq y (hWU hyU) hyA
      chart := e
      chart_mem := IsManifold.chart_mem_maximalAtlas (f x)
      coordinates := C
      coordinates_open := Metric.isOpen_ball
      coordinates_convex := convex_ball _ _
      coordinates_target := hball
      map_range := by
        intro y
        obtain ⟨z, hz, hzy⟩ := y.property
        have hz' : z = a y := Subtype.ext hzy
        change g (a y) ∈ e.source ∧ e (g (a y)) ∈ C
        rw [← hz']
        exact hz }
  refine ⟨p, ?_⟩
  have hxg : g ⟨x, hxU⟩ = f x := heq x hxU x.property
  refine ⟨⟨x, hxU⟩, ?_, rfl⟩
  change g ⟨x, hxU⟩ ∈ e.source ∧ e (g ⟨x, hxU⟩) ∈ C
  rw [hxg]
  exact ⟨hxsource, Metric.mem_ball_self hr⟩

/-- Local smooth map germs along a compact carrier yield a finite compact
cover subordinate to chart patches. Each selected compact set is a subset
of the original carrier, so the same prescribed map is retained throughout
finite extension induction. Empty carriers and targets need no default map.
-/
theorem exists_finite_compact_chart_cover_of_local
    [T2Space X] [IsManifold 𝓘(ℝ, F) ∞ N]
    {A : Set X} (hA : IsCompact A) (f : A → N)
    (hlocal : ∀ x : A, ∃ U : TopologicalSpace.Opens X, (x : X) ∈ U ∧
      ∃ g : U → N, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyU : y ∈ U) (hyA : y ∈ A), g ⟨y, hyU⟩ = f ⟨y, hyA⟩) :
    ∃ p : A → ChartPatch (E := E) (F := F) A f, ∃ t : Finset A, ∃ K : A → Set X,
      (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ (p i).domain) ∧
      A = ⋃ i ∈ t, K i ∧ (∀ i ∈ t, K i ⊆ A) := by
  classical
  choose p hp using fun x => exists_chartPatch_of_local f x (hlocal x)
  have hcover : A ⊆ ⋃ i : A, ((p i).domain : Set X) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun i => ((p i).domain : Set X))
    (fun i => (p i).domain.isOpen) hcover
  obtain ⟨K, hKc, hKU, hKA⟩ := hA.finite_compact_cover t
    (fun i => ((p i).domain : Set X)) (fun i _ => (p i).domain.isOpen) ht
  refine ⟨p, t, K, hKc, hKU, hKA, ?_⟩
  intro i hi x hx
  rw [hKA]
  exact mem_iUnion₂.mpr ⟨i, hi, hx⟩

end FsFltz.Geometry.SmoothMapExtension
