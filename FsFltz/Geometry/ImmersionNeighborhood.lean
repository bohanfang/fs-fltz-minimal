import FsFltz.Geometry.LocalInverse
import FsFltz.Geometry.DomainRestriction
import FsFltz.Geometry.Family
import FsFltz.Geometry.CompactEmbeddingNeighborhood
import FsFltz.Geometry.ParameterGraphImmersion
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Embedding neighborhoods of smooth compact germs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–141,
`def:chain`, lines 163–169, and `sec:lean`, lines 788–814. The source
requires an embedding on the compact ribbon. Injectivity and immersion
on that compact set do not require the whole supplied extension to embed.
The local producer below uses a continuous linear left inverse of the
actual derivative and the native inverse function theorem.

This does not construct an ambient extension of an arbitrary intrinsic
manifold with boundary.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

set_option backward.isDefEq.respectTransparency false

/-- An injective derivative on a genuine smooth open domain supplies an
open neighborhood on which the map is injective and remains immersive.
The linear projection used in the proof is chosen from the actual derivative. -/
theorem exists_isOpen_injective_immersion_neighborhood
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N] {f : M → N} {W : Set M} {a : M}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f W) (haW : a ∈ W)
    (hd : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a)) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧ InjOn f U ∧
      ∀ y ∈ U, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y) := by
  let c := chartAt F (f a)
  let df : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f a
  obtain ⟨A, hA⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := df) hd
  let q : M → E := A ∘ c ∘ f
  let V := W ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have haV : a ∈ V := ⟨haW, mem_chart_source F (f a)⟩
  have hAs : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ A := A.contDiff.contMDiff
  have hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ q V := by
    exact (hAs.contMDiffOn (s := univ)).comp
      (contMDiffOn_chart.comp (hf.mono inter_subset_left) (fun _ hy => hy.2))
      (fun _ _ => mem_univ _)
  have hfa := (hf.contMDiffAt (hW.mem_nhds haW)).mdifferentiableAt (by simp)
  have hca := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
    (c.open_source.mem_nhds haV.2)
  have hchart : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c (f a) = ContinuousLinearMap.id ℝ F := by
    exact mfderiv_extChartAt_self (I := 𝓘(ℝ, F))
  have hqd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) q a = ContinuousLinearMap.id ℝ E := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((A ∘ c) ∘ f) a = _
    rw [mfderiv_comp a ((hAs.contMDiffAt.comp (f a) hca).mdifferentiableAt (by simp)) hfa]
    rw [mfderiv_comp (f a) (hAs.mdifferentiableAt (by simp))
      (hca.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, A.fderiv, hchart]
    ext v
    exact hA v
  obtain ⟨e, hae, heq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    hV hq haV (by rw [hqd]; exact Function.bijective_id)
  refine ⟨e.source ∩ V, e.open_source.inter hV, ⟨hae, haV⟩,
    fun _ hy => hy.2.1, ?_, ?_⟩
  · intro y hy z hz he
    apply e.toPartialEquiv.injOn hy.1 hz.1
    rw [← heq hy.1, ← heq hz.1]
    exact congrArg (A ∘ c) he
  · intro y hy
    have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ q y := ⟨e, hy.1, heq⟩
    have hfy := (hf.contMDiffAt (hW.mem_nhds hy.2.1)).mdifferentiableAt (by simp)
    have hcy := (contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hy.2.2)
    have he := mfderiv_comp (f := f) (g := A ∘ c) y
      ((hAs.contMDiffAt.comp (f y) hcy).mdifferentiableAt (by simp)) hfy
    intro v w hvw
    apply (hlocal.isInvertible_mfderiv (by simp)).injective
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((A ∘ c) ∘ f) y) v =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((A ∘ c) ∘ f) y) w
    rw [he]
    exact congrArg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (A ∘ c) (f y)) hvw

/-- Injective derivatives persist on an open smooth domain. This follows
from the actual local projected inverses, including zero-dimensional models. -/
theorem isOpen_injective_mfderiv_on
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, F) ∞ N] {f : M → N} {W : Set M}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f W) :
    IsOpen {x | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨hxW, hxi⟩
  obtain ⟨U, hUo, hxU, hUW, _, hUi⟩ :=
    exists_isOpen_injective_immersion_neighborhood hW hf hxW hxi
  exact mem_of_superset (hUo.mem_nhds hxU) (fun y hy => ⟨hUW hy, hUi y hy⟩)

namespace SmoothManifold

/-- A smooth compact germ which is injective and immersive on its compact
carrier constructs an actual smooth embedding on some open neighborhood.
No embedding of the entire supplied extension manifold is an input. -/
theorem exists_smooth_embedding_neighborhood {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (K : Set M.Point)
    (hK : IsCompact K) (f : M.Point → N.Point) (W : Set M.Point)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (hf : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ f W)
    (hinj : InjOn f K)
    (himm : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x)) :
    ∃ (U : TopologicalSpace.Opens M.Point) (_hKU : K ⊆ U)
      (j : (M.restrict U).SmoothEmbedding N), (U : Set M.Point) ⊆ W ∧
      ∀ x, j.map x = f x.val := by
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  let S := {x | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x)}
  have hSo : IsOpen S := isOpen_injective_mfderiv_on hW hf
  have hKS : K ⊆ S := fun x hx => ⟨hKW hx, himm x hx⟩
  have hloc : ∀ x ∈ K, ∃ u ∈ 𝓝 x, InjOn f u := by
    intro x hx
    obtain ⟨u, huo, hxu, _, hui, _⟩ :=
      exists_isOpen_injective_immersion_neighborhood hW hf (hKW hx) (himm x hx)
    exact ⟨u, huo.mem_nhds hxu, hui⟩
  obtain ⟨U, hUo, hKU, hUS, _, hUe⟩ := exists_isOpen_embedding_neighborhood
    hK hSo hKS (hf.continuousOn.mono (fun _ hx => hx.1)) hinj hloc
  have hUW : U ⊆ W := fun _ hx => (hUS (subset_closure hx)).1
  let u : TopologicalSpace.Opens M.Point := ⟨U, hUo⟩
  have hs : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (fun x : u => f x.val) := by
    intro x
    exact (hf.contMDiffAt (hW.mem_nhds (hUW x.property))).comp x
      contMDiff_subtype_val.contMDiffAt
  let j : (M.restrict u).SmoothEmbedding N :=
    { map := ⟨fun x => f x.val, hs⟩
      embedding := hUe
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
          (fun x : u => f x.val) x)
        rw [M.mfderiv_comp_restrict_val N u x
          ((hf.contMDiffAt (hW.mem_nhds (hUW x.property))).mdifferentiableAt (by simp))]
        exact (hUS (subset_closure x.property)).2 }
  exact ⟨u, hKU, j, hUW, fun _ => rfl⟩

/-- A jointly smooth family which embeds its compact carrier constructs
smooth embeddings on one common spatial neighborhood. The parameter graph
and compact tube construction preserve an actual open extension across both
parameter endpoints, without requiring global smoothness in real time. -/
theorem exists_uniform_embedding_neighborhood {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e) (K : Set M.Point)
    (hK : IsCompact K) (j : ℝ → M.Point → N.Point) (W : Set (ℝ × M.Point))
    (hW : IsOpen W) (hcover : parameterInterval ×ˢ K ⊆ W)
    (hjs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p => j p.1 p.2) W)
    (hinj : ∀ t ∈ parameterInterval, InjOn (j t) K)
    (himm : ∀ t ∈ parameterInterval, ∀ x ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) (j t) x)) :
    ∃ (U : TopologicalSpace.Opens M.Point) (_hKU : K ⊆ U)
      (j' : Parameter → (M.restrict U).SmoothEmbedding N),
      (∀ t x, (j' t).map x = j t.val x.val) ∧
      (M.restrict U).IsSmoothIntervalMapFamily N (fun t => (j' t).map) ∧
      ∃ V : TopologicalSpace.Opens ℝ, parameterInterval ⊆ V ∧
        (V : Set ℝ) ×ˢ (U : Set M.Point) ⊆ W := by
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  let J : ℝ × M.Point → ℝ × N.Point := fun p => (p.1, j p.1 p.2)
  have hgraph : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) ∞ J W := contMDiffOn_fst.prodMk hjs
  have hsource : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ (ℝ × M.Point) := inferInstance
  have htarget : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) ∞ (ℝ × N.Point) := inferInstance
  let : ChartedSpace (ℝ × Model d) (ℝ × M.Point) := prodChartedSpace ℝ ℝ (Model d) M.Point
  let : ChartedSpace (ℝ × Model e) (ℝ × N.Point) := prodChartedSpace ℝ ℝ (Model e) N.Point
  have : IsManifold 𝓘(ℝ, ℝ × Model d) ∞ (ℝ × M.Point) := by
    rw [← modelWithCornersSelf_prod] at hsource
    exact hsource
  have : IsManifold 𝓘(ℝ, ℝ × Model e) ∞ (ℝ × N.Point) := by
    rw [← modelWithCornersSelf_prod] at htarget
    exact htarget
  have hgs : ContMDiffOn 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model e) ∞ J W := by
    simpa only [← modelWithCornersSelf_prod] using hgraph
  have hgi (p : ℝ × M.Point) (hp : p ∈ parameterInterval ×ˢ K) :
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model e) J p) := by
    have hd := (hjs.contMDiffAt (hW.mem_nhds (hcover hp))).mdifferentiableAt (by simp)
    have hi := (M.injective_mfderiv_parameterGraph_iff N hd).mpr (himm p.1 hp.1 p.2 hp.2)
    rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model d),
      ← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model e)] at hi
    exact hi
  let S := {p | p ∈ W ∧ Function.Injective
    (mfderiv 𝓘(ℝ, ℝ × Model d) 𝓘(ℝ, ℝ × Model e) J p)}
  have hSo : IsOpen S := isOpen_injective_mfderiv_on hW hgs
  have hKS : parameterInterval ×ˢ K ⊆ S := fun p hp => ⟨hcover hp, hgi p hp⟩
  have hloc : ∀ p ∈ parameterInterval ×ˢ K, ∃ u ∈ 𝓝 p, InjOn J u := by
    intro p hp
    obtain ⟨u, huo, hpu, _, hui, _⟩ :=
      exists_isOpen_injective_immersion_neighborhood hW hgs (hcover hp) (hgi p hp)
    exact ⟨u, huo.mem_nhds hpu, hui⟩
  obtain ⟨V, U, hVo, hUo, hIV, hKU, hVUS, hUe⟩ :=
    exists_isOpen_uniform_embedding_neighborhood (P := parameterInterval)
      isCompact_Icc hK hSo hKS
      (hjs.continuousOn.mono (fun _ hp => hp.1)) hinj hloc
  have hVUW : V ×ˢ U ⊆ W := fun p hp => (hVUS hp).1
  let u : TopologicalSpace.Opens M.Point := ⟨U, hUo⟩
  have hs (t : Parameter) : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞
      (fun x : u => j t.val x.val) := by
    intro x
    exact (M.contMDiffAt_slice_of_joint N hW hjs
      (hVUW (show (t.val, x.val) ∈ V ×ˢ U from ⟨hIV t.property, x.property⟩))).comp x
      contMDiff_subtype_val.contMDiffAt
  let j' : Parameter → (M.restrict u).SmoothEmbedding N := fun t =>
    { map := ⟨fun x => j t.val x.val, hs t⟩
      embedding := hUe t.val (hIV t.property)
      immersion := by
        intro x
        have hp : (t.val, x.val) ∈ W := hVUW ⟨hIV t.property, x.property⟩
        have hd := (hjs.contMDiffAt (hW.mem_nhds hp)).mdifferentiableAt (by simp)
        have hgraphinj := (hVUS (show (t.val, x.val) ∈ V ×ˢ U from
          ⟨hIV t.property, x.property⟩)).2
        have hi := (M.injective_mfderiv_parameterGraph_iff N hd).mp (by
          rw [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model d),
            ← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := Model e)]
          exact hgraphinj)
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
          (fun x : u => j t.val x.val) x)
        rw [M.mfderiv_comp_restrict_val N u x
          ((M.contMDiffAt_slice_of_joint N hW hjs hp).mdifferentiableAt (by simp))]
        exact hi }
  refine ⟨u, hKU, j', fun _ _ => rfl, ?_, ⟨V, hVo⟩, hIV, hVUW⟩
  refine ⟨fun t x => j t x.val, ⟨V ×ˢ univ, hVo.prod isOpen_univ, ?_, ?_⟩,
    fun _ => rfl⟩
  · intro p hp
    exact ⟨hIV hp.1, mem_univ _⟩
  · have hpre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × u => (p.1, p.2.val)) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    exact hjs.comp hpre.contMDiffOn (fun p hp => hVUW ⟨hp.1, p.2.property⟩)

end SmoothManifold
end FsFltz.Geometry
