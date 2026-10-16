import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Compact embedding neighborhoods

Topological localization for a smooth extension of a compact ribbon.
The specification `geoemtric-part-fsf.tex`, Definition `def:pair`, lines 132–141,
requires an embedding on the compact ribbon, with smooth extension across its
boundary. It does not require that the entire extension be an embedding.
This module constructs an embedding neighborhood from compact injectivity and
local injectivity. The smooth immersion-to-local-injectivity bridge is separate.
See also the foundational handoff `sec:lean`, lines 783–814.
-/

open Set Filter Topology

namespace FsFltz.Geometry

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Compact injectivity and local injectivity produce an actual embedding on
an open neighborhood whose compact closure stays inside a prescribed open set.
The map is only required to be continuous on that prescribed set. -/
theorem exists_isOpen_embedding_neighborhood [LocallyCompactSpace X]
    [T2Space X] [T2Space Y] {f : X → Y} {K W : Set X}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hf : ContinuousOn f W) (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ closure U ⊆ W ∧ IsCompact (closure U) ∧
      IsEmbedding (fun x : U => f x) := by
  obtain ⟨O, hOo, hKO, hOi⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => hf.continuousAt (hW.mem_nhds (hKW hx))) hloc
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hK (hOo.inter hW)
    (subset_inter hKO hKW)
  have hUL : closure (interior L) ⊆ L :=
    closure_minimal interior_subset hLc.isClosed
  have hLW : L ⊆ W := fun _ hx => (hLO hx).2
  have hLi : InjOn f L := hOi.mono (fun _ hx => (hLO hx).1)
  let : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  have he : IsEmbedding (fun x : L => f x) :=
    ((hf.mono hLW).domRestrict.isClosedEmbedding hLi.injective).isEmbedding
  refine ⟨interior L, isOpen_interior, hKL, hUL.trans hLW,
    hLc.of_isClosed_subset isClosed_closure hUL, ?_⟩
  exact he.comp (IsEmbedding.inclusion interior_subset)

/-- The parameter graph converts compact fiberwise injectivity into a single
embedding neighborhood. A tube inside that neighborhood gives one spatial
neighborhood for every parameter in an open neighborhood of the compact
parameter set. Local injectivity is required only along the compact product. -/
theorem exists_isOpen_uniform_embedding_neighborhood
    {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    [LocallyCompactSpace X] [T2Space T] [T2Space X] [T2Space Y]
    {f : T × X → Y} {P : Set T} {K : Set X} {W : Set (T × X)}
    (hP : IsCompact P) (hK : IsCompact K) (hW : IsOpen W) (hPKW : P ×ˢ K ⊆ W)
    (hf : ContinuousOn f W) (hinj : ∀ t ∈ P, InjOn (fun x => f (t, x)) K)
    (hloc : ∀ p ∈ P ×ˢ K, ∃ u ∈ 𝓝 p, InjOn (fun q => (q.1, f q)) u) :
    ∃ V U, IsOpen V ∧ IsOpen U ∧ P ⊆ V ∧ K ⊆ U ∧ V ×ˢ U ⊆ W ∧
      ∀ t ∈ V, IsEmbedding (fun x : U => f (t, x)) := by
  let J : T × X → T × Y := fun p => (p.1, f p)
  have hJi : InjOn J (P ×ˢ K) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩ ⟨s, y⟩ ⟨_, hy⟩ he
    have hts : t = s := congrArg Prod.fst he
    subst s
    exact Prod.ext rfl (hinj t ht hx hy (congrArg Prod.snd he))
  obtain ⟨Z, hZo, hPKZ, hZW, _, hZe⟩ := exists_isOpen_embedding_neighborhood
    (hP.prod hK) hW hPKW (continuousOn_fst.prodMk hf) hJi hloc
  obtain ⟨V, U, hVo, hUo, hPV, hKU, hVUZ⟩ :=
    generalized_tube_lemma hP hK hZo hPKZ
  refine ⟨V, U, hVo, hUo, hPV, hKU,
    hVUZ.trans (subset_closure.trans hZW), ?_⟩
  intro t ht
  have he : IsEmbedding (fun x : U =>
      (⟨(t, x), hVUZ ⟨ht, x.property⟩⟩ : Z)) :=
    ((isEmbedding_prodMkRight t).comp IsEmbedding.subtypeVal).codRestrict Z _
  exact (isEmbedding_prodMkRight t).of_comp_iff.mp (hZe.comp he)

end FsFltz.Geometry
