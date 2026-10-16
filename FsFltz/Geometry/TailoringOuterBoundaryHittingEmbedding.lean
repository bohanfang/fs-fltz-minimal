import FsFltz.Geometry.TailoringOuterBoundaryHittingImmersion
import FsFltz.Geometry.CompactEmbeddingNeighborhood
import FsFltz.Geometry.TailoringIntrinsicShrinkingMarking

/-!
# One common full-fiber neighborhood of embedded hitting projections

Source: `geometric-part-fsf-proof.tex`, the paragraph after `prop:band`,
lines 1818–1840. Local inverses from transverse backward scalar hits,
compact core injectivity and the tube lemma construct one open spatial
neighborhood for the whole coefficient interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance outerHittingEmbeddingCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance outerHittingEmbeddingSmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Transverse backward hits and compact core injectivity construct a common
embedding neighborhood. Differential injectivity holds on its whole product. -/
theorem exists_uniform_outer_projection_embedding_neighborhood
    {d : ℕ} (M : SmoothManifold d) (j : M.SmoothEmbedding (lgManifold n))
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hfst : ∀ t p, (G t p).1 = p.1)
    {f : LGSpace n → ℝ} (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ f)
    (hlevel : ∀ x, f (j.map x) = 1)
    {W : Set (ℝ × M.Point)} (hW : IsOpen W) {τ : ℝ × M.Point → ℝ}
    (hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℝ) ∞ τ W)
    {P : Set ℝ} {C : Set M.Point} (hP : IsCompact P) (hC : IsCompact C)
    (hPC : P ×ˢ C ⊆ W)
    (hinj : ∀ k ∈ P, InjOn (fun x => (G (τ (k, x)) (k, j.map x)).2) C)
    (hpos : ∀ p ∈ P ×ˢ C, 0 < deriv (fun t => f (G t (p.1, j.map p.2)).2) 0) :
    ∃ V : Set ℝ, ∃ U : Set M.Point, IsOpen V ∧ IsOpen U ∧ P ⊆ V ∧ C ⊆ U ∧
      V ×ˢ U ⊆ W ∧
      (∀ k ∈ V, IsEmbedding (fun x : U => (G (τ (k, x)) (k, j.map x)).2)) ∧
      ∀ p ∈ V ×ˢ U, Function.Injective
        (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          (fun q => (q.1, (G (τ q) (q.1, j.map q.2)).2)) p) := by
  let : LocallyCompactSpace M.Point := ChartedSpace.locallyCompactSpace (Model d) M.Point
  let π : ℝ × M.Point → LGSpace n := fun q => (G (τ q) (q.1, j.map q.2)).2
  let Γ : ℝ × M.Point → ℝ × LGSpace n := fun q => (q.1, π q)
  let S : Set (Set (ℝ × M.Point)) := {U | IsOpen U ∧ U ⊆ W ∧
    ∀ p ∈ U, Function.Injective
      (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) Γ p)}
  have hlocal (p) (hp : p ∈ P ×ˢ C) :=
    exists_outer_projection_injective_immersion_neighborhood M j G hG hfst hf hlevel
      hW hτ p (hPC hp) (hpos p hp)
  have hO : IsOpen (⋃₀ S) := isOpen_sUnion (fun _ h => h.1)
  have hOW : ⋃₀ S ⊆ W := by
    intro p hp
    obtain ⟨U, hU, hpU⟩ := mem_sUnion.mp hp
    exact hU.2.1 hpU
  have hPCO : P ×ˢ C ⊆ ⋃₀ S := by
    intro p hp
    obtain ⟨U, hU, hpU, hUW, _, hd⟩ := hlocal p hp
    exact mem_sUnion.mpr ⟨U, ⟨hU, hUW, hd⟩, hpU⟩
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × M.Point => (p.1, j.map p.2)) :=
    contMDiff_fst.prodMk (j.map.contMDiff.comp contMDiff_snd)
  have hπ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      𝓘(ℝ, Model (2 * n)) ∞ π W := by
    intro p hp
    exact (hG.comp_contMDiffOn (hτ.prodMk hi.contMDiffOn) p hp).snd
  obtain ⟨V, U, hV, hU, hPV, hCU, hVU, hemb⟩ :=
    exists_isOpen_uniform_embedding_neighborhood hP hC hO hPCO
      (hπ.continuousOn.mono hOW) hinj (fun p hp => by
        obtain ⟨U, hU, hpU, _, hinjU, _⟩ := hlocal p hp
        exact ⟨U, hU.mem_nhds hpU, hinjU⟩)
  refine ⟨V, U, hV, hU, hPV, hCU, hVU.trans hOW, hemb, ?_⟩
  intro p hp
  obtain ⟨U', hU', hpU'⟩ := mem_sUnion.mp (hVU hp)
  exact hU'.2.2 p hpU'

/-- The actual full-fiber marking supplies the compact native core; the
constructed local inverses then give smooth embeddings on one common open
full-fiber neighborhood, retaining the literal hitting formula. -/
theorem FullFiberRibbonMarking.exists_uniform_outer_hitting_embeddings
    {Q : WitnessedPair n}
    {R : Q.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking Q R f 1 φ)
    (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    {L : Set (LGSpace n)} (hcore : R.map '' Q.ribbonCompletion.core = L)
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hfst : ∀ t p, (G t p).1 = p.1)
    {P : Set ℝ} (hP : IsCompact P)
    {W : Set (ℝ × LGSpace n)} (hW : IsOpen W) (hPW : P ×ˢ L ⊆ W)
    {τ : ℝ × LGSpace n → ℝ}
    (hτ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞ τ W)
    (hinj : ∀ k ∈ P, InjOn (fun y => (G (τ (k, y)) (k, y)).2) L)
    (hpos : ∀ k ∈ P, ∀ y ∈ L, 0 < deriv (fun t => (f (G t (k, y)).2).re) 0) :
    ∃ (V : TopologicalSpace.Opens ℝ) (U : TopologicalSpace.Opens M.manifold.Point),
      P ⊆ (V : Set ℝ) ∧ M.embedding.map ⁻¹' L ⊆ (U : Set M.manifold.Point) ∧
      (∀ p ∈ (V : Set ℝ) ×ˢ (U : Set M.manifold.Point),
        (p.1, M.embedding.map p.2) ∈ W) ∧
      ∃ e : V → (M.manifold.restrict U).SmoothEmbedding (lgManifold n),
        (∀ k x, (e k).map x =
          (G (τ (k.val, M.embedding.map x.val)) (k.val, M.embedding.map x.val)).2) ∧
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
          𝓘(ℝ, Model (2 * n)) ∞
          (fun p : ℝ × M.manifold.Point =>
            (G (τ (p.1, M.embedding.map p.2)) (p.1, M.embedding.map p.2)).2)
          ((V : Set ℝ) ×ˢ (U : Set M.manifold.Point)) := by
  let a : Q.ribbonDomain.domain.extension.Point → M.manifold.Point :=
    fun x => M.marking.equiv (Q.ribbonCompletion.inclusion.map x)
  let C : Set M.manifold.Point := a '' Q.ribbonCompletion.core
  have hC : IsCompact C := Q.ribbonCompletion.isCompact_core.image
    (M.marking.equiv.contMDiff.continuous.comp
      Q.ribbonCompletion.inclusion.map.contMDiff.continuous)
  have hsquare (x) (hx : x ∈ Q.ribbonCompletion.core) : M.embedding.map (a x) = R.map x := by
    change M.embedding.map (M.marking.equiv (Q.ribbonCompletion.inclusion.map x)) = _
    rw [M.marking.inclusion (⟨x, hx.1⟩ : Q.ribbonDomain.domain.Point)]
    exact M.compact_square ⟨x, hx.1⟩
  have hCL : M.embedding.map '' C = L := by
    calc
      M.embedding.map '' C = (M.embedding.map ∘ a) '' Q.ribbonCompletion.core :=
        image_image M.embedding.map a Q.ribbonCompletion.core
      _ = R.map '' Q.ribbonCompletion.core := image_congr hsquare
      _ = L := hcore
  have hLC : M.embedding.map ⁻¹' L = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := hCL.symm ▸ hx
      exact M.embedding.embedding.injective he ▸ hy
    · intro hx
      exact hCL ▸ mem_image_of_mem M.embedding.map hx
  let i : ℝ × M.manifold.Point → ℝ × LGSpace n := fun p => (p.1, M.embedding.map p.2)
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ i :=
    contMDiff_fst.prodMk (M.embedding.map.contMDiff.comp contMDiff_snd)
  have hWi : IsOpen (i ⁻¹' W) := hW.preimage hi.continuous
  have hτi := hτ.comp hi.contMDiffOn (fun _ hx => hx)
  have hlevel (x : M.manifold.Point) : (f (M.embedding.map x)).re = 1 := by
    have hx : M.embedding.map x ∈ {y | f y = 1} := M.image ▸ mem_range_self x
    change f (M.embedding.map x) = 1 at hx
    simp only [hx, Complex.one_re]
  obtain ⟨V, U, hV, hU, hPV, hCU, hVU, hemb, himm⟩ :=
    exists_uniform_outer_projection_embedding_neighborhood M.manifold M.embedding G hG hfst
      (Complex.reCLM.contMDiff.comp hf) hlevel hWi hτi hP hC
      (fun p hp => hPW ⟨hp.1, hCL ▸ mem_image_of_mem M.embedding.map hp.2⟩)
      (fun k hk x hx y hy he => M.embedding.embedding.injective
        (hinj k hk (hCL ▸ mem_image_of_mem M.embedding.map hx)
          (hCL ▸ mem_image_of_mem M.embedding.map hy) he))
      (fun p hp => hpos p.1 hp.1 (M.embedding.map p.2)
        (hCL ▸ mem_image_of_mem M.embedding.map hp.2))
  let v : TopologicalSpace.Opens ℝ := ⟨V, hV⟩
  let u : TopologicalSpace.Opens M.manifold.Point := ⟨U, hU⟩
  let π : ℝ × M.manifold.Point → LGSpace n := fun p => (G (τ (i p)) (i p)).2
  have hπ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n)) ∞ π (i ⁻¹' W) := by
    intro p hp
    exact (hG.comp_contMDiffOn (hτi.prodMk hi.contMDiffOn) p hp).snd
  have hslice (k : v) (x : u) : ContMDiffAt 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, Model (2 * n)) ∞ (fun y => π (k.val, y)) x.val :=
    (hπ.contMDiffAt (hWi.mem_nhds (hVU ⟨k.property, x.property⟩))).comp x.val
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  let e (k : v) : (M.manifold.restrict u).SmoothEmbedding (lgManifold n) :=
    { map := ⟨fun x => π (k.val, x.val), fun x =>
        (hslice k x).comp x contMDiff_subtype_val.contMDiffAt⟩
      embedding := hemb k.val k.property
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
          𝓘(ℝ, Model (2 * n)) (fun x : u => π (k.val, x.val)) x)
        rw [M.manifold.mfderiv_comp_restrict_val (lgManifold n) u x
          ((hslice k x).mdifferentiableAt (by simp))]
        apply (M.manifold.injective_mfderiv_parameterGraph_iff (lgManifold n)
          (j := fun k y => π (k, y)) (p := (k.val, x.val))
          ((hπ.contMDiffAt (hWi.mem_nhds (hVU ⟨k.property, x.property⟩))).mdifferentiableAt
            (by simp))).mp
        exact himm (k.val, x.val) ⟨k.property, x.property⟩ }
  refine ⟨v, u, hPV, ?_, hVU, e, (fun _ _ => rfl), hπ.mono hVU⟩
  rw [hLC]
  exact hCU

end FsFltz
