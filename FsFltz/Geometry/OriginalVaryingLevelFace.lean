import FsFltz.Geometry.OriginalVaryingLevelFamily
import FsFltz.Geometry.SmoothEmbeddingFactorization
import FsFltz.Geometry.TailoringHittingRibbonFamily

/-!
# Restrict the varying original ribbon to its common unrounded face

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 450–469;
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 958–971. A compact
family whose whole carriers lie in one open face has one common extension
inside that face. The target restriction retains the actual embeddings and
their joint smoothness at parameter endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

/-- A compact embedding family whose full carriers lie in one open target
has a common source extension inside that target, retaining the literal
maps and their genuine joint parameter-endpoint extensions. -/
theorem exists_embeddingFamily_into_open {d e : ℕ}
    (D : CompactDomain d) (N : SmoothManifold e)
    (J : Parameter → D.extension.SmoothEmbedding N)
    (hJ : D.extension.IsSmoothIntervalMapFamily N (fun t => (J t).map))
    (O : TopologicalSpace.Opens N.Point)
    (hO : ∀ t x, x ∈ D.carrier → (J t).map x ∈ O) :
    ∃ (U : TopologicalSpace.Opens D.extension.Point) (_hDU : D.carrier ⊆ U)
      (K : Parameter → (D.extension.restrict U).SmoothEmbedding (N.restrict O)),
      (∀ t x, ((K t).map x).val = (J t).map x.val) ∧
      (D.extension.restrict U).IsSmoothIntervalMapFamily (N.restrict O)
        (fun t => (K t).map) := by
  classical
  obtain ⟨f, ⟨W, hW, hcover, hfs⟩, hf⟩ := hJ
  let Ω : Set (ℝ × D.extension.Point) := W ∩ (fun p => f p.1 p.2) ⁻¹' (O : Set N.Point)
  have hΩ : IsOpen Ω := hfs.continuousOn.isOpen_inter_preimage hW O.isOpen
  have hCΩ : parameterInterval ×ˢ D.carrier ⊆ Ω := by
    intro p hp
    refine ⟨hcover ⟨hp.1, mem_univ _⟩, ?_⟩
    change f p.1 p.2 ∈ O
    rw [hf ⟨p.1, hp.1⟩]
    exact hO ⟨p.1, hp.1⟩ p.2 hp.2
  obtain ⟨V, U, hV, hU, hIV, hDU, hVU⟩ :=
    generalized_tube_lemma isCompact_Icc D.compact hΩ hCΩ
  let U' : TopologicalSpace.Opens D.extension.Point := ⟨U, hU⟩
  have hmem (t : Parameter) (x : U') : (J t).map x.val ∈ O := by
    have hh := (hVU (show (t.val, x.val) ∈ V ×ˢ U from ⟨hIV t.property, x.property⟩)).2
    change f t.val x.val ∈ O at hh
    rwa [hf t] at hh
  let k : Parameter → U' → O := fun t x => ⟨(J t).map x.val, hmem t x⟩
  have hks (t : Parameter) : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞ (k t) :=
    (ContMDiff.subtypeVal_comp_iff O (k t)).mp
      ((J t).map.contMDiff.comp (D.extension.restrictInclusion U').map.contMDiff)
  let K : Parameter → (D.extension.restrict U').SmoothEmbedding (N.restrict O) := fun t =>
    { map := ⟨k t, hks t⟩
      embedding := ((J t).embedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
        (O : Set N.Point) (hmem t)
      immersion := by
        intro x
        have hc := mfderiv_comp (f := k t)
          (g := (Subtype.val : O → N.Point)) x
          ((N.restrictInclusion O).map.contMDiff.mdifferentiableAt (by simp))
          ((hks t).mdifferentiableAt (by simp))
        erw [N.mfderiv_restrict_val O] at hc
        change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e)
          (fun x : U' => (J t).map x.val) x = _ at hc
        rw [D.extension.mfderiv_comp_restrict_val N U' x
          ((J t).map.contMDiff.mdifferentiableAt (by simp))] at hc
        intro v w hvw
        apply (J t).immersion x.val
        rw [hc]
        exact congrArg (ContinuousLinearMap.id ℝ (Model e)) hvw }
  let r : ℝ → U' → O := fun t x =>
    if h : f t x.val ∈ O then ⟨f t x.val, h⟩ else
      ⟨(J parameterZero).map x.val, hmem parameterZero x⟩
  have hpre : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) ∞
      (fun p : ℝ × U' => (p.1, p.2.val)) :=
    contMDiff_fst.prodMk ((D.extension.restrictInclusion U').map.contMDiff.comp contMDiff_snd)
  refine ⟨U', hDU, K, fun _ _ => rfl, r, ⟨V ×ˢ univ, hV.prod isOpen_univ, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact ⟨hIV hp.1, mem_univ _⟩
  · intro p hp
    have hmap := hVU (show (p.1, p.2.val) ∈ V ×ˢ U from ⟨hp.1, p.2.property⟩)
    have hs := (hfs.contMDiffAt (hW.mem_nhds hmap.1)).comp p hpre.contMDiffAt
    apply ((ContMDiffAt.subtypeVal_comp_iff O (fun p : ℝ × U' => r p.1 p.2) p).mp ?_).contMDiffWithinAt
    apply hs.congr_of_eventuallyEq
    filter_upwards [(hV.prod isOpen_univ).mem_nhds hp] with q hq
    have hh := (hVU (show (q.1, q.2.val) ∈ V ×ˢ U from ⟨hq.1, q.2.property⟩)).2
    change f q.1 q.2.val ∈ O at hh
    simp only [Function.comp_apply, r, dite_eq_left hh]
  · intro t
    funext x
    apply Subtype.ext
    have hh : f t.val x.val ∈ O :=
      (hVU (show (t.val, x.val) ∈ V ×ˢ U from ⟨hIV t.property, x.property⟩)).2
    simp only [r, dite_eq_left hh]
    exact congrFun (hf t) x.val

end CompactDomain
end FsFltz.Geometry
