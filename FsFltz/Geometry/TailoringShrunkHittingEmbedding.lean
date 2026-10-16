import FsFltz.Geometry.TailoringMarkedHittingEmbedding

/-!
# Hitting embeddings on the entire retained shrunk ribbon

Source: `geometric-part-fsf-proof.tex`, paragraph following `prop:band`,
lines 1818–1845. The whole open extension of the concrete shrinking endpoint
is put inside the actual full-fiber hitting neighborhood. Composition retains
the fixed compact carrier and the actual negative-flow formula.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold


private def embeddingIntoOpen {d e : ℕ} {M : SmoothManifold d} {N : SmoothManifold e}
    (j : M.SmoothEmbedding N) (U : TopologicalSpace.Opens N.Point)
    (hU : ∀ x, j.map x ∈ U) : M.SmoothEmbedding (N.restrict U) where
  map := ⟨fun x => ⟨j.map x, hU x⟩,
    (ContMDiff.subtypeVal_comp_iff U _).mp j.map.contMDiff⟩
  embedding := j.embedding.codRestrict U hU
  immersion := by
    intro x v w hvw
    apply j.immersion x
    have hs : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) ∞
        (fun x => (⟨j.map x, hU x⟩ : U)) :=
      (ContMDiff.subtypeVal_comp_iff U _).mp j.map.contMDiff
    have he := mfderiv_comp (f := fun x => (⟨j.map x, hU x⟩ : U))
      (g := (Subtype.val : U → N.Point)) x
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model e)) (n := ∞)).mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x = _ at he
    rw [he]
    exact congrArg (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model e)
      (Subtype.val : U → N.Point) ⟨j.map x, hU x⟩) hvw

namespace IntrinsicShrinkingData
variable {n : ℕ} {P : WitnessedPair n} (S : IntrinsicShrinkingData P)
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P R f value φ)
    (U : TopologicalSpace.Opens M.manifold.Point)
    (hU : ∀ x : S.extension, (S.fiberEmbedding M parameterOne).map x ∈ U)

/-- Restrict the actual negative-flow fiber embedding to the chosen hitting
neighborhood, without replacing its compact carrier. -/
def fiberEmbeddingInto :
    (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding (M.manifold.restrict U) :=
  embeddingIntoOpen (S.fiberEmbedding M parameterOne) U hU

/-- The actual hitting embedding on the whole open shrinking endpoint. -/
def hittingEmbedding (V : TopologicalSpace.Opens ℝ)
    (e : V → (M.manifold.restrict U).SmoothEmbedding (lgManifold n)) (k : V) :
    (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n) :=
  (e k).comp (S.fiberEmbeddingInto M U hU)

theorem hittingEmbedding_apply (V : TopologicalSpace.Opens ℝ)
    (e : V → (M.manifold.restrict U).SmoothEmbedding (lgManifold n)) (k : V)
    (x : S.extension) :
    (S.hittingEmbedding M U hU V e k).map x =
      (e k).map ⟨(S.fiberEmbedding M parameterOne).map x, hU x⟩ := rfl

include hU in
/-- Joint smoothness of the full-fiber family remains joint smoothness after
precomposition by the actual fixed negative intrinsic flow. -/
theorem contMDiffOn_shrunk_family (V : TopologicalSpace.Opens ℝ)
    {d : ℕ} (N : SmoothManifold d) (g : ℝ × M.manifold.Point → N.Point)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model d) ∞ g ((V : Set ℝ) ×ˢ (U : Set M.manifold.Point))) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model d) ∞
      (fun p : ℝ × S.extension => g (p.1, (S.fiberEmbedding M parameterOne).map p.2))
      ((V : Set ℝ) ×ˢ univ) := by
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2))) ∞
      (fun p : ℝ × S.extension => (p.1, (S.fiberEmbedding M parameterOne).map p.2)) :=
    contMDiff_fst.prodMk ((S.fiberEmbedding M parameterOne).map.contMDiff.comp contMDiff_snd)
  exact hg.comp hi.contMDiffOn (fun p hp => ⟨hp.1, hU p.2⟩)

end IntrinsicShrinkingData

end FsFltz
