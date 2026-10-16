import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Shrinking real-open map extensions under coordinate changes

The smooth extension convention in `geoemtric-part-fsf.tex`, lines 119–122,
is stable under actual real-open coordinate diffeomorphisms. The lemma
below constructs the required common open domain explicitly. It supports
coordinate changes for the canonical-line maps in `def:maslov`, lines
212–244, without imposing globally defined extensions.
-/

open Set Topology
open scoped Manifold ContDiff

namespace FsFltz.Geometry.RealOpenMapExtension

variable {E₀ E₁ F₁ F₀ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]

/-- Shrink a smooth extension's open domain so precomposition and
postcomposition by partial coordinate diffeomorphisms are defined and smooth. -/
theorem exists_composition_domain
    (A : PartialDiffeomorph 𝓘(ℝ, E₀) 𝓘(ℝ, E₁) E₀ E₁ ∞)
    (B : PartialDiffeomorph 𝓘(ℝ, F₁) 𝓘(ℝ, F₀) F₁ F₀ ∞)
    (U : TopologicalSpace.Opens E₁) (G : E₁ → F₁) (hG : ContDiffOn ℝ ∞ G U)
    {x : E₀} (hxA : x ∈ A.source) (hxU : A x ∈ U) (hxB : G (A x) ∈ B.source) :
    ∃ V : TopologicalSpace.Opens E₀,
      x ∈ V ∧ (V : Set E₀) ⊆ A.source ∧
      (∀ y ∈ V, A y ∈ U ∧ G (A y) ∈ B.source) ∧
      ContDiffOn ℝ ∞ (fun y => B (G (A y))) V := by
  let S : Set E₀ := A.source ∩ A ⁻¹' U
  have hA : ContDiffOn ℝ ∞ A A.source := A.contMDiffOn_toFun.contDiffOn
  have hS : IsOpen S :=
    hA.continuousOn.isOpen_inter_preimage A.open_source U.isOpen
  have hGA : ContDiffOn ℝ ∞ (fun y => G (A y)) S :=
    hG.comp (hA.mono inter_subset_left) inter_subset_right
  let V : TopologicalSpace.Opens E₀ :=
    ⟨S ∩ (fun y => G (A y)) ⁻¹' B.source,
      hGA.continuousOn.isOpen_inter_preimage hS B.open_source⟩
  refine ⟨V, ⟨⟨hxA, hxU⟩, hxB⟩, (fun _ hy => hy.1.1),
    (fun _ hy => ⟨hy.1.2, hy.2⟩), ?_⟩
  exact B.contMDiffOn_toFun.contDiffOn.comp (hGA.mono inter_subset_left)
    inter_subset_right

end FsFltz.Geometry.RealOpenMapExtension
