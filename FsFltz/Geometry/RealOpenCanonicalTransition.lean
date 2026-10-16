import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-!
# Real-open scalar skew products

The real smoothness convention of `geoemtric-part-fsf.tex`, lines 119–122,
and the squared canonical line in `def:maslov`, lines 212–244, require
complex fiber coordinates over real open base neighborhoods. This file
constructs their local transition diffeomorphisms from an actual base
partial diffeomorphism and a smooth nonzero complex scalar.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace FsFltz.Geometry.RealOpenCanonicalTransition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real-smooth complex scalar skew product over a base partial
diffeomorphism, restricted to the open locus where its scalar is nonzero. -/
def skewProduct
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U) :
    PartialDiffeomorph 𝓘(ℝ, E × ℂ) 𝓘(ℝ, F × ℂ) (E × ℂ) (F × ℂ) ∞ := by
  let S : Set E := {x | x ∈ U ∧ a x ≠ 0}
  have hS : IsOpen S := by
    exact ha.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ne
  let T : Set F := B.target ∩ B.symm ⁻¹' S
  have hT : IsOpen T :=
    B.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage B.open_target hS
  have hB : ContDiffOn ℝ ∞ B B.source := B.contMDiffOn_toFun.contDiffOn
  have hBi : ContDiffOn ℝ ∞ B.symm B.target := B.contMDiffOn_invFun.contDiffOn
  refine
    { toFun := fun q => (B q.1, a q.1 * q.2)
      invFun := fun q => (B.symm q.1, (a (B.symm q.1))⁻¹ * q.2)
      source := (B.source ∩ S) ×ˢ univ
      target := T ×ˢ univ
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := (B.open_source.inter hS).prod isOpen_univ
      open_target := hT.prod isOpen_univ
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · intro q hq
    refine ⟨⟨B.map_source hq.1.1, ?_⟩, mem_univ _⟩
    change B.toPartialEquiv.symm (B.toPartialEquiv q.1) ∈ S
    rw [B.toPartialEquiv.left_inv hq.1.1]
    exact hq.1.2
  · intro q hq
    exact ⟨⟨B.map_target hq.1.1, hq.1.2⟩, mem_univ _⟩
  · intro q hq
    apply Prod.ext
    · exact B.left_inv hq.1.1
    · change (a (B.toPartialEquiv.symm (B.toPartialEquiv q.1)))⁻¹ * (a q.1 * q.2) = q.2
      rw [B.toPartialEquiv.left_inv hq.1.1]
      simp only [← mul_assoc, inv_mul_cancel₀ hq.1.2.2, one_mul]
  · intro q hq
    apply Prod.ext
    · exact B.right_inv hq.1.1
    · simp only [← mul_assoc, mul_inv_cancel₀ hq.1.2.2, one_mul]
  · exact ((hB.comp contDiffOn_fst (fun _ hq => hq.1.1)).prodMk
      ((ha.comp contDiffOn_fst (fun _ hq => hq.1.2.1)).mul
        contDiffOn_snd)).contMDiffOn
  · have hb : ContDiffOn ℝ ∞ (fun q : F × ℂ => B.symm q.1) (T ×ˢ univ) :=
      hBi.comp contDiffOn_fst (fun _ hq => hq.1.1)
    have hs : ContDiffOn ℝ ∞ (fun q : F × ℂ => a (B.symm q.1)) (T ×ˢ univ) :=
      ha.comp hb (fun _ hq => hq.1.2.1)
    exact (hb.prodMk ((hs.inv (fun _ hq => hq.1.2.2)).mul
      contDiffOn_snd)).contMDiffOn

@[simp]
theorem skewProduct_apply
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (q : E × ℂ) : skewProduct B U a ha q = (B q.1, a q.1 * q.2) := rfl

@[simp]
theorem skewProduct_symm_apply
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (q : F × ℂ) : (skewProduct B U a ha).symm q =
      (B.symm q.1, (a (B.symm q.1))⁻¹ * q.2) := rfl

@[simp]
theorem mem_skewProduct_source
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (q : E × ℂ) : q ∈ (skewProduct B U a ha).source ↔
      q.1 ∈ B.source ∧ q.1 ∈ U ∧ a q.1 ≠ 0 := by
  simp only [skewProduct, mem_prod, mem_inter_iff, mem_ofPred_eq, mem_univ, and_true]

/-- Every fiber coordinate is present above a base point in the nonzero locus. -/
theorem mk_mem_skewProduct_source
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    {p : E} (hpB : p ∈ B.source) (hpU : p ∈ U) (hpa : a p ≠ 0) (z : ℂ) :
    (p, z) ∈ (skewProduct B U a ha).source :=
  (mem_skewProduct_source B U a ha (p, z)).mpr ⟨hpB, hpU, hpa⟩

@[simp]
theorem mem_skewProduct_target
    (B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : TopologicalSpace.Opens E) (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (q : F × ℂ) : q ∈ (skewProduct B U a ha).target ↔
      q.1 ∈ B.target ∧ B.symm q.1 ∈ U ∧ a (B.symm q.1) ≠ 0 := by
  simp only [skewProduct, mem_prod, mem_inter_iff, mem_preimage, mem_ofPred_eq,
    mem_univ, and_true]

end FsFltz.Geometry.RealOpenCanonicalTransition
