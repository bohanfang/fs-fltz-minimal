import FsFltz.Geometry.CoordinateCanonicalTensor

/-!
# Source-local coframes for prescribed native complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. A genuine smooth real extension of the original
source coordinate complex field produces a smooth invertible local coframe.
The complex equation is required only on the original parameter locus; no
complex or symplectic compatibility equation is imposed off that locus.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry

/-- A smooth arbitrary native coordinate complex field produces its source
coframe near each prescribed point. The native coordinate model is merely
identified linearly with the encoded finite-dimensional model. -/
theorem exists_smooth_local_coordinateComplexCoframe {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Model (2 * n) ≃L[ℝ] F)
    {V A : Set E} {p : E} (hV : IsOpen V) (hpV : p ∈ V) (hpA : p ∈ A)
    (K : E → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K V)
    (hsq : ∀ z ∈ V ∩ A, ∀ v, K z (K z v) = -v) :
    ∃ W ⊆ V, IsOpen W ∧ p ∈ W ∧
      ∃ L : E → F →L[ℝ] TangentCoordinates n,
        ContDiffOn ℝ ∞ L W ∧ (∀ z ∈ W, (L z).IsInvertible) ∧
        ∀ z ∈ W ∩ A, ∀ v, L z (K z v) = coordinateComplexStructure n (L z v) := by
  let K' := fun z => P.symm.toContinuousLinearMap.comp ((K z).comp P.toContinuousLinearMap)
  have hK' : ContDiffOn ℝ ∞ K' V :=
    contDiffOn_const.clm_comp (hK.clm_comp contDiffOn_const)
  have hsq' : ∀ z ∈ V ∩ A, ∀ v, K' z (K' z v) = -v := by
    intro z hz v
    simp only [K', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [hsq z hz]
    simp
  obtain ⟨C₀, hC₀⟩ := exists_complexCoframe (K' p) (hsq' p ⟨hpV, hpA⟩)
  let C' := fun z => projectedComplexCoframe C₀ (K' z)
  have hC' : ContDiffOn ℝ ∞ C' V := contDiffOn_projectedComplexCoframe C₀ hK'
  let W := V ∩ C' ⁻¹' {L | L.IsInvertible}
  have hW : IsOpen W := hC'.continuousOn.isOpen_inter_preimage hV
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hpW : p ∈ W := by
    refine ⟨hpV, ?_⟩
    change (projectedComplexCoframe C₀ (K' p)).IsInvertible
    rw [projectedComplexCoframe_eq C₀ (K' p) hC₀]
    exact ⟨C₀, rfl⟩
  let L := fun z => (C' z).comp P.symm.toContinuousLinearMap
  refine ⟨W, inter_subset_left, hW, hpW, L,
    (hC'.clm_comp contDiffOn_const).mono inter_subset_left,
    (fun z hz => hz.2.comp ⟨P.symm, rfl⟩), ?_⟩
  intro z hz v
  have h := projectedComplexCoframe_intertwines C₀ (K' z)
    (hsq' z ⟨hz.1.1, hz.2⟩) (P.symm v)
  simpa only [L, C', K', ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

end FsFltz.Geometry
