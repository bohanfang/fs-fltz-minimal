import FsFltz.Geometry.ProperExhaustionCompleteFlow
import FsFltz.Analysis.OriginalRoundedBoundary
import FsFltz.Compactness

/-!
# Completeness on closed logarithmic submanifolds

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1221–1237.
A native field with linear logarithmic growth on the whole end is complete.
The closed embedding makes the actual restricted quadratic exhaustion proper.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- The native quadratic differential is bounded by the logarithmic radius
and the coordinate tangent norm, with the fixed norm conversion explicit. -/
theorem abs_dPhi0_le_radius_mul_norm {n : ℕ} (z v : TangentCoordinates n) :
    |dPhi0 (lgCover z) v| ≤ Real.sqrt (realSquaredNorm z.1) *
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ * ‖v‖ := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have he : dPhi0 (lgCover z) v = inner ℝ (e z.1) (e v.1) := by
    simp [dPhi0, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, lgCover, mul_comm, e]
  have hr : Real.sqrt (realSquaredNorm z.1) = ‖e z.1‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [realSquaredNorm, Real.norm_eq_abs, e]
  rw [he, hr]
  calc
    _ ≤ ‖e z.1‖ * ‖e v.1‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖e z.1‖ * (‖e.toContinuousLinearMap‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        ((e.toContinuousLinearMap.le_opNorm v.1).trans
          (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- Linear growth of the actual pushed-forward field on a closed embedded
submanifold constructs its all-real smooth flow. The compact remainder is
controlled by smoothness, without an assumed flow or continuation rule. -/
theorem exists_completeFlow_of_closedEmbedding_logarithmic_growth
    {n d : ℕ} (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
    (hclosed : IsClosed (range j.map)) (Z : (x : N.Point) → N.Tangent x) (hZ : N.IsSmoothVectorField Z)
    {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hgrowth : ∀ (x : N.Point) (z : TangentCoordinates n), j.map x = lgCover z →
      R ≤ Real.sqrt (realSquaredNorm z.1) → ∃ v : TangentCoordinates n,
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x (Z x) = lgCoverTangent z v ∧
          ‖v‖ ≤ C * Real.sqrt (realSquaredNorm z.1)) :
    Nonempty (CompleteLiouvilleFlow N Z) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let ρ : N.Point → ℝ := phi0 ∘ j.map
  have hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ :=
    contMDiff_original_phi0.comp j.map.contMDiff
  have hρnonneg : ∀ x, 0 ≤ ρ x := fun x =>
    div_nonneg (realSquaredNorm_nonneg (j.map x).1) (by norm_num)
  have hj : Topology.IsClosedEmbedding j.map := ⟨j.embedding, hclosed⟩
  have hproper : ∀ A : ℝ, 0 ≤ A → IsCompact {x : N.Point | ρ x ≤ A} :=
    fun A hA => hj.isCompact_preimage (isCompact_phi0_sublevel A hA)
  obtain ⟨B, hB⟩ := (hproper (R ^ 2 / 2) (by positivity)).exists_bound_of_continuousOn
    (N.continuous_scalarDerivative_vectorField hZ ρ hρ).continuousOn
  let k := ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖
  let D := max B (2 * k * C + 1)
  have hk : 0 ≤ k := norm_nonneg _
  have hD : 0 < D := (by positivity : 0 < 2 * k * C + 1).trans_le (le_max_right _ _)
  apply N.exists_completeFlow_of_proper_exhaustion Z hZ ρ hρ hρnonneg hproper hD
  intro x
  obtain ⟨z, hz⟩ := lgCover_surjective n (j.map x)
  by_cases hout : R ≤ Real.sqrt (realSquaredNorm z.1)
  · obtain ⟨v, hv, hvg⟩ := hgrowth x z hz.symm hout
    have hchain := mfderiv_comp_apply x
      (contMDiff_original_phi0.mdifferentiable (by simp) (j.map x))
      (j.map.contMDiff.mdifferentiable (by simp) x) (Z x)
    change N.scalarDerivative ρ x (Z x) =
      differentialCovector (lgManifold n) phi0 (j.map x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x (Z x)) at hchain
    rw [hchain, hv, ← hz, differentialCovector_phi0_lgCover]
    have hbound := (abs_dPhi0_le_radius_mul_norm z v).trans
      (mul_le_mul_of_nonneg_left hvg (mul_nonneg (Real.sqrt_nonneg _) hk))
    have hs := Real.sq_sqrt (realSquaredNorm_nonneg z.1)
    have hrho : 2 * ρ x = realSquaredNorm z.1 := by
      dsimp [ρ, phi0, Function.comp_def]
      rw [← hz]
      simp [lgCover]
      ring
    have hDC : 2 * k * C ≤ D := by dsimp [D]; linarith [le_max_right B (2 * k * C + 1)]
    nlinarith [hρnonneg x, mul_nonneg (sub_nonneg.mpr hDC) (hρnonneg x)]
  · have hx : ρ x ≤ R ^ 2 / 2 := by
      have hr := (lt_of_not_ge hout).le
      have hs := Real.sq_sqrt (realSquaredNorm_nonneg z.1)
      have hsle := (sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hr
      dsimp [ρ, phi0, Function.comp_def]
      rw [← hz]
      change realSquaredNorm z.1 / 2 ≤ R ^ 2 / 2
      nlinarith
    have hb : |N.scalarDerivative ρ x (Z x)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x hx
    exact hb.trans ((show B ≤ D from le_max_left _ _).trans
      (show D ≤ D * (1 + ρ x) from le_mul_of_one_le_right hD.le (by linarith [hρnonneg x])))

end FsFltz.Geometry
