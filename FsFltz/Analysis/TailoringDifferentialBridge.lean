import FsFltz.Analysis.TailoringEstimates
import FsFltz.Geometry.LocalCovers

/-!
# The tailoring estimate on the actual quotient differential

Source: `geometric-part-fsf-proof.tex`, `eq:C1`, lines 1107–1114;
`geoemtric-part-fsf.tex`, `sec:lean`, lines 778–814.
The differential in the analytic estimate is identified with the native
quotient differential pulled back by the actual quotient-cover tangent map.
-/

noncomputable section

namespace FsFltz

open Geometry
open scoped Manifold ContDiff

variable {n : ℕ}

theorem contMDiff_tailoringFamily_lgManifold (I : ToricInput n) (β s : ℝ) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (tailoringFamily I β s : LGSpace n → ℂ) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hp : ContMDiff 𝓘(ℝ, Geometry.Model (2 * n))
      (𝓘(ℝ, ℝ).prod (lgModel n)) ∞ (fun y : LGSpace n => (s, y)) :=
    contMDiff_const.prodMk
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  simpa only [Function.comp_def] using (contMDiff_tailoringFamily I β).comp hp

theorem contMDiff_tailoringOriginal_lgManifold (I : ToricInput n) (β : ℝ) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (tailoringOriginal I β : LGSpace n → ℂ) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  convert contMDiff_tailoringFamily_lgManifold I β 0 using 1
  exact (funext (tailoringFamily_zero I β)).symm

/-- The analytic differential equals the actual native quotient differential
pulled back through the actual derivative of the logarithmic cover. -/
theorem fderiv_tailoringFamily_error_lgCover (I : ToricInput n) (β s : ℝ)
    (x : TangentCoordinates n) :
    fderiv ℝ (fun z : TangentCoordinates n =>
      tailoringFamily I β s (lgCover z) - tailoringOriginal I β (lgCover z)) x =
      (complexDifferential (lgManifold n)
        (fun y => tailoringFamily I β s y - tailoringOriginal I β y) (lgCover x)).comp
        (lgCoverTangent x) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hf := (contMDiff_tailoringFamily_lgManifold I β s).sub
    (contMDiff_tailoringOriginal_lgManifold I β)
  have h := mfderiv_comp x (hf.mdifferentiable (by simp) (lgCover x))
    ((contMDiff_lgCover n).mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv] at h
  exact h

/-- The source's C¹ estimate controls the actual quotient differential in
the coordinates furnished by the logarithmic cover. -/
theorem tailoringFamily_exists_uniform_native_C1_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ x : TangentCoordinates n,
        ‖tailoringFamily I β s (lgCover x) - tailoringOriginal I β (lgCover x)‖ +
          ‖(complexDifferential (lgManifold n)
            (fun y => tailoringFamily I β s y - tailoringOriginal I β y) (lgCover x)).comp
              (lgCoverTangent x)‖ ≤
          C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I x.1 - β) := by
  obtain ⟨C, hC, hb⟩ := tailoringFamily_exists_uniform_C1_bound I
  refine ⟨C, hC, fun β s hs x => ?_⟩
  rw [← fderiv_tailoringFamily_error_lgCover]
  exact hb β s hs x

/-- The zeroth-order estimate holds at every point of the literal quotient. -/
theorem tailoringFamily_exists_uniform_C0_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, ‖tailoringFamily I β s y - tailoringOriginal I β y‖ ≤
        C * Real.exp (-Real.sqrt β) * Real.exp (supportHeight I y.1 - β) := by
  obtain ⟨C, hC, hb⟩ := tailoringFamily_exists_uniform_C1_bound I
  refine ⟨C, hC, fun β s hs y => ?_⟩
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hb β s hs x)

end FsFltz
