import FsFltz.Analysis.TailoringFiberProjectionEstimates
import FsFltz.Geometry.PotentialFiberLiouville

/-!
# Native projected exhaustion and its tailoring error

Source: `geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1208–1220.
The projector acts on the actual potential Liouville vector. Its differential
estimate consumes the proved operator estimate for the literal tailoring
family, with norms measured in fixed logarithmic covering coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set
open scoped ContDiff Manifold

variable {n : ℕ}

/-- The potential derivative of the actual symplectically projected base
Liouville field, including a nonholomorphic complex map. -/
def potentialFiberProjectedDerivative (φ : RealSpace n → ℝ) (f : LGSpace n → ℂ)
    (y : LGSpace n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y) : ℝ :=
  (lgManifold n).scalarDerivative (fun z => φ z.1) y
    ((lgManifold n).rankTwoFiberProjection
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) f y))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) f y))
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))

/-- On the Euler end the native scalar is the actual covering-coordinate
potential derivative of the actual continuous linear projector. -/
theorem potentialFiberProjectedDerivative_eq_cover {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    {f : LGSpace n → ℂ}
    (hf : letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f) :
    potentialFiberProjectedDerivative φ f (lgCover x) hnd =
      fderiv ℝ φ x.1
        (coverFiberProjection H (fderiv ℝ (fun z => f (lgCover z)) x) (x.1, 0)).1 := by
  unfold potentialFiberProjectedDerivative
  rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ x H hH hEuler,
    ← lgCoverTangent_coverFiberProjection hφ x H hH hnd hf,
    scalarDerivative_potential_lgCover hφ]

private theorem norm_inner_hessian_le
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) {U : ℝ} (hU : 0 < U)
    (hupper : ∀ v, inner ℝ (H v) v ≤ U * ‖v‖ ^ 2)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ‖inner ℝ (H u) v‖ ≤ Real.sqrt U * Real.sqrt (inner ℝ (H u) u) * ‖v‖ := by
  have h := inner_sq_le_metric_mul_inverseMetricSq H hsymm hpos u (H v)
  rw [← hsymm u v] at h
  simp only [inverseMetricSq, H.symm_apply_apply] at h
  rw [← real_inner_comm v (H v)] at h
  have hu := hpos u
  have hv := mul_le_mul_of_nonneg_left (hupper v) hu
  rw [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hU.le, Real.sq_sqrt hu]
  nlinarith only [h, hv]

private theorem norm_fderiv_potential_cover_le {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (x : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 x.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1)
    (hpos : ∀ v, 0 ≤ inner ℝ (H v) v) {U : ℝ} (hU : 0 < U)
    (hupper : ∀ v, inner ℝ (H v) v ≤ U * ‖v‖ ^ 2)
    (v : TangentCoordinates n) :
    ‖fderiv ℝ φ x.1 v.1‖ ≤
      Real.sqrt U * Real.sqrt (metricRadialSq H x.1) *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ * ‖v‖ := by
  rw [fderiv_potential_eq_euclidean_inner hφ,
    euclidean_gradient_eq_hessian_radial hφ x H hH hEuler]
  have hs : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) := by
    intro u v
    simpa only [← hH] using
      inner_fderiv_gradient_symmetric (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
        (WithLp.toLp 2 x.1) u v
  have hv : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ * ‖v‖ := by
    exact ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm v.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _))
  exact (norm_inner_hessian_le H hs hpos hU hupper _ _).trans
    ((mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by
      dsimp [metricRadialSq]; ring))

/-- Actual projector closeness controls the native exhaustion differential
and the linear size of the projected field on the whole homogeneous end. -/
theorem tailoringFamily_exists_uniform_projected_exhaustion_error
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ x : TangentCoordinates n,
        R ≤ Real.sqrt (realSquaredNorm x.1) →
        fderiv ℝ (coordinateGradient φ) x.1 x.1 = coordinateGradient φ x.1 →
        ∀ hnd : (lgManifold n).Nondegenerate
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
        let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
        ‖potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd -
          potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x)‖ ≤
            C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 ∧
        ‖coverFiberProjection H
          (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x) (x.1, 0)‖ ≤
            C * Real.sqrt (metricRadialSq H x.1) := by
  obtain ⟨P, hP, R, hR, β₀, hβ₀, hproj⟩ :=
    tailoringFamily_exists_uniform_fiberProjection_bounds I hφ hc hU hlower hupper
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let E := ‖e.symm.toContinuousLinearMap‖
  let A := ‖logCoverRadialLift n‖ / Real.sqrt c
  let C := 1 + Real.sqrt U * E * P * A + P * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C, E]; positivity
  refine ⟨C, hC, R, hR, β₀, hβ₀, ?_⟩
  intro β hβ s hs x hx hEuler hnd
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  let L := fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) x
  let L₀ := fderiv ℝ (fun z => tailoringOriginal I β (lgCover z)) x
  let v : TangentCoordinates n := (x.1, 0)
  let r := Real.sqrt (metricRadialSq H x.1)
  have hH : ∀ w, fderiv ℝ (gradient (φ ∘ e)) (WithLp.toLp 2 x.1) w = H w := fun _ => rfl
  have hpos : ∀ w, 0 ≤ inner ℝ (H w) w := fun w =>
    (mul_nonneg hc.le (sq_nonneg _)).trans (hlower _ w)
  have hr : 0 ≤ metricRadialSq H x.1 := hpos _
  have hrad := (metricRadialSq_radius_bounds H hc hU (hlower _) (hupper _) x.1).1
  have hv : ‖v‖ ≤ A * r := by
    have hnorm : ‖v‖ ≤ ‖logCoverRadialLift n‖ * Real.sqrt (realSquaredNorm x.1) := by
      have he : Real.sqrt (realSquaredNorm x.1) =
          ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
        rw [EuclideanSpace.norm_eq]
        simp [realSquaredNorm, Real.norm_eq_abs, sq_abs]
      rw [he]
      exact (logCoverRadialLift n).le_opNorm (WithLp.toLp 2 x.1)
    have hbound : Real.sqrt (realSquaredNorm x.1) ≤ r / Real.sqrt c :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by simpa [r, mul_comm] using hrad)
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hbound (norm_nonneg _)).trans_eq (by
      dsimp [A]; ring))
  obtain ⟨hdiff, hnorm⟩ := hproj β hβ s hs x hx
  have hδ : ‖(coverFiberProjection H L - coverFiberProjection H L₀) v‖ ≤
      P * Real.exp (-Real.sqrt β) * (A * r) :=
    ((coverFiberProjection H L - coverFiberProjection H L₀).le_opNorm v).trans
      (mul_le_mul hdiff hv (norm_nonneg _) (by positivity))
  have hscalar₀ : potentialFiberProjectedDerivative φ (tailoringOriginal I β) (lgCover x) hnd =
      potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x) := by
    rw [← W_tailoringNormalizedInput]
    exact scalarDerivative_potential_W_fiberProjection hφ (tailoringNormalizedInput I β)
      x H hH hEuler hnd
  have hscalar : potentialFiberProjectedDerivative φ (tailoringFamily I β s) (lgCover x) hnd -
      potentialMetricFiberDefect H (tailoringNormalizedInput I β) (lgCover x) =
        fderiv ℝ φ x.1 ((coverFiberProjection H L - coverFiberProjection H L₀) v).1 := by
    rw [← hscalar₀, potentialFiberProjectedDerivative_eq_cover hφ x H hH hEuler hnd
      (contMDiff_tailoringFamily_lgManifold I β s),
      potentialFiberProjectedDerivative_eq_cover hφ x H hH hEuler hnd
      (contMDiff_tailoringOriginal_lgManifold I β)]
    simp only [sub_apply, Prod.fst_sub, map_sub]
    rfl
  constructor
  · rw [hscalar]
    calc
      _ ≤ Real.sqrt U * r * E *
          ‖(coverFiberProjection H L - coverFiberProjection H L₀) v‖ :=
        norm_fderiv_potential_cover_le hφ x H hH hEuler hpos hU (hupper _) _
      _ ≤ Real.sqrt U * r * E * (P * Real.exp (-Real.sqrt β) * (A * r)) := by
        gcongr
      _ = (Real.sqrt U * E * P * A) * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 := by
        rw [show metricRadialSq H x.1 = r ^ 2 from (Real.sq_sqrt hr).symm]
        ring
      _ ≤ C * Real.exp (-Real.sqrt β) * metricRadialSq H x.1 := by
        gcongr
        dsimp [C]
        have hPA : 0 ≤ P * A := mul_nonneg hP.le hA
        linarith
  · calc
      _ ≤ ‖coverFiberProjection H L‖ * ‖v‖ := (coverFiberProjection H L).le_opNorm v
      _ ≤ P * (A * r) := mul_le_mul hnorm hv (norm_nonneg _) hP.le
      _ = (P * A) * r := by ring
      _ ≤ C * r := by
        gcongr
        dsimp [C, E]
        have hprod : 0 ≤ Real.sqrt U * E * P * A := by dsimp [E]; positivity
        linarith

end FsFltz
