import FsFltz.Geometry.TailoringCriticalNormalData
import FsFltz.Geometry.TailoringTransverseMetric

/-!
# Same critical data for the whole torus and its fixed transverse metric

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1538–1570,
and `lem:stable`, lines 1718–1724. One constructed critical datum supplies
the defining neighborhood, actual native charts and one fixed metric-normal
lift. That lift is chosen before all torus angles and chart centers.
No product normal tube or nonlinear neighborhood expansion is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ} {s : Finset (Lattice n)}

/-- Unnormalized monomial weights on the same reconstructed critical torus. -/
def criticalFaceTransverseWeights (β : ℝ) (q : s → ℝ) : s → ℝ :=
  fun v => Real.exp β * q v

namespace CriticalFaceNormalData

variable {I : ToricInput n} {φEnd φ : RealSpace n → ℝ} {β : ℝ}
  {u : RealSpace n} {q : s → ℝ} {lam : ℝ}
  {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}

theorem transverseWeights_pos (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (v : s) : 0 < criticalFaceTransverseWeights β q v :=
  mul_pos (Real.exp_pos _) (D.weight_pos v)

theorem transverseWeights_monomial (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (θ : Torus n) (hθ : θ ∈ coneTorus (positiveCone s)) (v : s) :
    monomial 1 v.val (u, θ) = (criticalFaceTransverseWeights β q v : ℂ) := by
  have he : (Real.exp β : ℂ) * (Real.exp (-β) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one]
  have hm : monomial 1 v.val (u, θ) =
      (Real.exp β : ℂ) * monomial (Real.exp (-β) : ℂ) v.val (u, θ) := by
    simp only [monomial, one_mul, ← mul_assoc, he]
  rw [hm, D.monomial_eq θ hθ v, ← Complex.ofReal_mul]
  rfl

theorem faceLevel_surjective (D : CriticalFaceNormalData I φEnd φ β s u q lam B R) :
    Surjective (faceLevelMap s) := by
  intro y
  refine ⟨B y, ?_⟩
  exact congrArg (fun A : (s → ℝ) →L[ℝ] (s → ℝ) => A y) D.right_inverse

/-- One actual datum and one of its defining neighborhoods produce a fixed
metric before all torus angles. Every chart is constructed from that same
datum, and its actual transverse rate has the positive derivative. -/
theorem exists_same_data_fixed_transverse_linearization
    (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (hStrong : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hs : IsPolytopeFace I.vertices s) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1}) (v₀ : s) :
    let H := fderiv ℝ (coordinateGradient φEnd) u
    let r := criticalFaceTransverseWeights β q
    ∃ W : ConormalTransverseNeighborhoodAt I φEnd β s u v₀,
    ∃ L : (W.projection.ker × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q,
      (faceFiberTransverseDifferential W.quotient H v₀ q r).comp L =
        ContinuousLinearMap.id ℝ (W.projection.ker × (s.erase v₀.val → ℝ)) ∧
      (∀ z V, faceFiberTransverseDifferential W.quotient H v₀ q r V = 0 →
        faceFiberMetric H q (L z) V = 0) ∧
      (∀ z w, fixedFaceTransverseMetric H q v₀ L z w =
        fixedFaceTransverseMetric H q v₀ L w z) ∧
      (∀ z, z ≠ 0 → 0 < fixedFaceTransverseMetric H q v₀ L z z) ∧
      ∀ θ ∈ coneTorus (positiveCone s),
        (∃ a : N.Point, j.map a = (u, θ)) ∧
        ∀ (a : N.Point) (ξ : TangentCoordinates n), j.map a = lgCover ξ →
          lgCover ξ = (u, θ) →
          ∃ C : NativeFaceHessianChart φ s H q lam N j a ξ,
            C.coordinateField (chartAt (Model (2 * n - 2)) a a) = 0 ∧
            C.coordinateTransverseRate (coordinateGradient φEnd) W.quotient v₀
              (chartAt (Model (2 * n - 2)) a a) = 0 ∧
            C.transverseLinearization (coordinateGradient φEnd) W.quotient v₀ L =
              (fderiv ℝ (C.coordinateTransverseRate (coordinateGradient φEnd) W.quotient v₀)
                (chartAt (Model (2 * n - 2)) a a)).comp (C.transverseNormalLift v₀ L) ∧
            (∀ z w, fixedFaceTransverseMetric H q v₀ L
              (C.transverseLinearization (coordinateGradient φEnd) W.quotient v₀ L z) w =
                faceConstrainedPairing s H q lam (L z) (L w)) ∧
            (∀ z w, fixedFaceTransverseMetric H q v₀ L
              (C.transverseLinearization (coordinateGradient φEnd) W.quotient v₀ L z) w =
                fixedFaceTransverseMetric H q v₀ L z
                  (C.transverseLinearization (coordinateGradient φEnd) W.quotient v₀ L w)) ∧
            (∀ z, z ≠ 0 → 0 < fixedFaceTransverseMetric H q v₀ L
              (C.transverseLinearization (coordinateGradient φEnd) W.quotient v₀ L z) z) := by
  classical
  let H := fderiv ℝ (coordinateGradient φEnd) u
  let r := criticalFaceTransverseWeights β q
  obtain ⟨W⟩ := D.conormal_neighborhood v₀
  obtain ⟨L, hL, horth⟩ := exists_fixed_faceTransverse_normalLift W.quotient
    W.quotient_surjective H D.hessian_surjective D.hessian_symm D.hessian_pos
    v₀ q r D.weight_pos D.transverseWeights_pos W.quotient_zero D.faceLevel_surjective
    B R D.right_inverse D.hessian_normal
  refine ⟨W, L, hL, horth, fixedFaceTransverseMetric_symm H q v₀ L D.hessian_symm,
    fixedFaceTransverseMetric_pos H q v₀ L W.quotient r hL D.hessian_pos, ?_⟩
  intro θ hθ
  refine ⟨?_, ?_⟩
  · have hmem : (u, θ) ∈ range j.map := by
      rw [himage]
      exact D.fiber_eq θ hθ
    exact hmem
  intro a ξ hpoint hξ
  obtain ⟨C⟩ := D.nativeChart hs hφ hc hlower hpi θ hθ N j himage a ξ hpoint hξ
  have hrad : ξ.1 = u := congrArg Prod.fst hξ
  have hΦ : ContDiffAt ℝ ∞ (coordinateGradient φEnd) ξ.1 :=
    hrad.symm ▸ D.gradient_smooth hStrong hEnd1
  have hHΦ : H = fderiv ℝ (coordinateGradient φEnd) ξ.1 := by rw [hrad]
  have hHφ : H = fderiv ℝ (coordinateGradient φ) ξ.1 := by
    rw [hrad]
    exact D.hessian_eq_global
  have hgood : ∀ᶠ p in 𝓝 (lgCover ξ), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1 :=
    hξ.symm ▸ D.good_germ θ
  have hmon : ∀ v : s, monomial 1 v.val (lgCover ξ) = (r v : ℂ) := by
    rw [hξ]
    exact D.transverseWeights_monomial θ hθ
  have hz := C.coordinateField_zero I β hφ hc hlower hpi himage hgood
  have hrzero : C.coordinateTransverseRate (coordinateGradient φEnd) W.quotient v₀
      (chartAt (Model (2 * n - 2)) a a) = 0 := by
    unfold NativeFaceHessianChart.coordinateTransverseRate
    rw [hz, map_zero]
  exact ⟨C, hz, hrzero,
    C.transverseLinearization_eq_rate_derivative I β hφ hc hlower hpi himage hgood
      W.quotient v₀ hΦ L,
    C.transverseLinearization_metric_eq_faceConstrainedPairing I β hφ hc hlower hpi himage
      hgood W.quotient v₀ hΦ hHΦ hHφ D.hessian_symm r hmon L hL horth,
    C.fixed_transverse_linearization_selfadjoint I β hφ hc hlower hpi himage hgood
      W.quotient v₀ hΦ hHΦ hHφ D.hessian_symm r hmon L hL horth,
    C.fixed_transverse_linearization_pos I β hφ hc hlower hpi himage hgood
      W.quotient W.quotient_zero v₀ hΦ hHΦ hHφ D.hessian_symm D.hessian_pos r hmon
      D.weight_pos D.transverseWeights_pos D.multiplier_pos D.right_inverse D.hessian_normal
      L hL horth⟩

end CriticalFaceNormalData

end FsFltz
