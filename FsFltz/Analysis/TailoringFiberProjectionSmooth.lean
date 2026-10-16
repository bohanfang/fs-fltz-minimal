import FsFltz.Analysis.TailoringFiberProjection

/-!
# Smoothness of the actual logarithmic symplectic projection

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1208–1220,
and `lem:invariance`, lines 1637–1658. The inverse Hessian and actual
differential determine a smooth projected field on the nonzero-pairing locus.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace FsFltz

open Geometry

theorem contDiff_potentialHessianEquiv_symm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ : E → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ x v : E, c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient φ) x v) v) :
    ContDiff ℝ ∞ (fun x => (potentialHessianEquiv hc hlower x).symm.toContinuousLinearMap) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hD := (contDiff_gradient hφ).fderiv_right (m := ∞) (by simp)
  have hi : (fderiv ℝ (gradient φ) x).IsInvertible :=
    ⟨potentialHessianEquiv hc hlower x, rfl⟩
  have hs := hi.contDiffAt_map_inverse.comp x hD.contDiffAt
  apply hs.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y =>
    (ContinuousLinearMap.inverse_equiv (potentialHessianEquiv hc hlower y)).symm)

variable {n : ℕ}

theorem contDiffAt_coverCovectorVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E → TangentCoordinates n →L[ℝ] ℝ} {x : E}
    (hp : ContDiffAt ℝ ∞ p x)
    (e : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentCoordinates n) :
    ContDiffAt ℝ ∞ (fun y => coverCovectorVector (p y) e) x := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.contDiffAt.comp x
    (hp.clm_comp contDiffAt_const)

theorem contDiffAt_coverHamiltonianVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {p : E → TangentCoordinates n →L[ℝ] ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ (fun y => (H y).symm.toContinuousLinearMap) x)
    (hp : ContDiffAt ℝ ∞ p x) :
    ContDiffAt ℝ ∞ (fun y => coverHamiltonianVector (H y) (p y)) x := by
  exact ((logCoverRadialLift n).contDiff.contDiffAt.comp x
    (hH.clm_apply (contDiffAt_coverCovectorVector hp (logCoverAngularLift n)))).sub
      ((logCoverAngularLift n).contDiff.contDiffAt.comp x
        (hH.clm_apply (contDiffAt_coverCovectorVector hp (logCoverRadialLift n))))

theorem contDiffAt_coverPlanePairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {L : E → TangentCoordinates n →L[ℝ] ℂ} {x : E}
    (hH : ContDiffAt ℝ ∞ (fun y => (H y).symm.toContinuousLinearMap) x)
    (hL : ContDiffAt ℝ ∞ L x) :
    ContDiffAt ℝ ∞ (fun y => coverPlanePairing (H y) (L y)) x := by
  have hp : ContDiffAt ℝ ∞ (fun y => Complex.reCLM.comp (L y)) x :=
    contDiffAt_const.clm_comp hL
  have hq : ContDiffAt ℝ ∞ (fun y => Complex.imCLM.comp (L y)) x :=
    contDiffAt_const.clm_comp hL
  exact ((hH.clm_apply (contDiffAt_coverCovectorVector hq (logCoverAngularLift n))).inner ℝ
    (contDiffAt_coverCovectorVector hp (logCoverRadialLift n))).sub
      ((hH.clm_apply (contDiffAt_coverCovectorVector hq (logCoverRadialLift n))).inner ℝ
        (contDiffAt_coverCovectorVector hp (logCoverAngularLift n)))

theorem contDiffAt_coverFiberProjection_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {L : E → TangentCoordinates n →L[ℝ] ℂ} {v : E → TangentCoordinates n} {x : E}
    (hH : ContDiffAt ℝ ∞ (fun y => (H y).symm.toContinuousLinearMap) x)
    (hL : ContDiffAt ℝ ∞ L x) (hv : ContDiffAt ℝ ∞ v x)
    (hπ : coverPlanePairing (H x) (L x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => coverFiberProjection (H y) (L y) (v y)) x := by
  simp_rw [coverFiberProjection_apply]
  have hp : ContDiffAt ℝ ∞ (fun y => Complex.reCLM.comp (L y)) x :=
    contDiffAt_const.clm_comp hL
  have hq : ContDiffAt ℝ ∞ (fun y => Complex.imCLM.comp (L y)) x :=
    contDiffAt_const.clm_comp hL
  have hπs := contDiffAt_coverPlanePairing H hH hL
  exact (hv.add (((hq.clm_apply hv).div hπs hπ).smul
    (contDiffAt_coverHamiltonianVector H hH hp))).sub
      (((hp.clm_apply hv).div hπs hπ).smul (contDiffAt_coverHamiltonianVector H hH hq))

/-- The real ambient cover field used by the local ODE argument is smooth
near every point of nonzero actual Poisson pairing. -/
theorem contDiffAt_potential_coverProjectedRadial
    {φ : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {f : TangentCoordinates n → ℂ} (hf : ContDiff ℝ ∞ f)
    {x : TangentCoordinates n}
    (hπ : coverPlanePairing (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1))
      (fderiv ℝ f x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : TangentCoordinates n =>
      coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1))
        (fderiv ℝ f y) (y.1, 0)) x := by
  apply contDiffAt_coverFiberProjection_apply
  · exact (contDiff_potentialHessianEquiv_symm
      (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) hc hlower).contDiffAt.comp x
        ((EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt.comp x contDiffAt_fst)
  · exact (hf.fderiv_right (m := ∞) (by simp)).contDiffAt
  · exact contDiffAt_fst.prodMk contDiffAt_const
  · exact hπ

/-- The existing uniform Poisson estimate discharges local smoothness on
every actual full fiber of norm at least one, throughout the tailoring path. -/
theorem tailoringFamily_exists_uniform_coverProjectedRadial_smooth
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ x : TangentCoordinates n, 1 ≤ ‖tailoringFamily I β s (lgCover x)‖ →
      ContDiffAt ℝ ∞ (fun y : TangentCoordinates n =>
        coverFiberProjection (potentialHessianEquiv hc hlower (WithLp.toLp 2 y.1))
          (fderiv ℝ (fun z => tailoringFamily I β s (lgCover z)) y) (y.1, 0)) x := by
  obtain ⟨_, _, _, _, B, hB, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨B, hB, ?_⟩
  intro β hβ s hs x hx
  apply contDiffAt_potential_coverProjectedRadial hφ hc hlower (contDiff_tailoringFamily_cover I β s)
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  have hp := ((hπ β hβ s hs (lgCover x) hnd).2.2 hx).ne'
  rw [planePairing_lambdaPotentialForm_eq_cover hφ x
    (potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)) (fun _ => rfl) hnd
      (contMDiff_tailoringFamily_lgManifold I β s)] at hp
  exact hp

end FsFltz
