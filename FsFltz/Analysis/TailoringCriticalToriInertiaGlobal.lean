import FsFltz.Analysis.TailoringCriticalToriInertia

/-!
# Transfer of the face inertia to the smooth global potential

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, `eq:hessian`,
lines 1538–1571, and `lem:stable`, lines 1703–1725.
The actual global potential is smooth; the homogeneous end potential is
only used through its germ near the reconstructed branch. No smoothness
of the homogeneous potential at the origin is required.
-/

noncomputable section

namespace FsFltz

open Set Filter Function Geometry
open scoped Topology BigOperators ContDiff

variable {n : ℕ}

/-- Equality of potential germs gives equality of their literal coordinate
gradients, including when only the homogeneous potential is punctured smooth. -/
theorem coordinateGradient_eq_of_eventuallyEq {φ ψ : RealSpace n → ℝ}
    {u : RealSpace n} (heq : φ =ᶠ[𝓝 u] ψ) :
    coordinateGradient φ u = coordinateGradient ψ u := by
  ext j
  exact congrArg (fun L : RealSpace n →L[ℝ] ℝ => L (Pi.single j 1)) heq.fderiv_eq

/-- Hessians depend only on the same local potential germ. -/
theorem coordinateHessian_eq_of_eventuallyEq {φ ψ : RealSpace n → ℝ}
    {u : RealSpace n} (heq : φ =ᶠ[𝓝 u] ψ) :
    fderiv ℝ (coordinateGradient φ) u = fderiv ℝ (coordinateGradient ψ) u := by
  have hg : coordinateGradient φ =ᶠ[𝓝 u] coordinateGradient ψ := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    exact coordinateGradient_eq_of_eventuallyEq hx
  exact hg.fderiv_eq

/-- Literal agreement outside a ball supplies a local germ at every point
strictly beyond its boundary. -/
theorem potential_germ_eq_on_end {φ ψ : RealSpace n → ℝ} {R : ℝ}
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = ψ u)
    {u : RealSpace n} (hu : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖) :
    φ =ᶠ[𝓝 u] ψ := by
  filter_upwards [((EuclideanSpace.equiv (Fin n) ℝ).symm.continuousAt.norm).eventually
    (eventually_gt_nhds hu)] with x hx
  exact heq x hx.le

/-- The reconstructed radius escapes every fixed exceptional ball, as a
consequence of the actual positive branch and nonzero face minimum. -/
theorem faceCriticalRadius_eventually_outside_ball
    {s : Finset (Lattice n)} {x : (s → ℝ) → RealSpace n}
    {z : ℝ → ((s → ℝ) × ℝ)} (hx : ContinuousAt x 0) (hz : ContinuousAt z 0)
    (hxne : x 0 ≠ 0) (hq : ∀ v, 0 < (z 0).1 v) (R : ℝ) :
    ∀ᶠ β : ℝ in atTop,
      R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (faceCriticalRadius x z β)‖ := by
  have hlog : ContinuousAt (fun ε : ℝ => fun v : s => Real.log ((z ε).1 v)) 0 :=
    continuousAt_pi.mpr fun v =>
      ((continuous_apply v).continuousAt.comp hz.fst).log (hq v).ne'
  have hp : ContinuousAt (fun ε : ℝ => ε • (fun v : s => Real.log ((z ε).1 v))) 0 :=
    continuousAt_id.smul hlog
  have hparam : Tendsto (fun β : ℝ => β⁻¹ • (fun v : s => Real.log ((z β⁻¹).1 v)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_smul] using
      hp.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hxnorm : 0 < ‖e (x 0)‖ := norm_pos_iff.mpr (by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hxne)
  have hn : ∀ᶠ y in 𝓝 (0 : s → ℝ), ‖e (x 0)‖ / 2 < ‖e (x y)‖ :=
    (e.continuousAt.comp hx).norm.eventually (eventually_gt_nhds (half_lt_self hxnorm))
  filter_upwards [hparam.eventually hn, eventually_gt_atTop (R / (‖e (x 0)‖ / 2)),
    eventually_gt_atTop (0 : ℝ)] with β hxβ hβ hβpos
  rw [faceCriticalRadius, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
  have hbound : R < β * (‖e (x 0)‖ / 2) := (div_lt_iff₀ (half_pos hxnorm)).mp hβ
  exact hbound.trans (mul_lt_mul_of_pos_left hxβ hβpos)

/-- The same actual branch eventually lies in the agreement germ between
the smooth global potential and its homogeneous end. -/
theorem faceCriticalRadius_eventually_potential_germ_eq
    {s : Finset (Lattice n)} {x : (s → ℝ) → RealSpace n}
    {z : ℝ → ((s → ℝ) × ℝ)} (hx : ContinuousAt x 0) (hz : ContinuousAt z 0)
    (hxne : x 0 ≠ 0) (hq : ∀ v, 0 < (z 0).1 v)
    {φ ψ : RealSpace n → ℝ} {R : ℝ}
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = ψ u) :
    ∀ᶠ β : ℝ in atTop, φ =ᶠ[𝓝 (faceCriticalRadius x z β)] ψ :=
  (faceCriticalRadius_eventually_outside_ball hx hz hxne hq R).mono fun _ hu =>
    potential_germ_eq_on_end heq hu

/-- The two face-weight representations agree literally. -/
theorem criticalFaceGram_eq_faceWeightSquare {s : Finset (Lattice n)}
    (q : s → ℝ) (X : RealSpace n) :
    criticalFaceGram s (faceCoordinateExtend s q) X = faceWeightSquare q (faceLevelMap s X) := by
  classical
  rw [criticalFaceGram, faceWeightSquare]
  simpa only [faceCoordinateExtend_apply, faceLevelMap_apply] using
    (Finset.sum_coe_sort s (fun v => faceCoordinateExtend s q v * pairing v X ^ 2)).symm

/-- Every smooth local full-face parametrization has the actual homogeneous
end Hessian computed in the inertia theorem, while its potential is the
smooth global extension. Only equality of the local germs is needed. -/
theorem criticalFace_parametrization_hessian_of_potential_germ {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ ψ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : Finset (Lattice n)) (β lam : ℝ) (q : s → ℝ)
    {g : F → TangentCoordinates n} (hg : ContDiff ℝ ∞ g) (a V : F)
    (hlevel : ∀ᶠ w in 𝓝 a, criticalFaceFunction s β (g w) = 1)
    (heq : φ =ᶠ[𝓝 (g a).1] ψ)
    (hmon : ∀ v : s,
      monomial (Real.exp (-β) : ℂ) v.val ((g a).1, angleQuotient (g a).2) = (q v : ℂ))
    (hcritical : coordinateGradient ψ (g a).1 = lam • faceNormalMap s q) :
    fderiv ℝ (fun w => φ (g w).1) a = 0 ∧
      fderiv ℝ (fderiv ℝ (fun w => φ (g w).1)) a V V =
        faceConstrainedHessian s (fderiv ℝ (coordinateGradient ψ) (g a).1) q lam
          (fderiv ℝ g a V) := by
  have hreal : ∀ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).im = 0 := by
    intro v hv
    rw [hmon ⟨v, hv⟩]
    rfl
  have hweights : (fun v => (monomial (Real.exp (-β) : ℂ) v
      ((g a).1, angleQuotient (g a).2)).re) =ᶠ[Filter.principal (s : Set (Lattice n))]
      faceCoordinateExtend s q := by
    rw [Filter.eventuallyEq_principal]
    intro v hv
    dsimp only
    rw [hmon ⟨v, hv⟩]
    simpa only [Complex.ofReal_re] using (faceCoordinateExtend_apply s q ⟨v, hv⟩).symm
  have hnormal : coordinateGradient φ (g a).1 = lam • ∑ v ∈ s,
      (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re • latticeReal v := by
    rw [coordinateGradient_eq_of_eventuallyEq heq, hcritical, faceNormalMap_eq_extended_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    exact (Filter.eventuallyEq_principal.mp hweights) hv |>.symm
  obtain ⟨hfirst, hsecond⟩ := criticalFace_parametrization_hessian hφ s β lam hg a V
    hlevel hreal hnormal
  refine ⟨hfirst, ?_⟩
  rw [hsecond, second_fderiv_eq_coordinate_hessian (hφ.differentiable (by simp)) hφ.contDiffAt,
    coordinateHessian_eq_of_eventuallyEq heq]
  have hgram (X : RealSpace n) : criticalFaceGram s
      (fun v => (monomial (Real.exp (-β) : ℂ) v ((g a).1, angleQuotient (g a).2)).re) X =
        faceWeightSquare q (faceLevelMap s X) := by
    rw [← criticalFaceGram_eq_faceWeightSquare]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(Filter.eventuallyEq_principal.mp hweights) hv]
  rw [hgram, hgram]
  rfl

end FsFltz
