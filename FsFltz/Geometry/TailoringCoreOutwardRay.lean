import FsFltz.Geometry.TailoringConormalNative

/-!
# The entire outward continuation of the actual conormal section

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1580–1617,
especially the whole outward continuation and radial positivity at
lines 1592–1593 and 1608–1613. The derivative below is first taken along
the literal scalar ray, then identified with the actual ambient Liouville
derivative of the same smooth potential on its homogeneous end.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology ContDiff Manifold

variable {n : ℕ}

/-- Every outward scalar continuation of an actual section point stays in
the literal Legendre conic set. The actual endpoint is real positive and
has positive radial derivative, both at the continued point and at the
original ray parameter. -/
theorem IsStronglyCompatibleEndPotential.eventually_coreSection_outward_ray
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd) :
    ∀ᶠ β in atTop, ∀ y ∈ tailoringCoreSection I φEnd β, ∀ t : ℝ, 1 ≤ t →
      (t • y.1, y.2) ∈ tailoringLegendreConic I φEnd ∧
      tailoringFamily I β 1 (t • y.1, y.2) =
        (tailoringRadialFunction I β (t • y.1) : ℂ) ∧
      0 < (tailoringFamily I β 1 (t • y.1, y.2)).re ∧
      ∃ d : ℝ, 0 < d ∧
        HasDerivAt (fun r : ℝ => tailoringFamily I β 1 (r • (t • y.1), y.2)) (d : ℂ) 1 ∧
        HasDerivAt (fun r : ℝ => tailoringFamily I β 1 (r • y.1, y.2)) ((d / t : ℝ) : ℂ) t := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hlog : Real.log (I.vertices.card : ℝ) < Real.log (2 * (I.vertices.card : ℝ)) :=
    Real.log_lt_log hN (by linarith)
  filter_upwards [hEnd.eventually_coreSection_eq_radial,
    hEnd.eventually_cone_family_eq_radial, hEnd.eventually_cone_ray_derivative_positive,
    eventually_ge_atTop (Real.log (I.vertices.card : ℝ) + 1)] with β heq hreal hderiv hlarge
  intro y hy t ht
  have hyreal : tailoringRadialFunction I β y.1 = 1 := by
    rw [heq] at hy
    exact hy.2
  have hheight := (tailoringRadialFunction_height_bounds I β hyreal).1
  have hheightpos : 0 < supportHeight I y.1 := by linarith
  have hu : y.1 ≠ 0 := by
    intro hu
    rw [hu, I.supportHeight_zero] at hheightpos
    exact lt_irrefl 0 hheightpos
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rcases hy.1 with ⟨hpne, σ, hσ, hσne, hp, hθ⟩
  have hgrad : coordinateGradient φEnd (t • y.1) = t • coordinateGradient φEnd y.1 :=
    coordinateGradient_smul_of_homogeneous_two hEnd.homogeneous
      (fun u hu => (hEnd.smooth u hu).differentiableAt (by simp)) hu htpos
  have hpt : coordinateGradient φEnd (t • y.1) ∈ σ := by
    rw [hgrad]
    exact I.smul_mem_of_mem_faceFan hσ hp htpos.le
  have hh : β - Real.log (2 * (I.vertices.card : ℝ)) < supportHeight I (t • y.1) := by
    rw [I.supportHeight_smul_of_nonneg htpos.le]
    have hhmono : supportHeight I y.1 ≤ t * supportHeight I y.1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hheightpos.le
    linarith
  have htune : t • y.1 ≠ 0 := smul_ne_zero htpos.ne' hu
  obtain ⟨d, hd, hvalue, hD⟩ := hderiv σ hσ (t • y.1, y.2) htune hpt hθ hh
  refine ⟨⟨?_, σ, hσ, hσne, hpt, hθ⟩, hreal σ hσ _ hpt hθ hh.le,
    hvalue, d, hd, hD, ?_⟩
  · rw [hgrad]
    exact smul_ne_zero htpos.ne' hpne
  · have hD' : HasDerivAt
        (fun r : ℝ => tailoringFamily I β 1 (r • (t • y.1), y.2)) (d : ℂ) (t / t) := by
      simpa only [div_self htpos.ne'] using hD
    have hline : HasDerivAt (fun r : ℝ => r / t) (1 / t) t := by
      simpa only [id_eq] using (hasDerivAt_id t).div_const t
    have hcomp := hD'.scomp t (h := fun r : ℝ => r / t) hline
    convert hcomp using 1
    · ext r
      change tailoringFamily I β 1 (r • y.1, y.2) =
        tailoringFamily I β 1 ((r / t) • (t • y.1), y.2)
      rw [smul_smul, div_mul_cancel₀ r htpos.ne']
    · simp [div_eq_mul_inv, mul_comm, Complex.real_smul]

/-- The entire outward continuation has positive derivative under the
literal ambient Liouville field of the same smooth end-extension potential.
Neither an Euler identity nor a radial field formula is supplied as input. -/
theorem tailoringEndpoint_exists_uniform_coreSection_outward_ambient_liouville
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ y ∈ tailoringCoreSection I φEnd β,
      ∀ t : ℝ, 1 ≤ t → ∃ d : ℝ, 0 < d ∧
        complexDifferential (lgManifold n) (tailoringFamily I β 1) (t • y.1, y.2)
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (t • y.1, y.2)) = (d : ℂ) := by
  obtain ⟨Br, hray⟩ := eventually_atTop.mp hEnd.eventually_coreSection_outward_ray
  obtain ⟨BR, hBR, hescape⟩ := tailoringFamily_exists_fiber_outside_radius I (R + 1)
  refine ⟨max BR Br, hBR.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  obtain ⟨_, _, _, d, hd, hD, _⟩ := hray β ((le_max_right _ _).trans hβ) y hy t ht
  obtain ⟨x, hx⟩ := lgCover_surjective n (t • y.1, y.2)
  have hx1 : x.1 = t • y.1 := congrArg Prod.fst hx
  have hx2 : angleQuotient x.2 = y.2 := congrArg Prod.snd hx
  have horigin : R + 1 ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ := by
    have h := hescape β ((le_max_left _ _).trans hβ) 1 (by simp) y hy.2
    rwa [realEuclideanRadius_eq_norm] at h
  have hradius : R < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x.1‖ := by
    rw [hx1, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hmono : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ ≤
        t * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y.1‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end
    hφ hEnd.smooth hEnd.homogeneous hR heq hradius
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
  have hZ : (lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x) =
      lgCoverTangent x (x.1, 0) :=
    (lgManifold n).liouvilleVector_eq _ _ hnd
      (liouvilleEquation_lambdaPotentialForm_radial hφ x hEuler)
  have hline : HasDerivAt (fun r : ℝ => (r • x.1, x.2)) (x.1, 0) 1 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (1 : ℝ)).smul_const x.1).prodMk (hasDerivAt_const (1 : ℝ) x.2)
  have hcover : HasFDerivAt (fun z => tailoringFamily I β 1 (lgCover z))
      (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x) ((1 : ℝ) • x.1, x.2) := by
    simpa only [one_smul, Prod.eta] using
      ((contDiff_tailoringFamily_cover I β 1).differentiable (by simp) x).hasFDerivAt
  have hcurve := hcover.comp_hasDerivAt 1 hline
  have hmaps : (fun r : ℝ => tailoringFamily I β 1 (lgCover (r • x.1, x.2))) =
      (fun r : ℝ => tailoringFamily I β 1 (r • (t • y.1), y.2)) := by
    ext r
    congr 1
    exact Prod.ext (congrArg (fun u => r • u) hx1) hx2
  change HasDerivAt (fun r : ℝ => tailoringFamily I β 1 (lgCover (r • x.1, x.2)))
    (fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x (x.1, 0)) 1 at hcurve
  rw [hmaps] at hcurve
  refine ⟨d, hd, ?_⟩
  rw [← hx, hZ]
  change ((complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)).comp
    (lgCoverTangent x)) (x.1, 0) = (d : ℂ)
  rw [← fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)]
  exact hcurve.unique hD

end FsFltz
