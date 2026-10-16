import FsFltz.Analysis.TailoringCriticalConormal
import FsFltz.Analysis.TailoringFiberProjection

/-!
# The conormal consequence of actual tailored critical conditions

Source: `geometric-part-fsf-proof.tex`, `sec:critical`, lines 1354–1365,
and `lem:localcritical`, lines 1428–1454. The native scalar derivative and
the zero of the native symplectic fiber projection are converted to actual
radial/angular covector annihilation. No localization or core result is
assumed in these pointwise critical hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- The total real derivative is the pairing with its literal coefficients
in the fixed coordinate basis, including nondifferentiable points. -/
theorem fderiv_eq_coordinateGradient_pairing (φ : RealSpace n → ℝ)
    (u v : RealSpace n) :
    fderiv ℝ φ u v = ∑ j, coordinateGradient φ u j * v j := by
  classical
  have hv : v = ∑ j : Fin n, v j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, coordinateGradient, smul_eq_mul, mul_comm]

/-- Zero of the native symplectic projection of the ambient Liouville
field implies annihilation of the primitive on the actual fiber kernel. -/
theorem lambdaPotentialForm_annihilates_kernel_of_projected_zero
    (φ : RealSpace n → ℝ) (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y)
    (hzero : (lgManifold n).rankTwoFiberProjection
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) = 0)
    (v : (lgManifold n).Tangent y)
    (hv : complexDifferential (lgManifold n) (tailoringFamily I β 1) y v = 0) :
    evalOne (lambdaPotentialForm φ) y v = 0 := by
  have hp : (Complex.reCLM.comp
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) y)) v = 0 := by
    simp [hv]
  have hq : (Complex.imCLM.comp
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) y)) v = 0 := by
    simp [hv]
  have h := (lgManifold n).rankTwoFiberProjection_contraction
    ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
    ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) v hp hq
  rw [(lgManifold n).liouvilleVector_contraction (lambdaPotentialForm φ) y
    ((lgManifold n).liouvilleEquation_exists (lambdaPotentialForm φ) y hnd) v] at h
  rw [hzero] at h
  exact h.symm.trans (((lgManifold n).exteriorDerivative (lambdaPotentialForm φ) y).map_coord_zero
    (0 : Fin 2) rfl)

/-- Actual native critical points of the restricted potential and zeros of
the actual native fiber-projected Liouville field both satisfy the same
exponentially small retained-line estimate for the actual coordinate gradient. -/
theorem tailoringEndpoint_exists_uniform_native_critical_conormal_bound
    (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ φ : RealSpace n → ℝ, ContDiff ℝ ∞ φ →
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x),
      ((∀ v : (lgManifold n).Tangent (lgCover x),
        complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x) v = 0 →
        (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) v = 0) ∨
       (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x)) = 0) →
      ∃ t : ℂ,
        ‖(fun j => (coordinateGradient φ x.1 j : ℂ)) -
            t • tailoringRetainedNormal I β (lgCover x)‖ ≤
          C * Real.exp (-Real.sqrt β) * ‖coordinateGradient φ x.1‖ := by
  obtain ⟨C, hC, B, hB, hline⟩ := tailoringEndpoint_exists_uniform_annihilator_line_bound I
  refine ⟨C, hC, B, hB, fun β hβ x hx φ hφ hnd hcritical => ?_⟩
  apply hline β hβ x hx
  have hkernel (v : TangentCoordinates n)
      (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
      complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
        (lgCoverTangent x v) = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)] at hv
    exact hv
  rcases hcritical with hcritical | hzero
  · refine Or.inl fun v hv => ?_
    rw [← fderiv_eq_coordinateGradient_pairing,
      ← scalarDerivative_potential_lgCover hφ x v]
    exact hcritical _ (hkernel v hv)
  · refine Or.inr fun v hv => ?_
    rw [← lambdaPotentialForm_lgCover φ x v]
    exact lambdaPotentialForm_annihilates_kernel_of_projected_zero φ I β (lgCover x)
      hnd hzero _ (hkernel v hv)

/-- The same estimate is consumed by the literal intrinsic critical point
and intrinsic field-zero conditions on an embedded smooth fiber. The
tangent-image and nonzero pairing contracts are the standard regular
symplectic level contracts, and permit a zero-dimensional fiber. -/
theorem tailoringEndpoint_exists_uniform_embedded_critical_conormal_bound
    (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ x : TangentCoordinates n, tailoringFamily I β 1 (lgCover x) = 1 →
      ∀ φ : RealSpace n → ℝ, ContDiff ℝ ∞ φ →
      ∀ (e : ℕ) (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point),
      j.map a = lgCover x →
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map a),
      (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
        (j.map a) hnd ≠ 0 →
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker →
      ((∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
      ∃ t : ℂ,
        ‖(fun k => (coordinateGradient φ x.1 k : ℂ)) -
            t • tailoringRetainedNormal I β (lgCover x)‖ ≤
          C * Real.exp (-Real.sqrt β) * ‖coordinateGradient φ x.1‖ := by
  obtain ⟨C, hC, B, hB, hline⟩ := tailoringEndpoint_exists_uniform_annihilator_line_bound I
  refine ⟨C, hC, B, hB, fun β hβ x hx φ hφ e N j a hpoint hnd hpi hkernel hcritical => ?_⟩
  apply hline β hβ x hx
  have hcoverKernel (v : TangentCoordinates n)
      (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
      complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
        (lgCoverTangent x v) = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)] at hv
    exact hv
  rcases hcritical with hcritical | hzero
  · have hcriticalNative (v : (lgManifold n).Tangent (j.map a))
        (hv : complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a) v = 0) :
        (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a) v = 0 := by
      have hmem : v ∈ (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a).range := by
        rw [hkernel]
        exact hv
      obtain ⟨w, hw⟩ := hmem
      have hchain := mfderiv_comp_apply a
        ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map a))
        (j.map.contMDiff.mdifferentiable (by simp) a) w
      change N.scalarDerivative (fun z => φ (j.map z).1) a w =
        (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a)
          (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a w) at hchain
      exact (congrArg ((lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a)) hw).symm.trans
        (hchain.symm.trans (hcritical w))
    rw [hpoint] at hcriticalNative
    refine Or.inl fun v hv => ?_
    rw [← fderiv_eq_coordinateGradient_pairing,
      ← scalarDerivative_potential_lgCover hφ x v]
    exact hcriticalNative _ (hcoverKernel v hv)
  · rw [(lgManifold n).complexDifferential_ker_eq_real_inf_imag] at hkernel
    have hprojection := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
      N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) a hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
      hpi hkernel
    rw [hzero, map_zero] at hprojection
    have hlambdaNative (v : (lgManifold n).Tangent (j.map a))
        (hv : complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a) v = 0) :
        evalOne (lambdaPotentialForm φ) (j.map a) v = 0 :=
      lambdaPotentialForm_annihilates_kernel_of_projected_zero φ I β (j.map a)
        hnd hprojection.symm v hv
    rw [hpoint] at hlambdaNative
    refine Or.inr fun v hv => ?_
    rw [← lambdaPotentialForm_lgCover φ x v]
    exact hlambdaNative _ (hcoverKernel v hv)

end FsFltz
