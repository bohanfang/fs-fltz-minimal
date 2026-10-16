import FsFltz.Analysis.TailoringFiberCriticalConormal
import FsFltz.Geometry.PrescribedGradingBridge

/-!
# Exact tangent and conormal equations at good endpoint points

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1491–1493,
and `lem:localcritical`, lines 1463–1468. Plateau values make the actual
cutoff differentials zero pointwise; no open holomorphic neighborhood is
assumed. The full-fiber critical conormal equation uses native intrinsic
criticality and the actual tangent image of the full regular fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- A cutoff attaining either plateau endpoint has zero actual differential. -/
theorem fderiv_tailoringCutoff_eq_zero_of_zero_or_one
    (I : ToricInput n) (β : ℝ) (v : Lattice n) (u : RealSpace n)
    (h : tailoringCutoff I β v u = 0 ∨ tailoringCutoff I β v u = 1) :
    fderiv ℝ (tailoringCutoff I β v) u = 0 := by
  rcases h with h | h
  · apply IsLocalMin.fderiv_eq_zero
    exact Eventually.of_forall fun z => by
      rw [h]
      exact tailoringCutoff_nonneg I β v z
  · apply IsLocalMax.fderiv_eq_zero
    exact Eventually.of_forall fun z => by
      rw [h]
      exact tailoringCutoff_le_one I β v z

/-- At a good point every term of the literal radial error vanishes. -/
theorem tailoringRadialError_eq_zero_of_good
    (I : ToricInput n) (β : ℝ) (y : LGSpace n)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v y.1 = 0 ∨ tailoringCutoff I β v y.1 = 1) :
    tailoringRadialError I β y = 0 := by
  have hzero := fderiv_tailoringCutoff_eq_zero_of_zero_or_one I β 0 y.1
    (hgood 0 (Finset.mem_insert_self _ _))
  have hvertex (v : Lattice n) (hv : v ∈ I.vertices) :=
    fderiv_tailoringCutoff_eq_zero_of_zero_or_one I β v y.1
      (hgood v (Finset.mem_insert_of_mem hv))
  simp only [tailoringRadialError, hzero, ContinuousLinearMap.comp_zero, sub_zero]
  exact Finset.sum_eq_zero fun v hv => by
    ext w
    simp [hvertex v hv]

/-- The actual endpoint differential is exactly complex linear at every
point with plateau cutoff values. -/
theorem fderiv_tailoringFamily_one_eq_leading_of_good
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x =
      tailoringLeadingDifferential I β (lgCover x) := by
  rw [fderiv_tailoringFamily_one_eq_equation_of_fiber I β x hx,
    fderiv_tailoringEquation_cover,
    tailoringRadialError_eq_zero_of_good I β (lgCover x) hgood,
    ContinuousLinearMap.zero_comp, add_zero]

/-- The retained differential intertwines the prescribed standard rotation
and multiplication by `i`, without any condition on the point. -/
theorem tailoringLeadingDifferential_complexStructure
    (I : ToricInput n) (β : ℝ) (y : LGSpace n) (v : TangentCoordinates n) :
    tailoringLeadingDifferential I β y (coordinateComplexStructure n v) =
      Complex.I * tailoringLeadingDifferential I β y v := by
  rw [tailoringLeadingDifferential_apply_eq_normal,
    tailoringLeadingDifferential_apply_eq_normal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateComplexStructure_apply, Pi.neg_apply, Complex.ofReal_neg]
  linear_combination -tailoringRetainedNormal I β y j * (v.2 j : ℂ) *
    Complex.I_mul_I


/-- Every actual good endpoint tangent remains tangent after standard rotation. -/
theorem tailoring_good_kernel_complexStructure
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    (v : TangentCoordinates n)
    (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
    fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x
      (coordinateComplexStructure n v) = 0 := by
  rw [fderiv_tailoringFamily_one_eq_leading_of_good I β x hx hgood] at hv ⊢
  rw [tailoringLeadingDifferential_complexStructure, hv, mul_zero]

/-- Native intrinsic criticality gives the exact retained conormal equation
at a point with plateau cutoff values. -/
theorem tailoring_good_critical_conormal_eq
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    (hG : tailoringRetainedNormal I β (lgCover x) ≠ 0)
    (φ : RealSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (e : ℕ) (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (hpoint : j.map a = lgCover x)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map a))
    (hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (j.map a) hnd ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker)
    (hcritical :
      (∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
      N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) :
    ∃ t : ℂ, (fun k => (coordinateGradient φ x.1 k : ℂ)) =
      t • tailoringRetainedNormal I β (lgCover x) := by
  have hcoverKernel (v : TangentCoordinates n)
      (hv : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0) :
      complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
        (lgCoverTangent x v) = 0 := by
    rw [fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1)] at hv
    exact hv
  have hann :
      (∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, coordinateGradient φ x.1 j * v.1 j = 0) ∨
      (∀ v : TangentCoordinates n,
        fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x v = 0 →
        ∑ j, coordinateGradient φ x.1 j * v.2 j = 0) := by
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
  have hleading := fderiv_tailoringFamily_one_eq_leading_of_good I β x hx hgood
  obtain ⟨t, ht⟩ := exists_retained_line_approximation_of_leading_pairing_bound I β
    (lgCover x) hG (coordinateGradient φ x.1) (η := 0) le_rfl (by
      rcases hann with h | h
      · exact Or.inl fun v hv => by simp [h v (by rwa [hleading])]
      · exact Or.inr fun v hv => by simp [h v (by rwa [hleading])])
  refine ⟨t, sub_eq_zero.mp (norm_le_zero_iff.mp ?_)⟩
  simpa only [mul_zero] using ht

/-- On any presentation of the actual full endpoint fiber, good intrinsic
critical points and intrinsic zeros satisfy the exact conormal equation.
Regularity, tangent range and nonzero retained normal are proved uniformly. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_good_critical_conormal_eq
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      Set.range j.map = {y | tailoringFamily I β 1 y = 1} → ∀ a : N.Point,
      (∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v (j.map a).1 = 0 ∨ tailoringCutoff I β v (j.map a).1 = 1) →
      ((∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0) ∨
        N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) →
      ∃ t : ℂ, (fun k => (coordinateGradient φ (j.map a).1 k : ℂ)) =
        t • tailoringRetainedNormal I β (j.map a) := by
  obtain ⟨B, hB, hnonzero⟩ := tailoringEndpoint_exists_uniform_retainedNormal_ne_zero I
  obtain ⟨_, _, _, _, B', hB', hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨max B B', hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N j himage a hgood hcritical
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_right _ _).trans hβ) 1 (by simp) y _).2.2 (by simp [hy])
  have ha : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map a)
  have h := tailoring_good_critical_conormal_eq I β x (hx.symm ▸ ha)
    (by simpa only [← hx, lgCover] using hgood)
    (hx.symm ▸ hnonzero β ((le_max_left _ _).trans hβ) (j.map a) ha)
    φ hφ (2 * n - 2) N j a hx.symm
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map a))
    (hpi (j.map a) ha).ne'
    (tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1 hpi j himage a)
    hcritical
  simpa only [← hx, lgCover] using h

end FsFltz
