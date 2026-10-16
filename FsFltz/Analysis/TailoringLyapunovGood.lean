import FsFltz.Analysis.TailoringGoodDifferential
import FsFltz.Analysis.PotentialComplexPositivity

/-!
# The actual intrinsic Lyapunov identity at good endpoint points

Source: `geometric-part-fsf-proof.tex`, `prop:lyapunov`, lines 1491–1493.
Pointwise plateau flatness makes the actual tangent kernel complex.
The primitive-determined projected field therefore has energy equal to
its derivative of the potential. No open holomorphic neighborhood or
independently supplied gradient field is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter
open scoped BigOperators Topology ContDiff Manifold

variable {n : ℕ}

/-- The source's intrinsic energy identity uses the actual native projected
Liouville vector and the prescribed standard rotation of its cover vector. -/
theorem tailoring_good_projectedLiouville_energy
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (lgCover x) hnd ≠ 0)
    (q : TangentCoordinates n)
    (hq : lgCoverTangent x q =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x))) :
    (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x q) =
      evalTwo ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x)
        (lgCoverTangent x q) (lgCoverTangent x (coordinateComplexStructure n q)) := by
  let L := complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
  have hker : L (lgCoverTangent x q) = 0 := by
    have hp := (lgManifold n).rankTwoFiberProjection_mem_kernel
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
      (Complex.reCLM.comp L) (Complex.imCLM.comp L) hpi
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x))
    rw [← hq] at hp
    apply Complex.ext
    · simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.zero_re] using hp.1
    · simpa only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Complex.zero_im] using hp.2
  have hrotate : L (lgCoverTangent x (coordinateComplexStructure n q)) = 0 := by
    have hlead := fderiv_tailoringFamily_one_eq_leading_of_good I β x hx hgood
    have hfd := fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1) x
    have hlq : tailoringLeadingDifferential I β (lgCover x) q = 0 := by
      rw [← hlead, hfd]
      exact hker
    change complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)
      (lgCoverTangent x (coordinateComplexStructure n q)) = 0
    rw [← ContinuousLinearMap.comp_apply, ← hfd, hlead,
      tailoringLeadingDifferential_complexStructure, hlq, mul_zero]
  have hcon := (lgManifold n).rankTwoFiberProjection_contraction
    ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
    (Complex.reCLM.comp L) (Complex.imCLM.comp L)
    ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x))
    (lgCoverTangent x (coordinateComplexStructure n q))
    (by simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hrotate, Complex.zero_re])
    (by simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, hrotate, Complex.zero_im])
  rw [← hq, (lgManifold n).liouvilleVector_contraction (lambdaPotentialForm φ)
    (lgCover x) ((lgManifold n).liouvilleEquation_exists (lambdaPotentialForm φ) (lgCover x) hnd)]
    at hcon
  rw [hcon, lambdaPotentialForm_lgCover, coordinateComplexStructure_apply,
    scalarDerivative_potential_lgCover hφ, fderiv_eq_coordinateGradient_pairing]

/-- Strict positivity uses the actual native projected vector. -/
theorem tailoring_good_projectedLiouville_positive
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x))
    (hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (lgCover x) hnd ≠ 0)
    (q : TangentCoordinates n)
    (hq : lgCoverTangent x q =
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover x) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (lgCover x)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover x))) (hqne : q ≠ 0) :
    0 < (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover x) (lgCoverTangent x q) := by
  rw [tailoring_good_projectedLiouville_energy I β x hx hgood hφ hnd hpi q hq]
  exact exteriorDerivative_lambdaPotentialForm_complex_pos hφ hc hlower x q hqne

/-- The genuine intrinsic field on every full fiber presentation is strictly
Lyapunov at each good point where it is nonzero. All regularity and
symplectic tangent contracts follow from the finite-input producers. -/
theorem tailoringEndpoint_exists_uniform_fullFiber_good_liouville_positive
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
      N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a ≠ 0 →
      0 < N.scalarDerivative (fun z => φ (j.map z).1) a
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a) := by
  obtain ⟨_, _, _, _, B, hB, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨B, hB, ?_⟩
  intro β hβ N j himage a hgood hzero
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β hβ 1 (by simp) y _).2.2 (by simp [hy])
  have ha : tailoringFamily I β 1 (j.map a) = 1 := by
    have hmem : j.map a ∈ Set.range j.map := ⟨a, rfl⟩
    rwa [himage] at hmem
  obtain ⟨x, hx⟩ := lgCover_surjective n (j.map a)
  have hkernel := tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β 1 1
    hpi j himage a
  let Z := N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a
  let D := mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map a
  have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (j.map a)
  have hpush := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) a hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (hpi (j.map a) ha).ne'
    (hkernel.trans ((lgManifold n).complexDifferential_ker_eq_real_inf_imag _ _))
  have hchain := mfderiv_comp_apply a
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map a))
    (j.map.contMDiff.mdifferentiable (by simp) a) Z
  change N.scalarDerivative (fun z => φ (j.map z).1) a Z =
    (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a) (D Z) at hchain
  rw [hchain]
  have hDne : D Z ≠ 0 := fun he => hzero (j.immersion a (he.trans D.map_zero.symm))
  have hpositive : ∀ (y : LGSpace n) (hy : y = lgCover x)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      tailoringFamily I β 1 y = 1 →
      (∀ v ∈ tailoringExponents I,
        tailoringCutoff I β v y.1 = 0 ∨ tailoringCutoff I β v y.1 = 1) →
      (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y h ≠ 0 →
      ∀ v : (lgManifold n).Tangent y,
        v = (lgManifold n).rankTwoFiberProjection
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y h
          (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
          (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) y))
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) →
        v ≠ 0 → 0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y v := by
    intro y hy h hf hg hp v hv hvne
    subst y
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    apply tailoring_good_projectedLiouville_positive I β x hf hg hφ hc hlower h hp q hv
    exact fun hq => hvne (by rw [hq, map_zero])
  exact hpositive (j.map a) hx.symm hnd ha hgood (hpi (j.map a) ha).ne' (D Z) hpush hDne

/-- At a good actual endpoint point, an intrinsic zero is an intrinsic
critical point. The proof rotates every actual tangent and uses the native
Liouville contraction equation, without assuming an independent gradient. -/
theorem tailoring_good_intrinsic_zero_is_critical
    (I : ToricInput n) (β : ℝ) (x : TangentCoordinates n)
    (hx : tailoringFamily I β 1 (lgCover x) = 1)
    (hgood : ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v x.1 = 0 ∨ tailoringCutoff I β v x.1 = 1)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : ℕ) (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n)) (a : N.Point)
    (hpoint : j.map a = lgCover x)
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map a))
    (hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1)
      (j.map a) hnd ≠ 0)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker)
    (hzero : N.liouvilleVector
      (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) a = 0) :
    ∀ v : N.Tangent a, N.scalarDerivative (fun z => φ (j.map z).1) a v = 0 := by
  have hprojection := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) a hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)))
    hpi (hkernel.trans ((lgManifold n).complexDifferential_ker_eq_real_inf_imag _ _))
  rw [hzero, map_zero] at hprojection
  have hlambdaNative (v : (lgManifold n).Tangent (j.map a))
      (hv : complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a) v = 0) :
      evalOne (lambdaPotentialForm φ) (j.map a) v = 0 :=
    lambdaPotentialForm_annihilates_kernel_of_projected_zero φ I β (j.map a)
      hnd hprojection.symm v hv
  rw [hpoint] at hlambdaNative
  have hscalarNative (v : (lgManifold n).Tangent (j.map a))
      (hv : complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a) v = 0) :
      (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a) v = 0 := by
    rw [hpoint] at hv ⊢
    obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
    have hfd := fderiv_complex_lgCover (contMDiff_tailoringFamily_lgManifold I β 1) x
    have hq : fderiv ℝ (fun z => tailoringFamily I β 1 (lgCover z)) x q = 0 := by
      rw [hfd]
      exact hv
    have hJq := tailoring_good_kernel_complexStructure I β x hx hgood q hq
    rw [hfd] at hJq
    have hann := hlambdaNative _ hJq
    change evalOne (lambdaPotentialForm φ) (lgCover x)
      (lgCoverTangent x (coordinateComplexStructure n q)) = 0 at hann
    rw [lambdaPotentialForm_lgCover φ x (coordinateComplexStructure n q),
      coordinateComplexStructure_apply] at hann
    rw [scalarDerivative_potential_lgCover hφ, fderiv_eq_coordinateGradient_pairing]
    exact hann
  intro v
  have hmem : mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a v ∈
      (complexDifferential (lgManifold n) (tailoringFamily I β 1) (j.map a)).ker := by
    rw [← hkernel]
    exact ⟨v, rfl⟩
  have hchain := mfderiv_comp_apply a
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map a))
    (j.map.contMDiff.mdifferentiable (by simp) a) v
  change N.scalarDerivative (fun z => φ (j.map z).1) a v =
    (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map a)
      (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map a v) at hchain
  exact hchain.trans (hscalarNative _ hmem)

end FsFltz
