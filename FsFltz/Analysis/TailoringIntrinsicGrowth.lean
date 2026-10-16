import FsFltz.Analysis.TailoringFiberProjectionEstimates

/-!
# Native full tailored fibers and intrinsic Liouville growth

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1208–1237.
The actual positive Poisson scalar constructs the actual smooth symplectic
fiber. The actual intrinsic Liouville field is identified with the proved
projection and satisfies the source's linear coordinate growth on the whole
homogeneous end. These are producers; completeness and completion markings
require the remaining global flow and outwardness arguments.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- Every actual tailored level outside the open unit base disk is a native
smooth symplectic hypersurface, uniformly in the homotopy parameter. This
constructs the full level image and includes zero-dimensional fibers. -/
theorem tailoringFamily_exists_uniform_symplectic_levelEmbedding
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ w : ℂ, 1 ≤ ‖w‖ →
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        Set.range j.map = {y | tailoringFamily I β s y = w} ∧
          N.IsSymplecticOn
            (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ := by
  obtain ⟨_d, _hd, _R, _hR, β₀, hβ₀, hb⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨β₀, hβ₀, fun β hβ s hs w hw => ?_⟩
  apply (lgManifold n).exists_planeFiber_symplecticEmbedding (lambdaPotentialForm φ)
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
    (tailoringFamily I β s) (contMDiff_tailoringFamily_lgManifold I β s) w
  intro y hy
  exact ((hb β hβ s hs y _).2.2 (by rwa [hy])).ne'

/-- Any actual embedding realizing a full level has the literal tangent
kernel. Positive native Poisson pairing proves the required regularity. -/
theorem tailoringFamily_levelEmbedding_tangent_range
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β s : ℝ) (w : ℂ)
    (hpi : ∀ y, tailoringFamily I β s y = w →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = {y | tailoringFamily I β s y = w}) (x : N.Point) :
    (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)).ker := by
  have hreg : ∀ y, tailoringFamily I β s y = w →
      Function.Surjective (complexDifferential (lgManifold n) (tailoringFamily I β s) y) :=
    fun y hy => (lgManifold n).complexDifferential_surjective_of_planePairing_ne_zero
      (lambdaPotentialForm φ) (tailoringFamily I β s) y
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) (hpi y hy).ne'
  have htan := @regularLevel_embedding_tangent_range (2 * n) (lgManifold n) ℂ
    inferInstance inferInstance inferInstance (tailoringFamily I β s) w
    (contMDiff_tailoringFamily_lgManifold I β s) hreg
  rw [Complex.finrank_real_complex] at htan
  exact htan j himage x

/-- On a homogeneous end, the native intrinsic field pushes forward to the
actual covering-coordinate projection of the radial vector. -/
theorem tailoringFamily_intrinsicLiouville_pushforward
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (I : ToricInput n) (β s : ℝ) (z : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 z.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) z.1 z.1 = coordinateGradient φ z.1)
    {e : ℕ} (N : SmoothManifold e) (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hcover : j.map x = lgCover z)
    (hkernel : (mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)).ker)
    (hpi : 0 < coverPlanePairing H
      (fderiv ℝ (fun q => tailoringFamily I β s (lgCover q)) z)) :
    mfderiv 𝓘(ℝ, Model e) 𝓘(ℝ, Model (2 * n)) j.map x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
      lgCoverTangent z
        (coverFiberProjection H (fderiv ℝ (fun q => tailoringFamily I β s (lgCover q)) z) (z.1, 0)) := by
  let hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ z H hH
  have hk := hkernel.trans ((lgManifold n).complexDifferential_ker_eq_real_inf_imag
    (tailoringFamily I β s) (j.map x))
  have hpair : ∀ (y : (lgManifold n).Point) (hy : y = lgCover z)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y h ≠ 0 := by
    intro y hy h
    subst y
    rw [planePairing_lambdaPotentialForm_eq_cover hφ z H hH h
      (contMDiff_tailoringFamily_lgManifold I β s)]
    exact hpi.ne'
  have hndj : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map x) := by
    simpa only [hcover] using hnd
  have hp := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) x
    hndj
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)))
    (hpair (j.map x) hcover hndj) hk
  rw [hp]
  have hproject : ∀ (y : (lgManifold n).Point) (hy : y = lgCover z)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      (lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y h
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β s) y))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β s) y))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y) =
          lgCoverTangent z
            (coverFiberProjection H (fderiv ℝ (fun q => tailoringFamily I β s (lgCover q)) z) (z.1, 0)) := by
    intro y hy h
    subst y
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ z H hH hEuler,
      lgCoverTangent_coverFiberProjection hφ z H hH h
        (contMDiff_tailoringFamily_lgManifold I β s)]
  exact hproject (j.map x) hcover hndj

/-- The actual native intrinsic field has uniform linear growth in the
fixed logarithmic coordinates on the entire homogeneous end. The field is
the primitive-determined intrinsic vector, rather than a supplied vector.
This includes rank one, without asserting a nonempty bounded-value end. -/
theorem tailoringFamily_exists_uniform_intrinsicLiouville_growth
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {Rend : ℝ} (hRend : 0 < Rend)
    (heq : ∀ u, Rend ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (x : N.Point) (z : TangentCoordinates n), j.map x = lgCover z →
        (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x).range =
          (complexDifferential (lgManifold n) (tailoringFamily I β s) (j.map x)).ker →
        R ≤ Real.sqrt (realSquaredNorm z.1) →
        ∃ v : TangentCoordinates n,
          mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
              lgCoverTangent z v ∧
        ‖v‖ ≤ C * Real.sqrt (realSquaredNorm z.1) := by
  obtain ⟨C, hC, Rp, hRp, Bp, hBp, hprojection⟩ :=
    tailoringFamily_exists_uniform_fiberProjection_bounds I hφ hc hU hlower hupper
  obtain ⟨d, hd, Rq, _hRq, Bq, _hBq, hpositive⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  let K := ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖
  have hK : 0 ≤ K := norm_nonneg _
  let R := max (max Rp Rq) (Rend + 1)
  refine ⟨1 + C * K, by positivity, R,
    lt_of_lt_of_le hRp ((le_max_left Rp Rq).trans (le_max_left _ _)),
    max Bp Bq, lt_of_lt_of_le hBp (le_max_left _ _), ?_⟩
  intro β hβ s hs N j x z hcover hkernel hz
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 z.1)
  let L := fderiv ℝ (fun q => tailoringFamily I β s (lgCover q)) z
  have hRpz := ((le_max_left Rp Rq).trans (le_max_left _ _)).trans hz
  have hRqz := ((le_max_right Rp Rq).trans (le_max_left _ _)).trans hz
  have hEndz : Rend < ‖(EuclideanSpace.equiv (Fin n) ℝ).symm z.1‖ := by
    have h := (le_max_right (max Rp Rq) (Rend + 1)).trans hz
    rw [realEuclideanRadius_eq_norm] at h
    linarith
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end hφ hEnd hhom hRend heq hEndz
  have hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 z.1) v = H v := fun _ => rfl
  let hnd := nondegenerate_lambdaPotentialForm_potentialHessian hφ hc hlower z
  have hpi : 0 < coverPlanePairing H L := by
    have hp := (hpositive β ((le_max_right _ _).trans hβ) s hs (lgCover z) hnd).2.1 hRqz
    rw [planePairing_lambdaPotentialForm_eq_cover hφ z H hH hnd
      (contMDiff_tailoringFamily_lgManifold I β s)] at hp
    exact (show 0 < d * Real.exp (supportHeight I (lgCover z).1 - β) ^ 2 / 2 by positivity).trans_le hp
  refine ⟨coverFiberProjection H L (z.1, 0),
    tailoringFamily_intrinsicLiouville_pushforward hφ I β s z H hH hEuler
      N j x hcover hkernel hpi, ?_⟩
  have hpn := (hprojection β ((le_max_left _ _).trans hβ) s hs z hRpz).2
  have hr : ‖(z.1, (0 : RealSpace n))‖ ≤ K * Real.sqrt (realSquaredNorm z.1) := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), realEuclideanRadius_eq_norm]
    exact (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.le_opNorm
      ((EuclideanSpace.equiv (Fin n) ℝ).symm z.1)
  calc
    _ ≤ ‖coverFiberProjection H L‖ * ‖(z.1, (0 : RealSpace n))‖ :=
      (coverFiberProjection H L).le_opNorm _
    _ ≤ C * (K * Real.sqrt (realSquaredNorm z.1)) :=
      mul_le_mul hpn hr (norm_nonneg _) hC.le
    _ ≤ (1 + C * K) * Real.sqrt (realSquaredNorm z.1) := by
      nlinarith [Real.sqrt_nonneg (realSquaredNorm z.1)]

/-- The actual full level-one fiber is constructed together with its
restricted symplectic form and uniform intrinsic end growth. Tangent-kernel
identification and the positive Poisson denominator are proved producers,
not additional assumptions on this constructed fiber. -/
theorem tailoringFamily_exists_uniform_fullFiber_intrinsic_growth
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {Rend : ℝ} (hRend : 0 < Rend)
    (heq : ∀ u, Rend ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
        Set.range j.map = {y | tailoringFamily I β s y = 1} ∧
          N.IsSymplecticOn
            (N.exteriorDerivative (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) univ ∧
          ∀ (x : N.Point) (z : TangentCoordinates n), j.map x = lgCover z →
            R ≤ Real.sqrt (realSquaredNorm z.1) →
            ∃ v : TangentCoordinates n,
              mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) j.map x
                (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
                  lgCoverTangent z v ∧
                ‖v‖ ≤ C * Real.sqrt (realSquaredNorm z.1) := by
  obtain ⟨C, hC, R, hR, Bg, hBg, hgrowth⟩ :=
    tailoringFamily_exists_uniform_intrinsicLiouville_growth I hφ hc hU hlower hupper
      hEnd hhom hRend heq
  obtain ⟨Bf, _hBf, hfiber⟩ :=
    tailoringFamily_exists_uniform_symplectic_levelEmbedding I hφ hc hU hlower hupper
  obtain ⟨_d, _hd, _R, _hR, Bp, _hBp, hp⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  let β₀ := max Bg (max Bf Bp)
  refine ⟨C, hC, R, hR, β₀, lt_of_lt_of_le hBg (le_max_left _ _), ?_⟩
  intro β hβ s hs
  have hBgβ := (le_max_left Bg (max Bf Bp)).trans hβ
  have hBfβ := (le_max_left Bf Bp).trans ((le_max_right Bg _).trans hβ)
  have hBpβ := (le_max_right Bf Bp).trans ((le_max_right Bg _).trans hβ)
  obtain ⟨N, j, himage, hsymp⟩ := hfiber β hBfβ s hs 1 (by simp)
  refine ⟨N, j, himage, hsymp, ?_⟩
  intro x z hcover hz
  have hpos : ∀ y, tailoringFamily I β s y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hp β hBpβ s hs y _).2.2 (by simp [hy])
  exact hgrowth β hBgβ s hs N j x z hcover
    (tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β s 1 hpos j himage x) hz

end FsFltz
