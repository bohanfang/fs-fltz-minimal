import FsFltz.Analysis.OriginalRoundedBoundary
import FsFltz.Analysis.OriginalFiberManifold
import FsFltz.Analysis.OriginalFiberSymplectic

/-!
# The actual intrinsic Liouville projection on original fibers

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 774–818,
and `prop:allinitial`, lines 925–930; `geoemtric-part-fsf.tex`,
`eq:fiberbound`, lines 277–289, and `g:initial`, lines 373–379.
The already defined projected radial vector is tangent to `ker dW` and
contracts the canonical ambient two-form to the original primitive there.
The native tangent-image and nondegeneracy bridges identify it with the
actual fiber Liouville field. Its exhaustion derivative is the intrinsic
Cauchy defect, distinct from the ambient expression `QW / a`.
No complete flow or completion marking is assumed or asserted here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators ComplexConjugate

namespace FsFltz

variable {n : ℕ}

/-- The normal correction is symplectically orthogonal to every fiber
tangent: its contraction is the imaginary part of a multiple of `dW r`.
Source: `lem:originalends`, intrinsic projection used in lines 790–812. -/
theorem omega0Coordinates_originalFiberTangent (I : ToricInput n)
    (y : LGSpace n) (r : TangentCoordinates n) (hr : dW I y r = 0) :
    omega0Coordinates (originalFiberTangentCoordinates I y) r =
      lambda0Coordinates y r := by
  have homega := omegaKCoordinates_eq_omega I 0 y (originalFiberTangentCoordinates I y) r
  simp only [omegaKCoordinates, zero_mul, add_zero, CoordinateGeometry.omega] at homega
  rw [homega, tangentComplexCoordinates_originalFiberTangent]
  have hinner : (∑ j, conj ((y.1 j : ℂ) -
      conj (G I y j) * (b0 I y / (a I y : ℂ))) * tangentComplexCoordinates r j) =
      (∑ j, conj (radialComplexCoordinates y j) * tangentComplexCoordinates r j) -
        conj (b0 I y / (a I y : ℂ)) * dW I y r := by
    rw [dW_eq_evaluation]
    simp only [map_sub, map_mul, Complex.conj_ofReal, starRingEnd_self_apply,
      sub_mul, Finset.sum_sub_distrib, CoordinateGeometry.evaluation, Finset.mul_sum,
      radialComplexCoordinates]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hinner, hr, mul_zero, sub_zero]
  have hprim := lambdaKCoordinates_eq_primitive I 0 y r
  simp only [lambdaKCoordinates, zero_div, zero_mul, add_zero,
    CoordinateGeometry.primitive] at hprim
  exact hprim.symm

end FsFltz

namespace FsFltz.Geometry

open SmoothManifold

variable {n : ℕ}

/-- The projected radial vector, pushed through the actual quotient cover,
lies in the kernel of the native complex differential of `W`. -/
theorem complexDifferential_W_originalFiberTangent_lgCover (I : ToricInput n)
    (x : TangentCoordinates n) (ha : 0 < a I (lgCover x)) :
    complexDifferential (lgManifold n) (W I) (lgCover x)
      (lgCoverTangent x (originalFiberTangentCoordinates I (lgCover x))) = 0 := by
  rw [complexDifferential_W_lgCover]
  exact dW_originalFiberTangent_zero I (lgCover x) ha

/-- The coordinate projection satisfies the actual native contraction
equation on the entire native tangent kernel, not just representative
coordinate directions. Source: `lem:originalends`, lines 790–812. -/
theorem exteriorDerivative_lambda0Form_originalFiberTangent_lgCover
    (I : ToricInput n) (x : TangentCoordinates n)
    (v : (lgManifold n).Tangent (lgCover x))
    (hv : complexDifferential (lgManifold n) (W I) (lgCover x) v = 0) :
    evalTwo ((lgManifold n).exteriorDerivative (lambda0Form n)) (lgCover x)
      (lgCoverTangent x (originalFiberTangentCoordinates I (lgCover x))) v =
        evalOne (lambda0Form n) (lgCover x) v := by
  obtain ⟨r, rfl⟩ := (lgCoverTangent_bijective x).2 v
  have hr : dW I (lgCover x) r = 0 := by
    simpa only [complexDifferential_W_lgCover] using hv
  have hcover := exteriorDerivative_lambdaKForm_lgCover I 0 x
    (originalFiberTangentCoordinates I (lgCover x)) r
  simp only [lambdaKForm, zero_smul, add_zero, omegaKCoordinates, zero_mul] at hcover
  rw [hcover, omega0Coordinates_originalFiberTangent I (lgCover x) r hr,
    lambda0Form_lgCover]

/-- The actual intrinsic Liouville field pushes forward to the coordinate
projection. The tangent-kernel equation and nondegeneracy are established
by the regular-level and symplectic-restriction producers. -/
theorem originalFiberLiouville_pushforward_lgCover {d : ℕ}
    (I : ToricInput n) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hkernel : (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker)
    (z : TangentCoordinates n) (hcover : j.map x = lgCover z)
    (ha : 0 < a I (j.map x)) :
    mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x) =
        lgCoverTangent z (originalFiberTangentCoordinates I (lgCover z)) := by
  let D := mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x
  let q := lgCoverTangent z (originalFiberTangentCoordinates I (lgCover z))
  have hq : complexDifferential (lgManifold n) (W I) (j.map x) q = 0 := by
    rw [hcover]
    exact complexDifferential_W_originalFiberTangent_lgCover I z (hcover ▸ ha)
  have hqrange : q ∈ D.range := by
    rw [hkernel]
    exact hq
  obtain ⟨v, hv⟩ := hqrange
  change D v = q at hv
  have heq : N.LiouvilleEquation
      (N.pullback (lgManifold n) j.map (lambda0Form n)) x v := by
    intro w
    rw [N.exteriorDerivative_pullback (lgManifold n) j.map (lambda0Form n)
      (isSmoothForm_lambda0Form n)]
    change ((lgManifold n).exteriorDerivative (lambda0Form n) (j.map x))
      (D ∘ ![v, w]) = lambda0Form n (j.map x) (D ∘ fun _ => w)
    have htuple : D ∘ ![v, w] = ![D v, D w] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, hv]
    have hw : complexDifferential (lgManifold n) (W I) (j.map x) (D w) = 0 := by
      have hmem : D w ∈ D.range := ⟨w, rfl⟩
      rw [hkernel] at hmem
      exact hmem
    rw [hcover] at hw ⊢
    exact exteriorDerivative_lambda0Form_originalFiberTangent_lgCover I z (D w) hw
  rw [N.liouvilleVector_eq _ x
    (nondegenerate_pullback_lambda0Form_of_tangent_kernel I N j x hkernel) heq]
  exact hv

/-- The native derivative of the restricted exhaustion is the intrinsic
Cauchy defect in `eq:fiberbound`, with no ambient `QW` cross term. -/
theorem scalarDerivative_phi0_originalFiberLiouville {d : ℕ}
    (I : ToricInput n) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hkernel : (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker)
    (ha : 0 < a I (j.map x)) :
    N.scalarDerivative (phi0 ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x) =
        realSquaredNorm (j.map x).1 - Complex.normSq (b0 I (j.map x)) / a I (j.map x) := by
  obtain ⟨z, hz⟩ := lgCover_surjective n (j.map x)
  have hpush := originalFiberLiouville_pushforward_lgCover I N j x hkernel z hz.symm ha
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hchain := mfderiv_comp_apply x
    (contMDiff_original_phi0.mdifferentiable (by simp) (j.map x))
    (j.map.contMDiff.mdifferentiable (by simp) x)
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x)
  change N.scalarDerivative (phi0 ∘ j.map) x
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x) =
      differentialCovector (lgManifold n) phi0 (j.map x)
        (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x)) at hchain
  rw [hchain, hpush, ← hz, differentialCovector_phi0_lgCover,
    dPhi0_originalFiberTangent]

/-- Cauchy–Schwarz bounds the intrinsic defect throughout every regular
fiber, including its compact part. Source: `lem:originalends`, lines 808–815. -/
theorem original_fiberDefect_bounds (I : ToricInput n) (y : LGSpace n)
    (ha : 0 < a I y) :
    0 ≤ realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y ∧
      realSquaredNorm y.1 - Complex.normSq (b0 I y) / a I y ≤ 2 * phi0 y := by
  have hc := norm_b0_le_euclidean_radius_mul_sqrt_a I y
  have hr := Real.sqrt_nonneg (realSquaredNorm y.1)
  have hg := Real.sqrt_nonneg (a I y)
  have hsq : Complex.normSq (b0 I y) ≤ realSquaredNorm y.1 * a I y := by
    rw [Complex.normSq_eq_norm_sq]
    have heq : (Real.sqrt (realSquaredNorm y.1) * Real.sqrt (a I y)) ^ 2 =
        realSquaredNorm y.1 * a I y := by
      rw [mul_pow, Real.sq_sqrt (realSquaredNorm_nonneg y.1),
        Real.sq_sqrt ha.le]
    nlinarith [norm_nonneg (b0 I y), mul_nonneg hr hg]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ ha).mpr hsq)
  · have hquot : 0 ≤ Complex.normSq (b0 I y) / a I y :=
      div_nonneg (Complex.normSq_nonneg _) ha.le
    unfold phi0
    linarith

/-- The actual intrinsic field satisfies the scalar growth estimate needed
for complete flow from the proper restricted exhaustion. -/
theorem scalarDerivative_phi0_originalFiberLiouville_growth {d : ℕ}
    (I : ToricInput n) (N : SmoothManifold d)
    (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hkernel : (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model (2 * n))) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker)
    (ha : 0 < a I (j.map x)) :
    |N.scalarDerivative (phi0 ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x)| ≤
        2 * (1 + phi0 (j.map x)) := by
  rw [scalarDerivative_phi0_originalFiberLiouville I N j x hkernel ha]
  obtain ⟨hnonneg, hle⟩ := original_fiberDefect_bounds I (j.map x) ha
  rw [abs_of_nonneg hnonneg]
  linarith

/-- On the whole actual far fiber the intrinsic derivative has the global
linear growth bound, without a supplied denominator hypothesis. -/
theorem scalarDerivative_phi0_original_farFiber_growth (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) (x : N.Point) :
    |N.scalarDerivative (phi0 ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x)| ≤
        2 * (1 + phi0 (j.map x)) := by
  have hx : W I (j.map x) = (R : ℂ) := by
    have hmem : j.map x ∈ Set.range j.map := ⟨x, rfl⟩
    rw [himage] at hmem
    exact hmem
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  have hphi := phi0_gt_of_far_value I Aamb R
    (sublevelMaximumAttained I Aamb hamb.1.le) ((le_max_right _ _).trans_lt hR)
    (j.map x) (by rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos])
  exact scalarDerivative_phi0_originalFiberLiouville_growth I N j x
    (original_farFiber_embedding_tangent_range I hamb hR j himage x)
    (hamb.2 (j.map x) hphi.le).1

/-- The source fiber-end estimate is outwardness of the actual intrinsic
Liouville field for the literal restricted exhaustion on every actual full
far-fiber realization. Source: `prop:allinitial`, lines 925–930. -/
theorem scalarDerivative_phi0_original_farFiber_pos (I : ToricInput n)
    {Aamb R Afib : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (hfib : FiberEndBound I Aamb R Afib)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : Set.range j.map = FullFiber I R) (x : N.Point)
    (hx : Afib ≤ phi0 (j.map x)) :
    0 < N.scalarDerivative (phi0 ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambda0Form n)) x) := by
  have hW : W I (j.map x) = (R : ℂ) := by
    have hmem : j.map x ∈ Set.range j.map := ⟨x, rfl⟩
    rw [himage] at hmem
    exact hmem
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  have hbound := hfib.2 (j.map x) hx (by
    rw [hW, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos])
  rw [scalarDerivative_phi0_originalFiberLiouville I N j x
    (original_farFiber_embedding_tangent_range I hamb hR j himage x) hbound.1]
  exact hbound.2

end FsFltz.Geometry
