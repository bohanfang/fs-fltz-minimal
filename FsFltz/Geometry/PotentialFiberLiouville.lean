import FsFltz.Geometry.PotentialHamiltonian
import FsFltz.Geometry.RankTwoFiberProjection
import FsFltz.Analysis.PotentialPathFiberBounds

/-!
# The actual intrinsic potential-fiber exhaustion identity

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 730–747,
and `lem:originalends`, lines 770–818. The native symplectic projection and
the actual Hessian Hamiltonian formulas identify the derivative of the
restricted potential along its primitive-determined intrinsic Liouville
field with the literal inverse-metric Cauchy defect. The logarithmic
full-fiber estimate consequently gives outwardness on the chosen path.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

section Pointwise

variable {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (I : ToricInput n) (z : TangentCoordinates n)
    (H : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ v, fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ))
      (WithLp.toLp 2 z.1) v = H v)
    (hEuler : fderiv ℝ (coordinateGradient φ) z.1 z.1 = coordinateGradient φ z.1)

include hφ hH hEuler

/-- The native projected field has the source's literal exhaustion derivative.
The normal correction uses the actual potential Hessian and native `dW`. -/
theorem scalarDerivative_potential_W_fiberProjection
    (hnd : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover z)) :
    (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover z)
      ((lgManifold n).rankTwoFiberProjection
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (lgCover z) hnd
        (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover z)))
        (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover z)))
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover z))) =
      potentialMetricFiberDefect H I (lgCover z) := by
  have hp := planePairing_W_lambdaPotentialForm hφ I z H hH hnd
  have hbase : complexDifferential (lgManifold n) (W I) (lgCover z)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover z)) =
        b0 I (lgCover z) := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ z H hH hEuler,
      complexDifferential_W_lgCover I z (z.1, 0)]
    simp [dW, b0, lgCover, mul_comm]
  have hrad : (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover z)
      ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) (lgCover z)) =
        metricRadialSq H z.1 := by
    rw [liouvilleVector_lambdaPotentialForm_radial_of_hessian hφ z H hH hEuler,
      scalarDerivative_potential_lgCover hφ, fderiv_potential_eq_euclidean_inner hφ,
      euclidean_gradient_eq_hessian_radial hφ z H hH hEuler]
    rfl
  have hA := scalarDerivative_potential_hamiltonian hφ z H hH hEuler hnd
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover z)))
    (toricDerivativeRe I (lgCover z)) (-toricDerivativeIm I (lgCover z))
    (complexDifferential_W_lgCover_re I z)
  have hB := scalarDerivative_potential_hamiltonian hφ z H hH hEuler hnd
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) (lgCover z)))
    (toricDerivativeIm I (lgCover z)) (toricDerivativeRe I (lgCover z))
    (complexDifferential_W_lgCover_im I z)
  have hb := b0_eq_complex_euclidean_pairing I (lgCover z)
  have hbRe := congrArg Complex.re hb
  have hbIm := congrArg Complex.im hb
  simp only [lgCover, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, one_mul, zero_add] at hbRe hbIm
  change (b0 I (lgCover z)).re =
    inner ℝ (WithLp.toLp 2 z.1) (toricDerivativeRe I (lgCover z)) at hbRe
  change (b0 I (lgCover z)).im =
    inner ℝ (WithLp.toLp 2 z.1) (toricDerivativeIm I (lgCover z)) at hbIm
  rw [inner_neg_right, ← hbIm] at hA
  rw [← hbRe] at hB
  change _ = metricRadialSq H z.1 -
    Complex.normSq (b0 I (lgCover z)) / toricInverseMetricSq H I (lgCover z)
  change differentialCovector (lgManifold n) (fun y => φ y.1) (lgCover z)
    (_ + _ • _ - _ • _) = _
  rw [map_sub, map_add, map_smul, map_smul]
  change (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover z) _ +
    (_ / (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) (lgCover z) hnd) *
      (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover z) _ -
    (_ / (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) (lgCover z) hnd) *
      (lgManifold n).scalarDerivative (fun y => φ y.1) (lgCover z) _ = _
  simp only [SmoothManifold.hamiltonianVector] at hA hB
  rw [hrad, hA, hB, hp]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, hbase, Complex.normSq_apply]
  ring

/-- The actual primitive-determined intrinsic field on any smooth realization
of a regular fiber satisfies the literal exhaustion identity. Its tangent
kernel equation is supplied by the regular-level theorem. -/
theorem scalarDerivative_potential_W_fiberLiouville {d : ℕ}
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hcover : j.map x = lgCover z)
    (hkernel : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker)
    (ha : 0 < toricInverseMetricSq H I (j.map x)) :
    N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
        potentialMetricFiberDefect H I (j.map x) := by
  have hnd := nondegenerate_lambdaPotentialForm_of_hessian hφ z H hH
  have hnd' : (lgManifold n).Nondegenerate
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) (j.map x) :=
    by rw [hcover]; exact hnd
  have hpair : ∀ (y : (lgManifold n).Point) (hy : y = lgCover z)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      (lgManifold n).planePairing (lambdaPotentialForm φ) (W I) y h =
        toricInverseMetricSq H I y := by
    intro y hy h
    subst y
    exact planePairing_W_lambdaPotentialForm hφ I z H hH h
  have hpi : (lgManifold n).planePairing (lambdaPotentialForm φ) (W I)
      (j.map x) hnd' ≠ 0 := by
    rw [hpair (j.map x) hcover hnd']
    exact ha.ne'
  have hkernel' := hkernel.trans
    ((lgManifold n).complexDifferential_ker_eq_real_inf_imag (W I) (j.map x))
  have hpush := (lgManifold n).liouvilleVector_pullback_eq_rankTwoFiberProjection
    N j (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) x hnd'
    (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) (j.map x)))
    (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) (j.map x))) hpi hkernel'
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hchain := mfderiv_comp_apply x
    ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (j.map x))
    (j.map.contMDiff.mdifferentiable (by simp) x)
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)
  change N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) =
      (lgManifold n).scalarDerivative (fun y => φ y.1) (j.map x)
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x)) at hchain
  rw [hchain, hpush]
  have hscalar : ∀ (y : (lgManifold n).Point) (hy : y = lgCover z)
      (h : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y),
      (lgManifold n).scalarDerivative (fun y => φ y.1) y
        ((lgManifold n).rankTwoFiberProjection
          ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y h
          (Complex.reCLM.comp (complexDifferential (lgManifold n) (W I) y))
          (Complex.imCLM.comp (complexDifferential (lgManifold n) (W I) y))
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y)) =
            potentialMetricFiberDefect H I y := by
    intro y hy h
    subst y
    exact scalarDerivative_potential_W_fiberProjection hφ I z H hH hEuler h
  exact hscalar (j.map x) hcover hnd'

end Pointwise

/-- For the retained affine potential path, the native intrinsic derivative
is the actual Hessian defect on the same homogeneous end. -/
theorem scalarDerivative_potentialPath_W_fiberLiouville
    {φ φEnd : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) u) v) v)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L) (hend : ∀ u, L ≤ ‖u‖ → φ u = φEnd u)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (I : ToricInput n)
    {d : ℕ} (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point)
    (hkernel : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x).range =
      (complexDifferential (lgManifold n) (W I) (j.map x)).ker)
    (hx : L < ‖(WithLp.toLp 2 (j.map x).1 : EuclideanSpace ℝ (Fin n))‖)
    (ha : 0 < toricInverseMetricSq
      (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 (j.map x).1)) I (j.map x)) :
    let ψ := potentialPath (fun u => ‖u‖ ^ 2 / 2) φ s ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm
    N.scalarDerivative ((fun y => ψ y.1) ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x) =
        potentialMetricFiberDefect
          (potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 (j.map x).1)) I (j.map x) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun u => ‖u‖ ^ 2 / 2
  let ψ := potentialPath q φ s ∘ e.symm
  let ψEnd := potentialPath q φEnd s ∘ e.symm
  have hq : ContDiff ℝ ∞ q := (contDiff_id.norm_sq ℝ).div_const 2
  have hψ : ContDiff ℝ ∞ ψ := (potentialPath_contDiff_space hq hφ s).comp e.symm.contDiff
  have hψEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ ψEnd u := by
    intro u hu
    exact ((contDiffAt_const.mul hq.contDiffAt).add
      (contDiffAt_const.mul (hEnds (e.symm u) (by simpa [e] using hu)))).comp u
        e.symm.contDiff.contDiffAt
  have hqhom : ∀ r : ℝ, 0 < r → ∀ u : EuclideanSpace ℝ (Fin n),
      q (r • u) = r ^ 2 * q u := by
    intro r hr u
    dsimp [q]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    ring
  have hψhom : ∀ r : ℝ, 0 < r → ∀ u, ψEnd (r • u) = r ^ 2 * ψEnd u := by
    intro r hr u
    simp only [ψEnd, Function.comp_apply, map_smul]
    exact potentialPath_homogeneous_two hqhom hhom s r hr _
  have hψeq : ∀ u, L ≤ ‖e.symm u‖ → ψ u = ψEnd u :=
    fun u hu => potentialPath_eq_of_eq_right (hend (e.symm u) hu) s
  obtain ⟨z, hz⟩ := lgCover_surjective n (j.map x)
  have hcoord : (j.map x).1 = z.1 := congrArg Prod.fst hz.symm
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end
    hψ hψEnds hψhom hL hψeq (by simpa [e, hcoord] using hx)
  let H := potentialPathHessianEquiv hφ hc hlower s hs (WithLp.toLp 2 (j.map x).1)
  have hcompose : ψ ∘ e = potentialPath q φ s := by
    funext u
    simp [ψ]
  have hH : ∀ v, fderiv ℝ (gradient (ψ ∘ e)) (WithLp.toLp 2 z.1) v = H v := by
    intro v
    rw [hcompose]
    simp only [H, hcoord, potentialPathHessianEquiv_apply]
    rfl
  exact scalarDerivative_potential_W_fiberLiouville hψ I z H hH hEuler N j x
    hz.symm hkernel ha

/-- The proved common logarithmic potential level controls the actual intrinsic
Liouville derivative for every independent coefficient and potential parameter.
The restricted primitive and its field are literal, and the homogeneous end
and inverse metric denominator are consequences of the end-level producer. -/
theorem _root_.FsFltz.ToricInput.coefficientPath_potentialPath_intrinsic_fiber_outward
    (I : ToricInput n) {φ φEnd : EuclideanSpace ℝ (Fin n) → ℝ} {c C : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v, c * ‖v‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient φ) u) v) v)
    (hupper : ∀ u v, inner ℝ ((fderiv ℝ (gradient φ) u) v) v ≤ C * ‖v‖ ^ 2)
    {L : ℝ} (hL : 0 < L) (hend : ∀ u, L ≤ ‖u‖ → φ u = φEnd u)
    (Aamb : ℝ) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      Aamb ≤ F ^ 2 * β ^ 2 / 2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, ∀ _hs : s ∈ Set.Icc (0 : ℝ) 1,
      ∀ (d : ℕ) (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (x : N.Point),
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (2 * n)) j.map x).range =
          (complexDifferential (lgManifold n) (W (I.alongCoefficientPath t)) (j.map x)).ker →
        let ψ := potentialPath (fun u => ‖u‖ ^ 2 / 2) φ s ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm
        F ^ 2 * β ^ 2 / 2 ≤ ψ (j.map x).1 →
        ‖W (I.alongCoefficientPath t) (j.map x)‖ ≤ Real.exp β →
          ψ (j.map x).1 ≤ N.scalarDerivative ((fun y => ψ y.1) ∘ j.map) x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x) ∧
          0 < N.scalarDerivative ((fun y => ψ y.1) ∘ j.map) x
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x) := by
  obtain ⟨F, hF, β₀, hβ₀, hbound⟩ :=
    I.coefficientPath_potentialPath_logarithmic_potential_level
      hφ hEnd1 hEnds hhom hc hlower hupper hL hend Aamb
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨hA, hfiber⟩ := hbound β hβ
  refine ⟨hA, ?_⟩
  intro t ht s hs d N j x hkernel ψ hx hW
  obtain ⟨hEnd, ha, hdef⟩ := hfiber t ht s hs (j.map x) hx hW
  have hid := scalarDerivative_potentialPath_W_fiberLiouville hφ hc hlower hEnds hhom
    hL hend s hs (I.alongCoefficientPath t) N j x hkernel hEnd ha
  change N.scalarDerivative ((fun y => ψ y.1) ∘ j.map) x
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x) = _ at hid
  rw [hid]
  refine ⟨hdef, ?_⟩
  have hβpos := hβ₀.trans_le hβ
  have hlevel : 0 < F ^ 2 * β ^ 2 / 2 := div_pos (mul_pos (sq_pos_of_pos hF)
    (sq_pos_of_pos hβpos)) (by norm_num)
  exact (hlevel.trans_le hx).trans_le hdef

end FsFltz.Geometry
