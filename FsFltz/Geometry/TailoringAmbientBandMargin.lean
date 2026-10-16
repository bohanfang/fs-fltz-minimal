import FsFltz.Geometry.TailoringAmbientRayPositivity
import FsFltz.Geometry.FlowAbsorption

/-!
# A uniform ambient base margin on compact outward cone bands

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1802–1816.
Compactness supplies a positive margin on a bounded radial continuation.
The rank-two quotient is a convex combination, so the margin holds for
every nonnegative base coefficient, even without a coefficient upper bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold
namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

private theorem scalarDerivative_re_complex {d : ℕ} (M : SmoothManifold d)
    {f : M.Point → ℂ} (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun y => (f y).re) x v = (complexDifferential M f x v).re := by
  unfold SmoothManifold.scalarDerivative complexDifferential
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (Complex.reCLM ∘ f) x v = _
  rw [mfderiv_comp x ((show ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ Complex.reCLM from Complex.reCLM.contMDiff).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, Complex.reCLM.fderiv]
  rfl

/-- A single positive lower bound on each compact radial band works for
the actual updated fields at all nonnegative coefficients. -/
theorem tailoringEndpoint_exists_uniform_outward_band_base_margin
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ T : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ tailoringCoreSection I φEnd β, ∀ t ∈ Icc (1 : ℝ) T,
        ∀ K : ℝ, 0 ≤ K → ε ≤
          (complexDifferential (lgManifold n) (tailoringFamily I β 1) (t • y.1, y.2)
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (t • y.1, y.2))).re := by
  obtain ⟨Ba, hBa, hamb⟩ :=
    tailoringEndpoint_exists_uniform_coreSection_outward_ambient_liouville
      I hφ hc hlower hEnd hR heq
  obtain ⟨_, _, _, _, Bp, _, hpair⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Br, hray⟩ := eventually_atTop.mp hEnd.eventually_coreSection_outward_ray
  obtain ⟨Bc, hcompact⟩ := eventually_atTop.mp (hEnd.eventually_coreSection_compact Φ hΦ hΦ₀)
  refine ⟨max Ba (max Bp (max Br Bc)), hBa.trans_le (le_max_left _ _), ?_⟩
  intro β hβ T
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have haβ := hamb β ((le_max_left _ _).trans hβ)
  have hpβ := hpair β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) 1 (by simp)
  have hrβ := hray β ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  have hcβ := hcompact β ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)))
  let f := tailoringFamily I β 1
  have hf := contMDiff_tailoringFamily_lgManifold I β 1
  let Z := (lgManifold n).liouvilleVector (lambdaPotentialForm φ)
  let a := fun x => (lgManifold n).scalarDerivative (fun y => (f y).re) x (Z x)
  let ray : ℝ × LGSpace n → LGSpace n := fun p => (p.1 • p.2.1, p.2.2)
  have hsm := (lgManifold n).isSmoothVectorField_liouvilleVector _
    (isSmoothForm_lambdaPotentialForm hφ)
    (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
  have ha : Continuous a := continuous_scalarDerivative_vectorField hsm _
    (Complex.reCLM.contMDiff.comp hf)
  have hrc : Continuous ray := (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd
  have hmin : Continuous (fun p => min (a (ray p)) ((f (ray p)).re / 2)) :=
    (ha.comp hrc).min ((Complex.continuous_re.comp (hf.continuous.comp hrc)).div_const 2)
  obtain ⟨ε, hε, hbound⟩ := (isCompact_Icc.prod hcβ).exists_forall_le'
    hmin.continuousOn (a := 0) (by
      rintro ⟨t, y⟩ ⟨ht, hy⟩
      obtain ⟨d, hd, he⟩ := haβ y hy t ht.1
      have hreal := (hrβ y hy t ht.1).2.2.1
      apply lt_min
      · dsimp only [a, ray, Z]
        rw [scalarDerivative_re_complex _ hf, he, Complex.ofReal_re]
        exact hd
      · exact div_pos hreal (by norm_num))
  refine ⟨ε, hε, ?_⟩
  intro y hy t ht K hK
  have hb := hbound (t, y) ⟨ht, hy⟩
  have hlow := (le_min_iff.mp hb).1
  have hval := (le_min_iff.mp hb).2
  obtain ⟨d, hd, he⟩ := haβ y hy t ht.1
  have hr := hrβ y hy t ht.1
  let x : LGSpace n := (t • y.1, y.2)
  let hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower x
  let π := (lgManifold n).planePairing (lambdaPotentialForm φ) f x hnd
  have hπ : 0 ≤ π := (hpβ x hnd).1
  have hden : 0 < 1 + K * π := by positivity
  have hfx : f x = ((f x).re : ℂ) := by
    have hv := hr.2.1
    change f x = _ at hv
    rw [hv, Complex.ofReal_re]
  have hεd : ε ≤ d := by
    change ε ≤ a x at hlow
    dsimp only [a, Z] at hlow
    rw [scalarDerivative_re_complex _ hf, he, Complex.ofReal_re] at hlow
    exact hlow
  change ε ≤ (complexDifferential (lgManifold n) f x
    ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm φ) f K) x)).re
  rw [(lgManifold n).complexDifferential_liouvilleVector_rankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ) hf K x hnd hden.ne', he]
  change ε ≤ (((d : ℂ) + (K * π / 2) • f x) / ((1 + K * π : ℝ) : ℂ)).re
  rw [hfx]
  simp only [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_div, Complex.ofReal_re]
  apply (le_div_iff₀ hden).mpr
  change ε ≤ (f x).re / 2 at hval
  have hprod := mul_le_mul_of_nonneg_left hval (mul_nonneg hK hπ)
  dsimp only [π] at hprod ⊢
  nlinarith

end FsFltz
