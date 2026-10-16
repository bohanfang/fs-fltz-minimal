import FsFltz.Analysis.TailoringExhaustionDomain
import FsFltz.Geometry.FlowAbsorption

/-!
# A common normalized base coefficient on compact tailoring domains

Source: `geometric-part-fsf-proof.tex`, the marked-deformation subsection,
lines 1239–1253, using the finite ambient boundary in `subsec:finite`,
lines 1182–1196.
The coefficient is produced from actual native Poisson estimates and the
compact bound for the actual base numerator. No ambient completeness of
the tailored form on all of `Y` is asserted. Compare
`geoemtric-part-fsf.tex`, `sec:junction`, lines 645–654.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold ComplexConjugate Topology
open Set

namespace FsFltz.Geometry

/-- Evaluation of a smooth complex map's native differential on a smooth
native field is continuous. -/
theorem SmoothManifold.continuous_complexDifferential_vectorField
    {d : ℕ} {M : SmoothManifold d} {Z : (x : M.Point) → M.Tangent x}
    (hZ : M.IsSmoothVectorField Z) (f : M.Point → ℂ)
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) :
    Continuous (fun x => complexDifferential M f x (Z x)) := by
  exact ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).continuous.comp
    ((hf.continuous_tangentMap (by simp)).comp hZ.contMDiff_section.continuous)).snd

/-- The native chain rule for the squared norm of an arbitrary smooth
complex map, including the nonholomorphic tailoring maps. -/
theorem SmoothManifold.scalarDerivative_complex_normSq {d : ℕ} (M : SmoothManifold d)
    {f : M.Point → ℂ} (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (x : M.Point) (v : M.Tangent x) :
    M.scalarDerivative (fun y => Complex.normSq (f y)) x v =
      2 * (conj (f x) * complexDifferential M f x v).re := by
  have hd := (hf.mdifferentiableAt (by simp) (x := x)).hasMFDerivAt
  have hr := Complex.reCLM.hasMFDerivAt.comp x hd
  have hi := Complex.imCLM.hasMFDerivAt.comp x hd
  have hs := ((hr.mul hr).add (hi.mul hi)).mfderiv
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y => Complex.normSq (f y)) x = _ at hs
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y => Complex.normSq (f y)) x) v = _
  rw [hs]
  change (f x).re * (complexDifferential M f x v).re +
      (f x).re * (complexDifferential M f x v).re +
      ((f x).im * (complexDifferential M f x v).im +
        (f x).im * (complexDifferential M f x v).im) = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact native base-radius formula for a rank-two updated primitive. -/
theorem SmoothManifold.scalarDerivative_complex_normSq_rankTwoPrimitive
    {d : ℕ} (M : SmoothManifold d) {α : M.Form 1} {f : M.Point → ℂ}
    (hα : M.IsSmoothForm α) (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (K : ℝ) (x : M.Point) (hnd : M.Nondegenerate (M.exteriorDerivative α) x)
    (hden : 1 + K * M.planePairing α f x hnd ≠ 0) :
    M.scalarDerivative (fun y => Complex.normSq (f y)) x
      (M.liouvilleVector (M.rankTwoPrimitive α f K) x) =
      (2 * (conj (f x) * complexDifferential M f x (M.liouvilleVector α x)).re +
        K * M.planePairing α f x hnd * Complex.normSq (f x)) /
          (1 + K * M.planePairing α f x hnd) := by
  rw [M.scalarDerivative_complex_normSq hf,
    M.complexDifferential_liouvilleVector_rankTwoPrimitive hα hf K x hnd hden]
  simp only [Complex.real_smul, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, sub_zero, add_zero, Complex.normSq_apply]
  ring

end FsFltz.Geometry

namespace FsFltz

open Geometry
variable {n : ℕ}

theorem tailoringFamily_affine (I : ToricInput n) (β s : ℝ) (y : LGSpace n) :
    tailoringFamily I β s y = tailoringOriginal I β y +
      s • (tailoringFamily I β 1 y - tailoringOriginal I β y) := by
  simp only [tailoringFamily, Complex.real_smul, Complex.ofReal_mul, one_mul]
  ring

/-- The actual spatial differential retains the affine parameter dependence. -/
theorem complexDifferential_tailoringFamily_affine (I : ToricInput n)
    (β s : ℝ) (y : LGSpace n) (v : (lgManifold n).Tangent y) :
    complexDifferential (lgManifold n) (tailoringFamily I β s) y v =
      complexDifferential (lgManifold n) (tailoringOriginal I β) y v +
        s • (complexDifferential (lgManifold n) (tailoringFamily I β 1) y v -
          complexDifferential (lgManifold n) (tailoringOriginal I β) y v) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have h₀ := (contMDiff_tailoringOriginal_lgManifold I β).mdifferentiableAt (by simp) (x := y)
  have h₁ := (contMDiff_tailoringFamily_lgManifold I β 1).mdifferentiableAt (by simp) (x := y)
  have hd := (h₀.hasMFDerivAt.add ((h₁.hasMFDerivAt.sub h₀.hasMFDerivAt).const_smul s)).mfderiv
  have he : tailoringFamily I β s = fun z => tailoringOriginal I β z +
      s • (tailoringFamily I β 1 z - tailoringOriginal I β z) := by
    funext z
    exact tailoringFamily_affine I β s z
  change Model (2 * n) at v
  change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) (tailoringFamily I β s) y) v = _
  rw [he]
  exact congrArg (fun L : Model (2 * n) →L[ℝ] ℂ => L v) hd

/-- The actual base numerator is continuous jointly in the homotopy
parameter and the spatial point. -/
theorem continuous_tailoringFamily_base_numerator (I : ToricInput n) (β : ℝ)
    {φ : RealSpace n → ℝ} {c : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) :
    Continuous (fun p : ℝ × LGSpace n =>
      2 * (conj (tailoringFamily I β p.1 p.2) *
        complexDifferential (lgManifold n) (tailoringFamily I β p.1) p.2
          ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) p.2)).re) := by
  let Z := (lgManifold n).liouvilleVector (lambdaPotentialForm φ)
  have hZ : (lgManifold n).IsSmoothVectorField Z :=
    (lgManifold n).isSmoothVectorField_liouvilleVector _ (isSmoothForm_lambdaPotentialForm hφ)
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
  have h₀ := (SmoothManifold.continuous_complexDifferential_vectorField hZ
    (tailoringOriginal I β) (contMDiff_tailoringOriginal_lgManifold I β)).comp
      (continuous_snd : Continuous (Prod.snd : ℝ × LGSpace n → LGSpace n))
  have h₁ := (SmoothManifold.continuous_complexDifferential_vectorField hZ
    (tailoringFamily I β 1) (contMDiff_tailoringFamily_lgManifold I β 1)).comp
      (continuous_snd : Continuous (Prod.snd : ℝ × LGSpace n → LGSpace n))
  have hd : Continuous (fun p : ℝ × LGSpace n =>
      complexDifferential (lgManifold n) (tailoringFamily I β p.1) p.2 (Z p.2)) := by
    apply (h₀.add (continuous_fst.smul (h₁.sub h₀))).congr
    intro p
    exact (complexDifferential_tailoringFamily_affine I β p.1 p.2 (Z p.2)).symm
  exact continuous_const.mul (Complex.continuous_re.comp
    ((Complex.continuous_conj.comp (contMDiff_tailoringFamily I β).continuous).mul hd))

/-- On every fixed cylinder the actual normalized tailoring family lies
inside any prescribed positive base radius once the scale is large enough. -/
theorem tailoringFamily_exists_compact_norm_lt_pos (I : ToricInput n) (R : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, ∀ y : LGSpace n,
      Real.sqrt (realSquaredNorm y.1) ≤ R → ‖tailoringFamily I β s y‖ < r := by
  obtain ⟨B, hB, hb⟩ := tailoringFamily_exists_unchanged_compact_differential I R
  obtain ⟨_d, _hd, U, hU, hu⟩ := I.exists_supportHeight_linear_bounds
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  refine ⟨max B (U * R + Real.log (I.vertices.card : ℝ) - Real.log r + 1),
    lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro β hβ s y hy
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  rw [(hb β ((le_max_left _ _).trans hβ) s x hy).1]
  have hheight : supportHeight I (lgCover x).1 ≤ U * R :=
    (hu (lgCover x).1).2.trans (mul_le_mul_of_nonneg_left hy hU.le)
  have hsmall : (I.vertices.card : ℝ) * Real.exp (supportHeight I (lgCover x).1 - β) < r := by
    rw [← Real.exp_log hN, ← Real.exp_add, ← Real.exp_log hr, Real.exp_lt_exp]
    have hh := (le_max_right B (U * R + Real.log (I.vertices.card : ℝ) - Real.log r + 1)).trans hβ
    linarith
  exact (norm_tailoringOriginal_le_card_mul_max I β (lgCover x)).trans_lt hsmall

/-- The lower bound is valid above any fixed positive base radius, allowing
one explicit uniform collar below the unit circle. -/
theorem tailoringFamily_exists_uniform_base_pairing_lowerBound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {r : ℝ} (hr : 0 < r) :
    ∃ d : ℝ, 0 < d ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y,
      r ≤ ‖tailoringFamily I β s y‖ →
      d * Real.exp (-β) ^ 2 / 2 ≤
        (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd := by
  obtain ⟨d, hd, R, _hR, Bπ, hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Bn, _hBn, hnorm⟩ := tailoringFamily_exists_compact_norm_lt_pos I R hr
  obtain ⟨a, ha, _H, _hH, hheight⟩ := I.exists_supportHeight_linear_bounds
  refine ⟨d, hd, max Bπ Bn, lt_of_lt_of_le hBπ (le_max_left _ _), ?_⟩
  intro β hβ s hs y hnd hf
  have hrad : R ≤ Real.sqrt (realSquaredNorm y.1) := by
    by_contra h
    exact not_lt_of_ge hf
      (hnorm β ((le_max_right _ _).trans hβ) s y (le_of_not_ge h))
  have hlo := (hπ β ((le_max_left _ _).trans hβ) s hs y hnd).2.1 hrad
  have hheight₀ : 0 ≤ supportHeight I y.1 :=
    (mul_nonneg ha.le (Real.sqrt_nonneg _)).trans (hheight y.1).1
  have hexp : Real.exp (-β) ≤ Real.exp (supportHeight I y.1 - β) :=
    Real.exp_le_exp.mpr (by linarith)
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hexp 2) hd.le)
    (by norm_num)).trans hlo

/-- The source's unit-circle case of the positive-radius lower bound. -/
theorem tailoringFamily_exists_uniform_unit_base_pairing_lowerBound
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ d : ℝ, 0 < d ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      ∀ hnd : (lgManifold n).Nondegenerate
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) y,
      1 ≤ ‖tailoringFamily I β s y‖ →
      d * Real.exp (-β) ^ 2 / 2 ≤
        (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd :=
  tailoringFamily_exists_uniform_base_pairing_lowerBound I hφ hc hU hlower hupper zero_lt_one

/-- On every actual compact carrier one finite normalized coefficient makes
the native base-radius derivative positive simultaneously for the entire
tailoring interval, and for every increase of that coefficient. -/
theorem tailoringFamily_exists_uniform_compact_base_outwardness_above
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {r : ℝ} (hr : 0 < r) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ C : Set (LGSpace n), IsCompact C →
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ K ≥ Kstar,
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y ∈ C,
      r ≤ ‖tailoringFamily I β s y‖ →
      0 < (lgManifold n).scalarDerivative
        (fun z => Complex.normSq (tailoringFamily I β s z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
  obtain ⟨d, hd, β₀, hβ₀, hπ⟩ :=
    tailoringFamily_exists_uniform_base_pairing_lowerBound I hφ hc hU hlower hupper hr
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ C hC
  let b : ℝ × LGSpace n → ℝ := fun p =>
    2 * (conj (tailoringFamily I β p.1 p.2) *
      complexDifferential (lgManifold n) (tailoringFamily I β p.1) p.2
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) p.2)).re
  have hb : Continuous b := continuous_tailoringFamily_base_numerator I β hφ hc hlower
  obtain ⟨N, hN⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hC).bddAbove_image
    hb.norm.continuousOn
  let p := d * Real.exp (-β) ^ 2 / 2
  have hp : 0 < p := by dsimp [p]; positivity
  let Kstar := (max N 0 + 1) / (p * r ^ 2)
  have hpr : 0 < p * r ^ 2 := mul_pos hp (sq_pos_of_pos hr)
  have hKstar : 0 < Kstar := div_pos (by have := le_max_right N 0; linarith) hpr
  refine ⟨Kstar, hKstar, ?_⟩
  intro K hK s hs y hy hf
  have hKpos : 0 < K := hKstar.trans_le hK
  let hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y
  let π := (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y hnd
  have hpπ : p ≤ π := hπ β hβ s hs y hnd hf
  have hπpos : 0 < π := hp.trans_le hpπ
  have hden : 0 < 1 + K * π := by positivity
  have hbN : -max N 0 ≤ b (s, y) := by
    have h := hN (mem_image_of_mem (fun q => ‖b q‖) (show (s, y) ∈ Icc (0 : ℝ) 1 ×ˢ C from ⟨hs, hy⟩))
    rw [Real.norm_eq_abs] at h
    exact (neg_le_neg (le_max_left N 0)).trans (abs_le.mp h).1
  have hnormSq : r ^ 2 ≤ Complex.normSq (tailoringFamily I β s y) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ hr.le hf 2
  have hpπnorm : p * r ^ 2 ≤ π * Complex.normSq (tailoringFamily I β s y) :=
    mul_le_mul hpπ hnormSq (sq_nonneg _) hπpos.le
  have hKp : max N 0 + 1 ≤ K * (p * r ^ 2) := (div_le_iff₀ hpr).mp hK
  have hKπ : max N 0 + 1 ≤ K * π * Complex.normSq (tailoringFamily I β s y) := by
    simpa only [mul_assoc] using hKp.trans (mul_le_mul_of_nonneg_left hpπnorm hKpos.le)
  rw [(lgManifold n).scalarDerivative_complex_normSq_rankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β s)
    K y hnd hden.ne']
  apply div_pos _ hden
  change 0 < b (s, y) + K * π * Complex.normSq (tailoringFamily I β s y)
  linarith only [hbN, hKπ]

/-- The source's unit-circle case, retained for finite-domain consumers. -/
theorem tailoringFamily_exists_uniform_compact_base_outwardness
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ C : Set (LGSpace n), IsCompact C →
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ K ≥ Kstar,
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y ∈ C,
      1 ≤ ‖tailoringFamily I β s y‖ →
      0 < (lgManifold n).scalarDerivative
        (fun z => Complex.normSq (tailoringFamily I β s z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) :=
  tailoringFamily_exists_uniform_compact_base_outwardness_above I hφ hc hU hlower hupper zero_lt_one

/-- The common normalized base coefficient exists on the literal finite
potential domain for every sufficiently large tailoring scale. The
homogeneous potential end supplies compactness; no positivity threshold
or domain marking is supplied as an input. -/
theorem tailoringFamily_exists_uniform_finite_domain_base_outwardness
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (D : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ K ≥ Kstar,
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      2 * φ y.1 ≤ D ^ 2 * β ^ 2 → 1 ≤ ‖tailoringFamily I β s y‖ →
      0 < (lgManifold n).scalarDerivative
        (fun z => Complex.normSq (tailoringFamily I β s z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y) := by
  obtain ⟨β₀, hβ₀, hb⟩ :=
    tailoringFamily_exists_uniform_compact_base_outwardness I hφ hc hU hlower hupper
  refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
  have hcompact : IsCompact {y : LGSpace n | 2 * φ y.1 ≤ D ^ 2 * β ^ 2} := by
    convert isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hREnd heq
      (D ^ 2 * β ^ 2 / 2) using 1
    ext y
    change (2 * φ y.1 ≤ D ^ 2 * β ^ 2) ↔ (φ y.1 ≤ D ^ 2 * β ^ 2 / 2)
    constructor <;> intro h <;> linarith only [h]
  exact hb β hβ _ hcompact

end FsFltz
