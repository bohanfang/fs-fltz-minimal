import FsFltz.Geometry.PotentialBaseOutward
import FsFltz.Geometry.PotentialAmbientRoundedMotion
import FsFltz.Geometry.TailoringRoundedDomain

/-!
# Uniform outwardness for the holomorphic coefficient/potential rounding

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1049,
the finite coefficient choice, lines 1315–1326, and assembly, lines 2127–2158.
The later common coefficient may also dominate the finite threshold at R/2,
which produces an entire base collar without a new compact gluing argument.
This makes no additional requirement on the supplied original coefficient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance roundedOutwardLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance roundedOutwardLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- The literal diagonal path threshold controls the actual native base
derivative at every far value, uniformly along the whole path. -/
theorem ToricInput.coefficientPath_potentialPath_base_outward
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    let hφE := hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ K : ℝ, coefficientPotentialPathThreshold I hφE hc hlower R ≤ K →
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      R ≤ ‖W (I.alongCoefficientPath t) y‖ →
      0 < (lgManifold n).scalarDerivative
        (fun z => Complex.normSq (W (I.alongCoefficientPath t) z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
          (W (I.alongCoefficientPath t)) K) y) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let hφE := hφ.comp e.contDiff
  obtain ⟨R₀, B, hR₀, _hB, hbound⟩ :=
    I.coefficientPath_potentialPath_threshold_wellDefined hφE hc hlower hupper L
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR K hK t ht y hy
  obtain ⟨hpairs, _hne, hbdd, _hK0, _hupper⟩ := hbound R hR
  obtain ⟨_hpairne, hpairbdd, hpoints, hκpos, _hκupper⟩ := hpairs t ht t ht
  have hκpath : potentialPathThreshold I hφE hc hlower t t ht R ≤
      coefficientPotentialPathThreshold I hφE hc hlower R :=
    le_csSup hbdd ⟨t, ht, rfl⟩
  have hKnonneg : 0 ≤ K := zero_le_one.trans (hκpos.trans (hκpath.trans hK))
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨hx, ha⟩ := hpoints (lgCover x) hy
  let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ t
  have hψ : ContDiff ℝ ∞ ψ := potentialPath_native_contDiff hφ t
  have hψeq : potentialPath (fun z => ‖z‖ ^ 2 / 2) (φ ∘ e) t ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm = ψ := by
    funext u
    change (1 - t) * (‖e.symm u‖ ^ 2 / 2) + t * φ (e (e.symm u)) =
      (1 - t) * (realSquaredNorm u / 2) + t * φ u
    rw [e.apply_symm_apply]
    congr 2
    simp [e, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hnorm : Real.sqrt (realSquaredNorm x.1) =
      ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n)))]
    congr 1
    simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hxend : L < ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
    simpa only [lgCover, hnorm] using hx
  have hEuler := coordinateHessian_apply_self_on_homogeneous_end hψ
    (potentialPath_native_end_contDiffAt hEnd t) (potentialPath_native_end_homogeneous hhom t)
    hL (potentialPath_native_eq_end hend t) hxend
  have hbase := potentialPathThreshold_native_baseoutward I hφE hc hlower t t ht hRpos
    hpairbdd (hκpath.trans hK) hKnonneg x hy ha (by
      simpa only [hψeq] using hEuler)
  simpa only [hψeq] using hbase.1.trans_le hbase.2

/-- The native spatial chain rule for the exact unnormalized path scalar. -/
theorem scalarDerivative_potentialPath_roundedDefiningFunction
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (t R A : ℝ) (m : RoundingChoice) (y : LGSpace n) (v : (lgManifold n).Tangent y) :
    (lgManifold n).scalarDerivative
      (fun z => potentialPath_roundedDefiningFunction I φ R A m (t, z)) y v =
      fderiv ℝ m.profile.toFun
        (potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 - A,
          Complex.normSq (W (I.alongCoefficientPath t) y) - R ^ 2)
        ((lgManifold n).scalarDerivative
            (fun z => potentialPath (fun u => realSquaredNorm u / 2) φ t z.1) y v,
          (lgManifold n).scalarDerivative
            (fun z => Complex.normSq (W (I.alongCoefficientPath t) z)) y v) := by
  change Model (2 * n) at v
  let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ t
  let J := I.alongCoefficientPath t
  have hp := (contMDiff_potentialValue (potentialPath_native_contDiff hφ t)).mdifferentiable
    (by simp) y
  have hw := (contMDiff_original_absWSq J).mdifferentiable (by simp) y
  have hp' := hp.sub (mdifferentiableAt_const (c := A))
  have hw' := hw.sub (mdifferentiableAt_const (c := R ^ 2))
  have hm := m.profile.smooth.contMDiff.mdifferentiable (by simp)
    (ψ y.1 - A, Complex.normSq (W J y) - R ^ 2)
  have hpair : HasMFDerivAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ × ℝ)
      (fun z => (ψ z.1 - A, Complex.normSq (W J z) - R ^ 2)) y
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => ψ z.1 - A) y).prod
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z : LGSpace n => Complex.normSq (W J z) - R ^ 2) y)) :=
    ⟨(hp'.prodMk_space hw').continuousAt, hp'.hasMFDerivAt.2.prodMk hw'.hasMFDerivAt.2⟩
  change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (m.profile.toFun ∘ fun z : LGSpace n =>
        (ψ z.1 - A, Complex.normSq (W J z) - R ^ 2)) y) v =
    fderiv ℝ m.profile.toFun (ψ y.1 - A, Complex.normSq (W J y) - R ^ 2)
      ((mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun z : LGSpace n => ψ z.1) y) v,
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun z : LGSpace n => Complex.normSq (W J z)) y) v)
  erw [mfderiv_comp_apply y hm (hp'.prodMk_space hw') v, mfderiv_eq_fderiv,
    hpair.mfderiv, mfderiv_sub hp mdifferentiableAt_const,
    mfderiv_sub hw mdifferentiableAt_const]
  simp only [mfderiv_const, sub_zero]
  rfl

/-- One coefficient and one width make the literal rounded defining
function outward on its entire nonnegative region at every path parameter.
Only the freely chosen later coefficient is enlarged to control R/2. -/
theorem ToricInput.coefficientPath_potentialPath_rounded_outward
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    let hφE := hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
    ∃ A₀ R₀ : ℝ, 0 < A₀ ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ Kstar : ℝ, 0 < Kstar ∧
      coefficientPotentialPathThreshold I hφE hc hlower R ≤ Kstar ∧
      ∀ A : ℝ, 2 * A₀ ≤ A → ∀ Aminus : ℝ, Aminus < A →
      ∃ δ : ℝ, 0 < δ ∧ δ < A - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K : ℝ, Kstar ≤ K → ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ∀ y : LGSpace n, 0 ≤ potentialPath_roundedDefiningFunction I φ R A m (t, y) →
      0 < (lgManifold n).scalarDerivative
        (fun z => potentialPath_roundedDefiningFunction I φ R A m (t, z)) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
          (W (I.alongCoefficientPath t)) K) y) := by
  let hφE := hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
  obtain ⟨A₀, hA₀, hpotential⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_ambient_outward
      hφ hEnd hhom hc hlower hupper hL hend I
  obtain ⟨Rbase, hRbase, hbase⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_base_outward
      I hφ hc hlower hupper hEnd hhom hL hend
  refine ⟨A₀, 2 * Rbase, hA₀, by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := (by positivity : 0 < 2 * Rbase).trans_le hR
  have hRhalf : Rbase ≤ R / 2 := by linarith
  let Kstar := max 1 (max (coefficientPotentialPathThreshold I hφE hc hlower R)
    (coefficientPotentialPathThreshold I hφE hc hlower (R / 2)))
  have hKstar : 0 < Kstar := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨Kstar, hKstar, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro A hA Aminus hgap
  have hApos : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 2) hA₀).trans_le hA
  let δ := min (A / 4) (min (R ^ 2 / 4) ((A - Aminus) / 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδA : δ ≤ A / 4 := min_le_left _ _
  have hδR : δ ≤ R ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδgap : δ < A - Aminus := by
    have hδle : δ ≤ (A - Aminus) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK t ht y hq
  have hKnonneg : 0 ≤ K := hKstar.le.trans hK
  rw [scalarDerivative_potentialPath_roundedDefiningFunction I hφ]
  apply m.profile.fderiv_pos_of_active
  · intro hp
    have hc := m.profile.first_ge_neg_two_eps_of_nonneg_of_partial_pos hm _ hq hp
    apply hpotential t ht t ht K hKnonneg y
    change -2 * m.eps ≤ potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 - A at hc
    have heps := hmd.trans hδA
    linarith
  · intro hp
    have hc := m.profile.second_ge_neg_two_eps_of_nonneg_of_partial_pos hm _ hq hp
    apply hbase (R / 2) hRhalf K
      (((le_max_right _ _).trans (le_max_right _ _)).trans hK) t ht y
    change -2 * m.eps ≤ Complex.normSq (W (I.alongCoefficientPath t) y) - R ^ 2 at hc
    rw [Complex.normSq_eq_norm_sq] at hc
    have heps := hmd.trans hδR
    nlinarith [norm_nonneg (W (I.alongCoefficientPath t) y)]

end FsFltz.Geometry
