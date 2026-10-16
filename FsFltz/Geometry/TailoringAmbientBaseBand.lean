import FsFltz.Geometry.TailoringAmbientBandMargin

/-!
# Compactness and positive base speed in actual finite cone bands

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1802–1816.
The band is cut out by the actual endpoint function, rather than by an
assumed upper bound on the outward radial parameter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz
open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology ContDiff Manifold
variable {n : ℕ}

theorem IsStronglyCompatibleEndPotential.eventually_outward_base_band_parameter_bound
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd) :
    ∀ᶠ β in atTop, ∀ y ∈ tailoringCoreSection I φEnd β,
      ∀ t : ℝ, 1 ≤ t → ∀ M : ℝ,
        (tailoringFamily I β 1 (t • y.1, y.2)).re ≤ M →
        t ≤ β + max M 0 := by
  filter_upwards [hEnd.eventually_coreSection_eq_radial,
    hEnd.eventually_coreSection_outward_ray,
    eventually_ge_atTop (Real.log (I.vertices.card : ℝ) + 1)] with β heq hray hβ
  intro y hy t ht M hM
  have hyreal : tailoringRadialFunction I β y.1 = 1 := by
    rw [heq] at hy
    exact hy.2
  have hh : 1 ≤ supportHeight I y.1 := by
    linarith [(tailoringRadialFunction_height_bounds I β hyreal).1]
  have hth : t ≤ supportHeight I (t • y.1) := by
    rw [I.supportHeight_smul_of_nonneg (by linarith : 0 ≤ t)]
    nlinarith
  have hv : tailoringRadialFunction I β (t • y.1) ≤ M := by
    rw [(hray y hy t ht).2.1, Complex.ofReal_re] at hM
    exact hM
  by_cases hg : β - Real.sqrt β ≤ supportHeight I (t • y.1)
  · have he := tailoringRadialFunction_max_term_lower I β (t • y.1) hg
    have hex := Real.add_one_le_exp (supportHeight I (t • y.1) - β)
    have hm := le_max_left M 0
    linarith
  · have hm := le_max_right M 0
    have hs := Real.sqrt_nonneg β
    linarith

/-- The literal outward cone restricted to a finite base interval is compact. -/
theorem IsStronglyCompatibleEndPotential.eventually_outward_finite_base_band_compact
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0) :
    ∀ᶠ β in atTop, ∀ M : ℝ,
      IsCompact {x : LGSpace n | ∃ y ∈ tailoringCoreSection I φEnd β,
        ∃ t : ℝ, 1 ≤ t ∧ x = (t • y.1, y.2) ∧ (tailoringFamily I β 1 x).re ≤ M} := by
  filter_upwards [hEnd.eventually_outward_base_band_parameter_bound,
    hEnd.eventually_coreSection_compact Φ hΦ hΦ₀] with β hbound hcompact
  intro M
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let ray : ℝ × LGSpace n → LGSpace n := fun p => (p.1 • p.2.1, p.2.2)
  have hrc : Continuous ray := (continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd
  have hf : Continuous (fun p : ℝ × LGSpace n => (tailoringFamily I β 1 (ray p)).re) :=
    Complex.continuous_re.comp ((contMDiff_tailoringFamily_lgManifold I β 1).continuous.comp hrc)
  have hs := ((isCompact_Icc (a := (1 : ℝ)) (b := β + max M 0)).prod hcompact).inter_right
    (isClosed_le hf (continuous_const (y := M)))
  have he : {x : LGSpace n | ∃ y ∈ tailoringCoreSection I φEnd β,
      ∃ t : ℝ, 1 ≤ t ∧ x = (t • y.1, y.2) ∧ (tailoringFamily I β 1 x).re ≤ M} =
      ray '' ((Icc (1 : ℝ) (β + max M 0) ×ˢ tailoringCoreSection I φEnd β) ∩
        {p | (tailoringFamily I β 1 (ray p)).re ≤ M}) := by
    ext x
    constructor
    · rintro ⟨y, hy, t, ht, rfl, hM⟩
      exact ⟨(t, y), ⟨⟨⟨ht, hbound y hy t ht M hM⟩, hy⟩, hM⟩, rfl⟩
    · rintro ⟨⟨t, y⟩, ⟨⟨ht, hy⟩, hM⟩, rfl⟩
      exact ⟨y, hy, t, ht.1, rfl, hM⟩
  rw [he]
  exact hs.image hrc

/-- A finite bound on the actual base value supplies a positive speed bound
for every nonnegative coefficient, without a radial-parameter assumption. -/
theorem tailoringEndpoint_exists_uniform_finite_base_band_margin
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ tailoringCoreSection I φEnd β, ∀ t : ℝ, 1 ≤ t →
        (tailoringFamily I β 1 (t • y.1, y.2)).re ≤ M →
        ∀ K : ℝ, 0 ≤ K → ε ≤
          (complexDifferential (lgManifold n) (tailoringFamily I β 1) (t • y.1, y.2)
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (t • y.1, y.2))).re := by
  obtain ⟨Ba, hBa, hmargin⟩ := tailoringEndpoint_exists_uniform_outward_band_base_margin
    I hφ hc hU hlower hupper hEnd Φ hΦ hΦ₀ hR heq
  obtain ⟨Br, hrad⟩ := eventually_atTop.mp hEnd.eventually_outward_base_band_parameter_bound
  refine ⟨max Ba Br, hBa.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M
  obtain ⟨ε, hε, hm⟩ := hmargin β ((le_max_left _ _).trans hβ) (β + max M 0)
  refine ⟨ε, hε, ?_⟩
  intro y hy t ht hM K hK
  exact hm y hy t ⟨ht, hrad β ((le_max_right _ _).trans hβ) y hy t ht M hM⟩ K hK

end FsFltz
