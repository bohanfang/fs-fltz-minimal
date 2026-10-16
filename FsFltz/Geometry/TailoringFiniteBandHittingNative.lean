import FsFltz.Geometry.TailoringFiniteBandHittingRadial
import FsFltz.Geometry.TailoringFiniteBandHittingSmooth

/-!
# Finite hitting for the actual tailored ambient field

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1802–1817.
The quantitative speed is proved from the actual tailored function and
rank-two primitive. An auxiliary smooth action is required to solve that
field until it reaches the chosen base level and to retain the explicit
outward cone band on that interval. These are analytic ODE and confinement
hypotheses, not assumed hitting times or core/boundary bijections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ContDiff Manifold
open Set Filter

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance finiteBandHittingNativeChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance finiteBandHittingNativeIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Each orbit of the actual endpoint field reaches a prescribed finite
base level in uniformly bounded positive time. Only the native ODE and
literal band retention are supplied; the hit itself is constructed. -/
theorem tailoringEndpoint_exists_uniform_finite_base_hits
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
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ M : ℝ, 1 < M →
      ∃ ε : ℝ, 0 < ε ∧
      ∀ F : Flow ℝ (ℝ × LGSpace n),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) →
      ∀ K : ℝ, 0 ≤ K → ∀ y ∈ tailoringCoreSection I φEnd β,
        (∀ t : ℝ, 0 ≤ t → (tailoringFamily I β 1 (F t (K, y)).2).re ≤ M →
          (F t (K, y)).2 ∈ tailoringLegendreConic I φEnd ∧
            1 ≤ (tailoringFamily I β 1 (F t (K, y)).2).re) →
        (∀ t : ℝ, 0 ≤ t → (tailoringFamily I β 1 (F t (K, y)).2).re ≤ M →
          HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n))
            (fun s => (F s (K, y)).2) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
                (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (F t (K, y)).2))) →
        ∃ t ∈ Ioc (0 : ℝ) (M / ε), (tailoringFamily I β 1 (F t (K, y)).2).re = M := by
  obtain ⟨Ba, hBa, hmargin⟩ := tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦ hΦ₀ hR heq
  refine ⟨Ba, hBa, ?_⟩
  intro β hβ M hM
  obtain ⟨ε, hε, hm⟩ := hmargin β hβ M
  refine ⟨ε, hε, ?_⟩
  intro F hF K hK y hy hconf hode
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let f := tailoringFamily I β 1
  have hf := contMDiff_tailoringFamily_lgManifold I β 1
  let g : ℝ → ℝ := fun t => (f (F t (K, y)).2).re
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n)) ∞
      (fun t => (F t (K, y)).2) :=
    (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd
  have hg : Differentiable ℝ g :=
    ((Complex.reCLM.contMDiff.comp (hf.comp hcurve)).contDiff).differentiable (by simp)
  have hgzero : g 0 = 1 := by
    have he : tailoringFamily I β 1 y = 1 := hy.2
    simp only [g, f, Flow.map_zero_apply, he, Complex.one_re]
  have hspeed : ∀ t ∈ Ioo (0 : ℝ) ((M - g 0 + 1) / ε),
      g t ≤ M → ε ≤ deriv g t := by
    intro t ht hgt
    obtain ⟨hcone, hlow⟩ := hconf t ht.1.le hgt
    have hlocal := hode t ht.1.le hgt
    have hd := (hasMFDerivAt_iff_hasFDerivAt.mp
      ((hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hlocal))
    have hgd := (Complex.reCLM.hasFDerivAt.comp t hd).hasDerivAt
    have he : deriv g t = (complexDifferential (lgManifold n) f (F t (K, y)).2
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) f K) (F t (K, y)).2)).re := by
      have hgd' : HasDerivAt g _ t := hgd
      rw [hgd'.deriv]
      change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) f (F t (K, y)).2
        ((1 : ℝ) • _)).re = _
      rw [one_smul]
      rfl
    rw [he]
    exact hm _ hcone hlow hgt K hK
  obtain ⟨t, ht, he⟩ := exists_pos_time_scalar_eq_of_lower_speed hg hε
    (by rw [hgzero]; exact hM) hspeed
  refine ⟨t, ?_, he⟩
  simpa only [hgzero, sub_add_cancel] using ht

/-- At an actual native transverse hit, coefficient and logarithmic
initial-point coordinates have one open smooth hitting-time neighborhood.
The resulting map is the literal spatial component of the same action. -/
theorem tailoringEndpoint_exists_smooth_hitting_time_logCoordinates
    (I : ToricInput n) (β : ℝ) (φ : RealSpace n → ℝ)
    (F : Flow ℝ (ℝ × LGSpace n))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2))
    (K t M : ℝ) (x : TangentCoordinates n)
    (hhit : (tailoringFamily I β 1 (F t (K, lgCover x)).2).re = M)
    (hode : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n))
      (fun s => (F s (K, lgCover x)).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (F t (K, lgCover x)).2)))
    (htrans : (complexDifferential (lgManifold n) (tailoringFamily I β 1)
      (F t (K, lgCover x)).2
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (F t (K, lgCover x)).2)).re ≠ 0) :
    ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (K, x) ∈ V ∧
      ∃ τ : ℝ × TangentCoordinates n → ℝ,
        ContDiffOn ℝ ∞ τ V ∧ τ (K, x) = t ∧
        (∀ p ∈ V, (tailoringFamily I β 1 (F (τ p) (p.1, lgCover p.2)).2).re = M) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
          (fun p => (F (τ p) (p.1, lgCover p.2)).2) V := by
  let f := tailoringFamily I β 1
  have hf := contMDiff_tailoringFamily_lgManifold I β 1
  let H : (ℝ × TangentCoordinates n) × ℝ → ℝ :=
    fun p => (f (F p.2 (p.1.1, lgCover p.1.2)).2).re
  have hcoords : ContMDiff 𝓘(ℝ, (ℝ × TangentCoordinates n) × ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))) ∞
      (fun p : (ℝ × TangentCoordinates n) × ℝ => (p.2, (p.1.1, lgCover p.1.2))) :=
    contDiff_snd.contMDiff.prodMk
      (contDiff_fst.fst.contMDiff.prodMk
        ((contMDiff_lgCover n).comp contDiff_fst.snd.contMDiff))
  have hH : ContDiff ℝ ∞ H :=
    (Complex.reCLM.contMDiff.comp (hf.comp (hF.comp hcoords).snd)).contDiff
  have hd := hasMFDerivAt_iff_hasFDerivAt.mp
    ((hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hode)
  have hder : HasDerivAt (fun s => H ((K, x), s))
      (complexDifferential (lgManifold n) f (F t (K, lgCover x)).2
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) f K) (F t (K, lgCover x)).2)).re t := by
    convert (Complex.reCLM.hasFDerivAt.comp t hd).hasDerivAt using 1
    · funext s
      rfl
    · change _ = (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) f (F t (K, lgCover x)).2
        ((1 : ℝ) • _)).re
      rw [one_smul]
      rfl
  have hhitH : H ((K, x), t) = M := hhit
  have htransH : (deriv (fun s => H ((K, x), s)) t) ≠ 0 := by
    rw [hder.deriv]
    exact htrans
  have hderH : DifferentiableAt ℝ (fun s => H ((K, x), s)) t :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) t
  obtain ⟨V, hV, hxV, τ, hτ, hτx, hτhit⟩ :=
    exists_smooth_hitting_time_neighborhood (H := H) (p := (K, x))
      hH hhitH (hderH.hasDerivAt) htransH
  refine ⟨V, hV, hxV, τ, hτ, hτx, hτhit, ?_⟩
  have hτM : ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, ℝ) ∞ τ V :=
    contMDiffOn_iff_contDiffOn.mpr hτ
  have hp : ContMDiff 𝓘(ℝ, ℝ × TangentCoordinates n)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × TangentCoordinates n => (p.1, lgCover p.2)) :=
    contDiff_fst.contMDiff.prodMk ((contMDiff_lgCover n).comp contDiff_snd.contMDiff)
  intro p hpV
  exact (hF.comp_contMDiffOn (hτM.prodMk hp.contMDiffOn) p hpV).snd

end FsFltz
