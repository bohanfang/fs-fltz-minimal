import FsFltz.Geometry.TailoringFiniteBandHittingNative
import FsFltz.Geometry.TailoringAmbientConormalFlowForward

/-!
# Finite base hitting from the actual core

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1799–1817.
The forward native ODE producer supplies all cone and lower-base
retention. The positive band speed then constructs the finite hit,
and strict increase of the actual base coordinate proves uniqueness.
A jointly smooth action solving the native equation at all forward
times remains an explicit analytic hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology ContDiff Manifold
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance finiteBandHittingCoreChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance finiteBandHittingCoreIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- Actual forward integral curves from the core have a unique finite
base-level hit. No cone, ray, or lower-base retention premise is supplied. -/
theorem tailoringEndpoint_exists_uniform_ambient_core_finite_base_hits
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ M : ℝ, 1 < M →
      ∃ ε : ℝ, 0 < ε ∧
      ∀ F : Flow ℝ (ℝ × LGSpace n),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) →
      ∀ K : ℝ, 0 ≤ K → ∀ y ∈ tailoringCoreSection I φEnd β,
        (∀ t : ℝ, 0 ≤ t → IsMIntegralCurveAt (fun s => (F s (K, y)).2)
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        ∃ t ∈ Ioc (0 : ℝ) (M / ε),
          (tailoringFamily I β 1 (F t (K, y)).2).re = M ∧
          (F t (K, y)).2 ∈ tailoringLegendreConic I φEnd ∧
          ∀ s : ℝ, 0 ≤ s → (tailoringFamily I β 1 (F s (K, y)).2).re = M → s = t := by
  obtain ⟨Bh, hBh, hhit⟩ := tailoringEndpoint_exists_uniform_finite_base_hits
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hR heq
  obtain ⟨Bf, hBf, hforward⟩ := tailoringEndpoint_exists_uniform_ambient_core_forward
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  refine ⟨max Bh Bf, lt_of_lt_of_le hBh (le_max_left _ _), ?_⟩
  intro β hβ M hM
  obtain ⟨ε, hε, hh⟩ := hhit β (le_trans (le_max_left _ _) hβ) M hM
  refine ⟨ε, hε, ?_⟩
  intro F hF K hK y hy hγ
  have hstart : (F 0 (K, y)).2 ∈ tailoringCoreSection I φEnd β := by
    simpa only [Flow.map_zero_apply] using hy
  have hr := hforward β (le_trans (le_max_right _ _) hβ) K hK
    (fun s => (F s (K, y)).2) 0 hγ hstart
  obtain ⟨t, ht, he⟩ := hh F hF K hK y hy
    (fun s hs _ => ⟨(hr.1 s hs).1, (hr.1 s hs).2.2⟩)
    (fun s hs _ => (hγ s hs).hasMFDerivAt)
  refine ⟨t, ht, he, (hr.1 t ht.1.le).1, ?_⟩
  intro s hs he'
  exact hr.2.2.injOn (mem_Ici.mpr hs) (mem_Ici.mpr ht.1.le) (he'.trans he.symm)

/-- The finite actual core hit has a smooth coefficient and logarithmic
initial-point neighborhood, and its literal spatial hitting map is smooth.
The hit and transversality are both constructed from the native producers. -/
theorem tailoringEndpoint_exists_uniform_ambient_core_finite_smooth_base_hits
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ M : ℝ, 1 < M →
      ∃ ε : ℝ, 0 < ε ∧
      ∀ F : Flow ℝ (ℝ × LGSpace n),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) →
      ∀ K : ℝ, 0 ≤ K → ∀ x : TangentCoordinates n,
        lgCover x ∈ tailoringCoreSection I φEnd β →
        (∀ t : ℝ, 0 ≤ t → IsMIntegralCurveAt (fun s => (F s (K, lgCover x)).2)
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        ∃ t ∈ Ioc (0 : ℝ) (M / ε),
          (tailoringFamily I β 1 (F t (K, lgCover x)).2).re = M ∧
          (∀ s : ℝ, 0 ≤ s → (tailoringFamily I β 1 (F s (K, lgCover x)).2).re = M → s = t) ∧
          ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (K, x) ∈ V ∧
            ∃ τ : ℝ × TangentCoordinates n → ℝ,
              ContDiffOn ℝ ∞ τ V ∧ τ (K, x) = t ∧
              (∀ p ∈ V, (tailoringFamily I β 1 (F (τ p) (p.1, lgCover p.2)).2).re = M) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
                (fun p => (F (τ p) (p.1, lgCover p.2)).2) V := by
  obtain ⟨Bc, hBc, hcore⟩ := tailoringEndpoint_exists_uniform_ambient_core_finite_base_hits
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bm, hBm, hmargin⟩ := tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hR heq
  refine ⟨max Bc Bm, lt_of_lt_of_le hBc (le_max_left _ _), ?_⟩
  intro β hβ M hM
  obtain ⟨ε, hε, hhit⟩ := hcore β (le_trans (le_max_left _ _) hβ) M hM
  obtain ⟨δ, hδ, hm⟩ := hmargin β (le_trans (le_max_right _ _) hβ) M
  refine ⟨ε, hε, ?_⟩
  intro F hF K hK x hx hγ
  obtain ⟨t, ht, he, hcone, hu⟩ := hhit F hF K hK (lgCover x) hx hγ
  have hpos : 0 < (complexDifferential (lgManifold n) (tailoringFamily I β 1)
      (F t (K, lgCover x)).2
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (F t (K, lgCover x)).2)).re :=
    lt_of_lt_of_le hδ (hm _ hcone (le_trans hM.le he.ge) he.le K hK)
  obtain ⟨V, hV, hxV, τ, hτ, hτx, hτhit, hmap⟩ :=
    tailoringEndpoint_exists_smooth_hitting_time_logCoordinates I β φ F hF K t M x he
      (hγ t ht.1.le).hasMFDerivAt (ne_of_gt hpos)
  exact ⟨t, ht, he, hu, V, hV, hxV, τ, hτ, hτx, hτhit, hmap⟩

end FsFltz
