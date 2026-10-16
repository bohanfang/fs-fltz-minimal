import FsFltz.Geometry.TailoringOuterBoundaryHitting
import FsFltz.Geometry.TailoringFiniteBandHittingSmooth

/-!
# Smooth times and maps at the actual potential boundary

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775,
and `prop:band`, lines 1778–1817. The target is the literal potential
level, not a base-coordinate level. Native agreement is needed only
near the constructed hit; the coefficient and logarithmic initial
coordinates have one genuine open neighborhood of smooth hitting times.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

local instance outerBoundaryHittingSmoothChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance outerBoundaryHittingSmoothIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- A native transverse potential hit constructs a time and its literal
spatial map smooth on one actual open coefficient/logarithmic neighborhood. -/
theorem tailoringEndpoint_exists_smooth_outer_hitting_time_logCoordinates
    (I : ToricInput n) (β : ℝ) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (F : Flow ℝ (ℝ × LGSpace n))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2))
    (K t A : ℝ) (x : TangentCoordinates n)
    (hhit : φ (F t (K, lgCover x)).2.1 = A)
    (hode : IsMIntegralCurveAt (fun s => (F s (K, lgCover x)).2)
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t)
    (htrans : (lgManifold n).scalarDerivative (fun z => φ z.1 - A)
      (F t (K, lgCover x)).2
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K)
        (F t (K, lgCover x)).2) ≠ 0) :
    ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (K, x) ∈ V ∧
      ∃ τ : ℝ × TangentCoordinates n → ℝ,
        ContDiffOn ℝ ∞ τ V ∧ τ (K, x) = t ∧
        (∀ p ∈ V, φ (F (τ p) (p.1, lgCover p.2)).2.1 = A) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
          (fun p => (F (τ p) (p.1, lgCover p.2)).2) V := by
  let ρ : LGSpace n → ℝ := fun z => φ z.1 - A
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_potentialValue hφ).sub contMDiff_const
  let H : (ℝ × TangentCoordinates n) × ℝ → ℝ :=
    fun p => ρ (F p.2 (p.1.1, lgCover p.1.2)).2
  have hcoords : ContMDiff 𝓘(ℝ, (ℝ × TangentCoordinates n) × ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))) ∞
      (fun p : (ℝ × TangentCoordinates n) × ℝ => (p.2, (p.1.1, lgCover p.1.2))) :=
    contDiff_snd.contMDiff.prodMk
      (contDiff_fst.fst.contMDiff.prodMk
        ((contMDiff_lgCover n).comp contDiff_fst.snd.contMDiff))
  have hH : ContDiff ℝ ∞ H :=
    (hρ.comp (hF.comp hcoords).snd).contDiff
  have hd := hasDerivAt_scalar_of_isMIntegralCurveAt (lgManifold n) hρ hode
  have hhitH : H ((K, x), t) = 0 := sub_eq_zero.mpr hhit
  obtain ⟨V, hV, hxV, τ, hτ, hτx, hτhit⟩ :=
    exists_smooth_hitting_time_neighborhood (H := H) (p := (K, x))
      hH hhitH hd htrans
  refine ⟨V, hV, hxV, τ, hτ, hτx, ?_, ?_⟩
  · intro p hp
    exact sub_eq_zero.mp (hτhit p hp)
  · have hτM : ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, ℝ) ∞ τ V :=
      contMDiffOn_iff_contDiffOn.mpr hτ
    have hp : ContMDiff 𝓘(ℝ, ℝ × TangentCoordinates n)
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
        (fun p : ℝ × TangentCoordinates n => (p.1, lgCover p.2)) :=
      contDiff_fst.contMDiff.prodMk ((contMDiff_lgCover n).comp contDiff_snd.contMDiff)
    intro p hpV
    exact (hF.comp_contMDiffOn (hτM.prodMk hp.contMDiffOn) p hpV).snd

/-- The actual regional native flow and boundary outwardness construct
the finite unique hit, transversality, and its open smooth time/map
neighborhood. Only native agreement inside the literal compact sublevel
is required; all-forward native dynamics is not an input. -/
theorem tailoringEndpoint_exists_uniform_core_outer_boundary_smooth_hits
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B,
      ∀ F : Flow ℝ (ℝ × LGSpace n),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) →
      ∀ K : ℝ, 0 ≤ K →
        (∀ y t, φ (F t (K, y)).2.1 ≤ D ^ 2 * β ^ 2 / 2 →
          IsMIntegralCurveAt (fun s => (F s (K, y)).2)
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
      ∀ x : TangentCoordinates n, lgCover x ∈ tailoringCoreSection I φEnd β →
        φ (lgCover x).1 < D ^ 2 * β ^ 2 / 2 →
        ∃ t : ℝ, 0 < t ∧ φ (F t (K, lgCover x)).2.1 = D ^ 2 * β ^ 2 / 2 ∧
          (∀ s, φ (F s (K, lgCover x)).2.1 = D ^ 2 * β ^ 2 / 2 → s = t) ∧
          ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (K, x) ∈ V ∧
            ∃ τ : ℝ × TangentCoordinates n → ℝ,
              ContDiffOn ℝ ∞ τ V ∧ τ (K, x) = t ∧
              (∀ p ∈ V, φ (F (τ p) (p.1, lgCover p.2)).2.1 = D ^ 2 * β ^ 2 / 2) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
                (fun p => (F (τ p) (p.1, lgCover p.2)).2) V := by
  obtain ⟨Bh, hBh, hhit⟩ := tailoringEndpoint_exists_uniform_core_outer_boundary_hits
    I hφ hc hU hlower hupper hEnd1 hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq hD
  obtain ⟨Bd, _, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd.smooth hEnd.homogeneous hR heq hD
  refine ⟨max Bh Bd, hBh.trans_le (le_max_left _ _), ?_⟩
  intro β hβ F hF K hK hode x hx hinside
  obtain ⟨t, ht, he, hu, _⟩ := hhit β ((le_max_left _ _).trans hβ)
    F hF K hK hode (lgCover x) hx hinside
  obtain ⟨_, _, hboundary⟩ := hdata β ((le_max_right _ _).trans hβ)
  have htrans := (hboundary 1 (by simp) K hK).2
    (F t (K, lgCover x)).2 (sub_eq_zero.mpr he)
  obtain ⟨V, hV, hxV, τ, hτ, hτx, hτhit, hmap⟩ :=
    tailoringEndpoint_exists_smooth_outer_hitting_time_logCoordinates I β hφ F hF K t
      (D ^ 2 * β ^ 2 / 2) x he (hode (lgCover x) t he.le) htrans.ne'
  exact ⟨t, ht, he, hu, V, hV, hxV, τ, hτ, hτx, hτhit, hmap⟩

end FsFltz
