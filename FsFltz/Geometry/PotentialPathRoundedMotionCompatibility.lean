import FsFltz.Geometry.PotentialPathRoundedMotion
import FsFltz.Geometry.TailoringRoundedMarkedLift

/-!
# The unchanged holomorphic rounded face along the full ribbon

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 996–1009.
The strict potential-level gap gives an actual joint open germ along every
point of the full truncated fiber. On this germ, the fiber derivative
equations imply the rounded ambient boundary equation. No simultaneous
fiber lift or global pair transport is assumed to exist.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance roundedCompatLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance roundedCompatLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth
local instance roundedCompatProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance roundedCompatProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- The whole truncated holomorphic fiber has an actual joint open germ
of the unrounded base face, for the literal moving potential. -/
theorem potentialPath_roundedDefiningFunction_exists_unrounded_germ
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (R A Aminus : ℝ) (m : RoundingChoice) (heps : 0 < m.eps)
    (hgap : Aminus < A - m.eps) (t : ℝ) (y : LGSpace n)
    (hf : W (I.alongCoefficientPath t) y = (R : ℂ))
    (hy : potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 ≤ Aminus) :
    ∃ O : Set (ℝ × LGSpace n), IsOpen O ∧ (t, y) ∈ O ∧
      ∀ p ∈ O, potentialPath_roundedDefiningFunction I φ R A m p =
        Complex.normSq (W (I.alongCoefficientPath p.1) p.2) - R ^ 2 := by
  let x : ℝ × LGSpace n → ℝ := fun p =>
    potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1 - A
  let z : ℝ × LGSpace n → ℝ := fun p =>
    Complex.normSq (W (I.alongCoefficientPath p.1) p.2) - R ^ 2
  have hx : Continuous x := by
    have hpath : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × LGSpace n =>
          potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1) :=
      ((contMDiff_const.sub contMDiff_fst).mul
        (contMDiff_original_phi0.comp contMDiff_snd)).add
        (contMDiff_fst.mul ((contMDiff_potentialValue hφ).comp contMDiff_snd))
    exact hpath.continuous.sub continuous_const
  have hz : Continuous z :=
    (Complex.continuous_normSq.comp
      (contMDiff_coefficientPath_W_native_joint I).continuous).sub continuous_const
  let O : Set (ℝ × LGSpace n) := {p | m.eps < z p - x p}
  have hO : IsOpen O := isOpen_lt continuous_const (hz.sub hx)
  refine ⟨O, hO, ?_, ?_⟩
  · change m.eps < (Complex.normSq (W (I.alongCoefficientPath t) y) - R ^ 2) -
      (potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 - A)
    rw [hf, Complex.normSq_ofReal]
    nlinarith
  · intro p hp
    change m.eps < z p - x p at hp
    have hle : x p ≤ z p := by linarith
    have hexact := m.profile.exact_away (x p, z p) (by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith)
    exact hexact.trans (max_eq_right hle)

/-- Every point of the full literal truncated holomorphic fiber belongs
to the actual rounded zero face. -/
theorem potentialPath_roundedDefiningFunction_eq_zero_on_truncated_fiber
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (R A Aminus : ℝ) (m : RoundingChoice) (heps : 0 < m.eps)
    (hgap : Aminus < A - m.eps) (t : ℝ) (y : LGSpace n)
    (hf : W (I.alongCoefficientPath t) y = (R : ℂ))
    (hy : potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 ≤ Aminus) :
    potentialPath_roundedDefiningFunction I φ R A m (t, y) = 0 := by
  obtain ⟨O, _hO, hp, hbase⟩ := potentialPath_roundedDefiningFunction_exists_unrounded_germ
    I hφ R A Aminus m heps hgap t y hf hy
  simpa only [hf, Complex.normSq_ofReal, sq, sub_self] using hbase (t, y) hp

/-- On the actual unchanged joint germ, any parameter-and-fiber
horizontal tangent vector automatically preserves the rounded equation. -/
theorem potentialPath_rounded_derivative_zero_of_fiber_horizontal
    (I : ToricInput n) (φ : RealSpace n → ℝ) (R A : ℝ) (m : RoundingChoice)
    (O : Set (ℝ × LGSpace n)) (hO : IsOpen O)
    (hbase : ∀ p ∈ O, potentialPath_roundedDefiningFunction I φ R A m p =
      Complex.normSq (W (I.alongCoefficientPath p.1) p.2) - R ^ 2)
    (p : ℝ × LGSpace n) (hp : p ∈ O)
    (v : TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p)
    (hv : mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
      (fun q : ℝ × LGSpace n => (q.1, W (I.alongCoefficientPath q.1) q.2)) p v = (1, 0)) :
    mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
      (potentialPath_roundedDefiningFunction I φ R A m) p v = 0 := by
  have hτ : MDifferentiableAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × LGSpace n → ℝ) p := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_fst (n := ∞)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
      (fun q : ℝ × LGSpace n => W (I.alongCoefficientPath q.1) q.2) p := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_coefficientPath_W_native_joint I).mdifferentiableAt (by simp)
  have hdf := (parameter_level_horizontal_components hτ hf v hv).2
  have hn : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ => ‖z‖ ^ 2)
      (W (I.alongCoefficientPath p.1) p.2) :=
    (contDiff_norm_sq ℝ (n := ∞)).contMDiff.mdifferentiableAt (by simp)
  have hnorm := hn.hasMFDerivAt.comp p hf.hasMFDerivAt
  have hbaseDer := hnorm.sub (hasMFDerivAt_const (c := R ^ 2) p)
  have hagree : potentialPath_roundedDefiningFunction I φ R A m =ᶠ[𝓝 p]
      (fun q : ℝ × LGSpace n => ‖W (I.alongCoefficientPath q.1) q.2‖ ^ 2 - R ^ 2) := by
    filter_upwards [hO.mem_nhds hp] with q hq
    simpa only [Complex.normSq_eq_norm_sq] using hbase q hq
  rw [hagree.mfderiv_eq]
  change mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ)
    (fun q : ℝ × LGSpace n => ‖W (I.alongCoefficientPath q.1) q.2‖ ^ 2 - R ^ 2) p v = 0
  erw [hbaseDer.mfderiv]
  change (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ => ‖z‖ ^ 2)
    (W (I.alongCoefficientPath p.1) p.2))
    (mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℂ)
      (fun q : ℝ × LGSpace n => W (I.alongCoefficientPath q.1) q.2) p v) - 0 = 0
  rw [hdf, map_zero, sub_self]

end FsFltz.Geometry
