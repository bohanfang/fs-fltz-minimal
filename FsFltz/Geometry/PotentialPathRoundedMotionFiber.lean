import FsFltz.Geometry.PotentialPathRoundedMotionCompatibility
import FsFltz.Geometry.PotentialFiberLiouville

/-!
# Constructed local holomorphic fiber and frontier lifts

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 996–1009,
the common logarithmic truncations, lines 1010–1049, and assembly,
lines 2127–2158. Far-value regularity and the actual intrinsic fiber
derivative construct local lifts of the moving full fiber and potential
frontier. Global gluing and the smooth completed pair remain later tasks.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance fiberMotionLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance fiberMotionLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth
local instance fiberMotionProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance fiberMotionProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- Far-value regularity constructs an actual smooth horizontal lift near
every point of every full holomorphic fiber along the coefficient path. -/
theorem ToricInput.coefficientPath_exists_local_fiber_horizontalField (I : ToricInput n) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      W (I.alongCoefficientPath t) y = (R : ℂ) →
      ∃ (O : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧ (t, y) ∈ O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) O ∧
        ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × ℂ)
          (fun q : ℝ × LGSpace n => (q.1, W (I.alongCoefficientPath q.1) q.2)) p (V p) = (1, 0) := by
  obtain ⟨B, hB, hregular⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_far_regular I
  refine ⟨B + 1, by linarith, ?_⟩
  intro R hR t ht y hy
  have hRpos : 0 < R := (by linarith : 0 < B + 1).trans_le hR
  have hreg := hregular t ht y (by
    rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    linarith)
  exact exists_parameter_level_horizontalField
    (contMDiff_coefficientPath_W_native_joint I) hreg

/-- Finite potential hypotheses and the proved logarithmic fiber estimate
construct local lifts preserving the moving fiber and the moving potential
simultaneously. The whole actual full fiber, including rank one, is used. -/
theorem ToricInput.coefficientPath_potentialPath_exists_local_marked_horizontalField
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      W (I.alongCoefficientPath t) y = (Real.exp β : ℂ) →
      F ^ 2 * β ^ 2 / 2 ≤ potentialPath (fun u => realSquaredNorm u / 2) φ t y.1 →
      ∃ (O : Set (ℝ × LGSpace n))
        (V : (p : ℝ × LGSpace n) → TangentSpace 𝓘(ℝ, ℝ × Model (2 * n)) p),
        IsOpen O ∧ (t, y) ∈ O ∧
        ContMDiffOn 𝓘(ℝ, ℝ × Model (2 * n)) (𝓘(ℝ, ℝ × Model (2 * n))).tangent ∞
          (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × Model (2 * n)) (ℝ × LGSpace n))) O ∧
        ∀ p ∈ O, mfderiv 𝓘(ℝ, ℝ × Model (2 * n)) 𝓘(ℝ, ℝ × (ℂ × ℝ))
          (fun q : ℝ × LGSpace n =>
            (q.1, (W (I.alongCoefficientPath q.1) q.2,
              potentialPath (fun u => realSquaredNorm u / 2) φ q.1 q.2.1))) p (V p) = (1, 0) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hφE := hφ.comp e.contDiff
  have hEndE := hEnd1.comp e.contDiff
  have hEndsE : ∀ u ≠ 0, ContDiffAt ℝ ∞ (φEnd ∘ e) u := by
    intro u hu
    apply (hEnd (e u) (by
      intro hz
      apply hu
      apply e.injective
      simpa only [map_zero] using hz)).comp u e.contDiff.contDiffAt
  have hhomE : ∀ r : ℝ, 0 < r → ∀ u, (φEnd ∘ e) (r • u) = r ^ 2 * (φEnd ∘ e) u := by
    intro r hr u
    simpa only [Function.comp_apply, map_smul] using hhom r hr (e u)
  have hendE : ∀ u, L ≤ ‖u‖ → (φ ∘ e) u = (φEnd ∘ e) u := by
    intro u hu
    exact hend (e u) hu
  obtain ⟨F, hF, B₀, hB₀, hbound⟩ :=
    I.coefficientPath_potentialPath_intrinsic_fiber_outward
      hφE hEndE hEndsE hhomE hc hlower hupper hL hendE 0
  obtain ⟨B, hB, hregular⟩ := FsFltz.Geometry.ToricInput.coefficientPath_far_regular I
  refine ⟨F, hF, max B₀ (Real.log (B + 1)), hB₀.trans_le (le_max_left _ _), ?_⟩
  intro β hβ t ht y hy hlevel
  have hexp : B < Real.exp β := by
    have hlog := (le_max_right B₀ (Real.log (B + 1))).trans hβ
    have hB1 : 0 < B + 1 := by linarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hB1] at hexp
    linarith
  have hnorm : ‖(Real.exp β : ℂ)‖ = Real.exp β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos β)]
  have hregAll : ∀ z, W (I.alongCoefficientPath t) z = (Real.exp β : ℂ) →
      Function.Surjective (complexDifferential (lgManifold n)
        (W (I.alongCoefficientPath t)) z) := by
    intro z hz
    exact hregular t ht z (by rwa [hz, hnorm])
  have hrealization := exists_regularLevel_embedding (lgManifold n)
    (W (I.alongCoefficientPath t)) (Real.exp β : ℂ)
    (contMDiff_W_lgManifold _) hregAll
  rw [Complex.finrank_real_complex] at hrealization
  obtain ⟨N, j, himage⟩ := hrealization
  have hmem : y ∈ range j.map := by rw [himage]; exact hy
  obtain ⟨x, rfl⟩ := hmem
  have htangent := @regularLevel_embedding_tangent_range (2 * n) (lgManifold n) ℂ
    inferInstance inferInstance inferInstance (W (I.alongCoefficientPath t))
    (Real.exp β : ℂ) (contMDiff_W_lgManifold _) hregAll
  rw [Complex.finrank_real_complex] at htangent
  have hkernel := htangent j himage x
  let ψ := potentialPath (fun u => realSquaredNorm u / 2) φ t
  have hψeq : potentialPath (fun u => ‖u‖ ^ 2 / 2) (φ ∘ e) t ∘
      (EuclideanSpace.equiv (Fin n) ℝ).symm = ψ := by
    funext u
    change (1 - t) * (‖e.symm u‖ ^ 2 / 2) + t * φ (e (e.symm u)) =
      (1 - t) * (realSquaredNorm u / 2) + t * φ u
    rw [e.apply_symm_apply]
    congr 2
    simp [e, EuclideanSpace.norm_sq_eq, realSquaredNorm]
  have hpos := (hbound β ((le_max_left _ _).trans hβ)).2 t ht t ht
    (2 * n - 2) N j x hkernel (by simpa only [hψeq] using hlevel)
    (by rw [hy, hnorm])
  have hj : ∀ z, W (I.alongCoefficientPath t) (j.map z) = (Real.exp β : ℂ) := by
    intro z
    have hm : j.map z ∈ range j.map := ⟨z, rfl⟩
    rwa [himage] at hm
  have hmarked := surjective_markedLevel_of_fiber_tangent (lgManifold n) N
    (W (I.alongCoefficientPath t)) (fun z => ψ z.1)
    (contMDiff_W_lgManifold _) (contMDiff_potentialValue (potentialPath_native_contDiff hφ t))
    j (Real.exp β : ℂ) hj x (hregAll _ hy)
    (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm ψ)) x)
    (by simpa only [hψeq] using hpos.2.ne')
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ × ℝ) ∞
      (fun p : ℝ × LGSpace n => (W (I.alongCoefficientPath p.1) p.2,
        potentialPath (fun u => realSquaredNorm u / 2) φ p.1 p.2.1)) := by
    apply (contMDiff_coefficientPath_W_native_joint I).prodMk_space
    exact ((contMDiff_const.sub contMDiff_fst).mul
      (contMDiff_original_phi0.comp contMDiff_snd)).add
      (contMDiff_fst.mul ((contMDiff_potentialValue hφ).comp contMDiff_snd))
  exact exists_parameter_level_horizontalField hsmooth hmarked

end FsFltz.Geometry
