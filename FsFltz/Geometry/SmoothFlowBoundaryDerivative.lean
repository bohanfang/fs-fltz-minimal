import FsFltz.Geometry.TailoringOuterBoundaryHittingSmooth
import FsFltz.Geometry.LocalCovers

/-!
# Transversality on an open coefficient neighborhood

Source: `geometric-part-fsf-proof.tex`, `lem:hitting`, lines 1760–1775,
and `prop:band`, lines 1802–1817. Compact boundary transversality extends
across coefficient endpoints. The flow law then gives uniqueness of
potential hits for every initial point throughout this open coefficient set.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}
local instance smoothFlowBoundaryCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance smoothFlowBoundarySmooth :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- The time derivative of a smooth scalar family is continuous on the
native coefficient/quotient space, with no choice of logarithmic representative. -/
theorem continuous_time_deriv_lg
    {H : ℝ × (ℝ × LGSpace n) → ℝ}
    (hH : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      𝓘(ℝ, ℝ) ∞ H) (t : ℝ) :
    Continuous (fun p : ℝ × LGSpace n => deriv (fun s => H (s, p)) t) := by
  have hq := (isLocalDiffeomorph_lgCover n).isOpenMap.isQuotientMap
    (contMDiff_lgCover n).continuous (lgCover_surjective n)
  apply hq.continuous_lift_prod_right
  let g : (ℝ × TangentCoordinates n) → ℝ → ℝ :=
    fun p s => H (s, (p.1, lgCover p.2))
  have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
    (hH.comp (contDiff_snd.contMDiff.prodMk
      (contDiff_fst.fst.contMDiff.prodMk
        ((contMDiff_lgCover n).comp contDiff_fst.snd.contMDiff)))).contDiff
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ (g p) t (1 : ℝ)) :=
    hg.fderiv_apply contDiff_const contDiff_const (by simp)
  exact hd.continuous

/-- Compact boundary positivity persists on an open coefficient neighborhood. -/
theorem exists_isOpen_parameter_boundary_deriv_pos
    {H : ℝ × (ℝ × LGSpace n) → ℝ}
    (hH : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      𝓘(ℝ, ℝ) ∞ H)
    {P : Set ℝ} {S : Set (LGSpace n)} (hP : IsCompact P) (hS : IsCompact S)
    (hpos : ∀ p ∈ P ×ˢ S, 0 < deriv (fun t => H (t, p)) 0) :
    ∃ J : Set ℝ, IsOpen J ∧ P ⊆ J ∧
      ∀ K ∈ J, ∀ y ∈ S, 0 < deriv (fun t => H (t, (K, y))) 0 := by
  have hO : IsOpen {p : ℝ × LGSpace n | 0 < deriv (fun t => H (t, p)) 0} :=
    isOpen_lt continuous_const (continuous_time_deriv_lg hH 0)
  obtain ⟨J, U, hJ, _hU, hPJ, hSU, hJU⟩ :=
    generalized_tube_lemma hP hS hO hpos
  exact ⟨J, hJ, hPJ, fun K hK y hy => hJU ⟨hK, hSU hy⟩⟩

/-- The flow law transports the time-zero scalar derivative to every time. -/
theorem deriv_scalar_flow_eq_time_zero
    (F : Flow ℝ (ℝ × LGSpace n))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2))
    {ρ : LGSpace n → ℝ} (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    (p : ℝ × LGSpace n) (t : ℝ) :
    deriv (fun s => ρ (F s p).2) t =
      deriv (fun s => ρ (F s (F t p)).2) 0 := by
  have hs : Differentiable ℝ (fun s => ρ (F s (F t p)).2) :=
    (hρ.comp (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable
      (by simp)
  have hd := (hs (t - t)).hasDerivAt.comp (h := fun s : ℝ => s - t) t
    ((hasDerivAt_id t).sub_const t)
  have he : (fun s => ρ (F (s - t) (F t p)).2) = fun s => ρ (F s p).2 := by
    funext s
    rw [← F.map_add, sub_add_cancel]
  simpa only [sub_self, mul_one, Function.comp_def, he] using hd.deriv

/-- Compact transverse boundary hits remain unique for all initial points
on one open coefficient neighborhood, including across interval endpoints. -/
theorem exists_isOpen_parameter_unique_flow_hits
    (F : Flow ℝ (ℝ × LGSpace n))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2))
    (hfst : ∀ t p, (F t p).1 = p.1)
    {ρ : LGSpace n → ℝ} (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    {P : Set ℝ} (hP : IsCompact P) {A : ℝ}
    (hS : IsCompact {y : LGSpace n | ρ y = A})
    (hpos : ∀ K ∈ P, ∀ y, ρ y = A →
      0 < deriv (fun t => ρ (F t (K, y)).2) 0) :
    ∃ J : Set ℝ, IsOpen J ∧ P ⊆ J ∧
      ∀ K ∈ J, ∀ y : LGSpace n, ∀ s t : ℝ,
        ρ (F s (K, y)).2 = A → ρ (F t (K, y)).2 = A → s = t := by
  obtain ⟨J, hJ, hPJ, hposJ⟩ := exists_isOpen_parameter_boundary_deriv_pos
    (hρ.comp hF.snd) hP hS (fun p hp => hpos p.1 hp.1 p.2 hp.2)
  refine ⟨J, hJ, hPJ, ?_⟩
  intro K hK y s t hs ht
  have hg : Differentiable ℝ (fun r => ρ (F r (K, y)).2) :=
    (hρ.comp (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd).contDiff.differentiable
      (by simp)
  apply eq_of_level_eq_of_boundary_deriv_pos hg _ hs ht
  intro r hr
  rw [deriv_scalar_flow_eq_time_zero F hF hρ]
  have hpair : F r (K, y) = (K, (F r (K, y)).2) :=
    Prod.ext (hfst r (K, y)) rfl
  rw [hpair]
  exact hposJ K hK (F r (K, y)).2 hr

end FsFltz.Geometry
