import FsFltz.Geometry.TailoringFiniteBandHittingCore
import FsFltz.Analysis.TailoringExhaustionDomain
import FsFltz.Geometry.BoundaryOutwardAbsorptionMarking

/-!
# Finite hits of the actual outer potential boundary

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1802–1817.
The compact potential sublevel bounds the actual base coordinate. A
trajectory avoiding its outer boundary would solve the native equation
forever inside that sublevel, contradicting the positive base speed.
Only native ODE agreement inside this compact region is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff Manifold

namespace FsFltz.Geometry

/-- A scalar function with positive derivative at every level crossing
has at most one crossing, without any derivative sign away from it. -/
theorem eq_of_level_eq_of_boundary_deriv_pos {g : ℝ → ℝ}
    (hg : Differentiable ℝ g) {A s t : ℝ}
    (hpos : ∀ r, g r = A → 0 < deriv g r)
    (hs : g s = A) (ht : g t = A) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · have hh := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
      (fun r => (hg r).hasDerivAt) hpos hs.ge h
    exact False.elim ((not_lt_of_ge ht.le) hh)
  · exact h
  · have hh := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
      (fun r => (hg r).hasDerivAt) hpos ht.ge h
    exact False.elim ((not_lt_of_ge hs.le) hh)

/-- The native derivative of a scalar along a local integral curve. -/
theorem hasDerivAt_scalar_of_isMIntegralCurveAt {d : ℕ} (M : SmoothManifold d)
    {ρ : M.Point → ℝ} (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    {Z : (x : M.Point) → M.Tangent x} {γ : ℝ → M.Point} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ Z t) :
    HasDerivAt (fun s => ρ (γ s)) (M.scalarDerivative ρ (γ t) (Z (γ t))) t := by
  have h := (hasMFDerivAt_iff_hasFDerivAt.mp
    ((hρ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hγ.hasMFDerivAt)).hasDerivAt
  apply h.congr_deriv
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ (γ t) ((1 : ℝ) • Z (γ t)) = _
  rw [one_smul]
  rfl

/-- On a compact interval ending above a level, there is a last crossing
and the scalar stays at or above that level after this crossing. -/
theorem exists_last_level_crossing_before_zero {g : ℝ → ℝ} (hg : Continuous g)
    {A a : ℝ} (ha : a < 0) (hga : g a = A) (hgzero : A < g 0) :
    ∃ t ∈ Ico a (0 : ℝ), g t = A ∧ ∀ s ∈ Icc t (0 : ℝ), A ≤ g s := by
  let S : Set ℝ := Icc a 0 ∩ {s | g s = A}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  obtain ⟨t, ht, hmax⟩ := hS.exists_isMaxOn
    (show S.Nonempty from ⟨a, ⟨left_mem_Icc.mpr ha.le, hga⟩⟩) continuous_id.continuousOn
  have htneg : t < 0 := by
    have htne : t ≠ 0 := by intro he; exact hgzero.ne (he ▸ ht.2).symm
    exact lt_of_le_of_ne ht.1.2 htne
  refine ⟨t, ⟨ht.1.1, htneg⟩, ht.2, ?_⟩
  intro s hs
  by_contra hn
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hs.2 hg.continuousOn
    (show A ∈ Icc (g s) (g 0) from ⟨(lt_of_not_ge hn).le, hgzero.le⟩)
  have hrS : r ∈ S := ⟨⟨ht.1.1.trans (hs.1.trans hr.1), hr.2⟩, he⟩
  have hrt : r ≤ t := hmax hrS
  have hst : t = s := le_antisymm hs.1 (hr.1.trans hrt)
  exact hn (hst ▸ ht.2.ge)

end FsFltz.Geometry

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance outerBoundaryHittingChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance outerBoundaryHittingIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- A smooth flow solving the actual native equation inside the compact
potential sublevel has a unique literal outer-boundary hit from every
actual core point strictly inside. No global native flow is assumed. -/
theorem tailoringEndpoint_exists_uniform_core_outer_boundary_hits
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
      ∀ y ∈ tailoringCoreSection I φEnd β,
        φ y.1 < D ^ 2 * β ^ 2 / 2 →
        ∃ t : ℝ, 0 < t ∧ φ (F t (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 ∧
          (∀ s, φ (F s (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 → s = t) ∧
          (∀ s ∈ Icc (0 : ℝ) t, (F s (K, y)).2 ∈ tailoringLegendreConic I φEnd ∧
            1 ≤ (tailoringFamily I β 1 (F s (K, y)).2).re) := by
  obtain ⟨Bb, hBb, hbasehit⟩ := tailoringEndpoint_exists_uniform_ambient_core_finite_base_hits
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bf, _, hforward⟩ := tailoringEndpoint_exists_uniform_ambient_conormal_forward_superlevel
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bd, _, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd.smooth hEnd.homogeneous hR heq hD
  refine ⟨max Bb (max Bf Bd), hBb.trans_le (le_max_left _ _), ?_⟩
  intro β hβ F hF K hK hode y hy hinside
  have hβb : Bb ≤ β := (le_max_left _ _).trans hβ
  have hβf : Bf ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβd : Bd ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hcompact, _, hboundary⟩ := hdata β hβd
  let A : ℝ := D ^ 2 * β ^ 2 / 2
  let ρ : LGSpace n → ℝ := fun z => φ z.1
  let γ : ℝ → LGSpace n := fun s => (F s (K, y)).2
  let g : ℝ → ℝ := ρ ∘ γ
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n)) ∞ γ :=
    (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd
  have hg : Differentiable ℝ g :=
    ((contMDiff_potentialValue hφ).comp hcurve).contDiff.differentiable (by simp)
  have hzero : g 0 < A := by simpa only [g, ρ, γ, Function.comp_apply, Flow.map_zero_apply] using hinside
  have hderpos : ∀ s, g s = A → 0 < deriv g s := by
    intro s hs
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt (lgManifold n)
      (ρ := fun z => φ z.1 - A)
      ((contMDiff_potentialValue hφ).sub contMDiff_const) (hode y s hs.le)
    change HasDerivAt (fun r => g r - A) _ s at hd
    have hd' : HasDerivAt (fun r => g r - A) (deriv g s) s :=
      (hg s).hasDerivAt.sub_const A
    rw [hd'.unique hd]
    have hp := (hboundary 1 (by simp) K hK).2 (γ s) (sub_eq_zero.mpr hs)
    exact hp
  have hex : ∃ t : ℝ, 0 < t ∧ g t = A := by
    by_contra hnot
    have hbelow : ∀ s : ℝ, 0 ≤ s → g s < A := by
      intro s hs
      by_contra hb
      obtain ⟨t, ht, he⟩ := intermediate_value_Icc hs hg.continuous.continuousOn
        (show A ∈ Icc (g 0) (g s) from ⟨hzero.le, le_of_not_gt hb⟩)
      have htpos : 0 < t := by
        have htne : t ≠ 0 := by intro h; subst t; exact hzero.ne he
        exact lt_of_le_of_ne ht.1 htne.symm
      exact hnot ⟨t, htpos, he⟩
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image
      (Complex.continuous_re.comp (contMDiff_tailoringFamily_lgManifold I β 1).continuous).continuousOn
    let M' : ℝ := max M 1 + 1
    obtain ⟨ε, _, hhit⟩ := hbasehit β hβb M' (by dsimp [M']; linarith [le_max_right M 1])
    obtain ⟨t, ht, he, _, _⟩ := hhit F hF K hK y hy
      (fun s hs => hode y s (hbelow s hs).le)
    have hb := hM (mem_image_of_mem (fun z : LGSpace n => (tailoringFamily I β 1 z).re)
      (show γ t ∈ {z : LGSpace n | φ z.1 - D ^ 2 * β ^ 2 / 2 ≤ 0} from sub_nonpos.mpr (hbelow t ht.1.le).le))
    change (tailoringFamily I β 1 (F t (K, y)).2).re ≤ M at hb
    rw [he] at hb
    dsimp [M'] at hb
    linarith [le_max_left M 1]
  obtain ⟨t, ht, he⟩ := hex
  refine ⟨t, ht, he, fun s hs => eq_of_level_eq_of_boundary_deriv_pos hg hderpos hs he, ?_⟩
  have hbefore : ∀ s ∈ Icc (0 : ℝ) t, g s ≤ A := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with hst | hst
    · exact hst ▸ he.le
    · by_contra hnot
      have hh := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
        (fun r => (hg r).hasDerivAt) hderpos (le_of_not_ge hnot) hst
      exact (not_lt_of_ge he.le) hh
  have hstart : γ 0 ∈ tailoringLegendreConic I φEnd := by
    simpa only [γ, Flow.map_zero_apply] using hy.1
  have hbase : 1 ≤ (tailoringFamily I β 1 (γ 0)).re := by
    have he : tailoringFamily I β 1 y = 1 := hy.2
    simp only [γ, Flow.map_zero_apply, he, Complex.one_re, le_refl]
  have hr := hforward β hβf K hK γ 0 t ht.le
    (fun s hs => hode y s (hbefore s hs)) hstart hbase
  intro s hs
  exact ⟨(hr.1 s hs).1, (hr.1 s hs).2.2⟩

/-- Every actual conic outer-boundary point beyond base one reaches the
actual level-one core section in finite negative time. Cone retention is
proved on the last crossing interval, rather than supplied as a premise. -/
theorem tailoringEndpoint_exists_uniform_outer_boundary_backward_hits
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
      ∀ y ∈ tailoringLegendreConic I φEnd,
        φ y.1 = D ^ 2 * β ^ 2 / 2 → 1 < (tailoringFamily I β 1 y).re →
        ∃ t : ℝ, t < 0 ∧ (F t (K, y)).2 ∈ tailoringCoreSection I φEnd β := by
  obtain ⟨Bi, hBi, hinv⟩ := tailoringEndpoint_exists_uniform_ambient_conormal_invariance_on
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bm, _, hmargin⟩ := tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hR heq
  obtain ⟨Bd, _, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd.smooth hEnd.homogeneous hR heq hD
  obtain ⟨Br, hreal⟩ := eventually_atTop.mp hEnd.eventually_cone_family_eq_radial
  refine ⟨max Bi (max Bm (max Bd Br)), hBi.trans_le (le_max_left _ _), ?_⟩
  intro β hβ F hF K hK hode y hy hlevel hbasezero
  have hβi : Bi ≤ β := (le_max_left _ _).trans hβ
  have hβm : Bm ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβd : Bd ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβr : Br ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  obtain ⟨hcompact, _, hboundary⟩ := hdata β hβd
  let A : ℝ := D ^ 2 * β ^ 2 / 2
  let γ : ℝ → LGSpace n := fun s => (F s (K, y)).2
  let g : ℝ → ℝ := fun s => φ (γ s).1
  let b : ℝ → ℝ := fun s => (tailoringFamily I β 1 (γ s)).re
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n)) ∞ γ :=
    (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd
  have hg : Differentiable ℝ g :=
    ((contMDiff_potentialValue hφ).comp hcurve).contDiff.differentiable (by simp)
  have hb : Differentiable ℝ b :=
    (Complex.reCLM.contMDiff.comp ((contMDiff_tailoringFamily_lgManifold I β 1).comp hcurve)).contDiff.differentiable (by simp)
  have hgzero : g 0 = A := by simpa only [g, γ, Flow.map_zero_apply] using hlevel
  have hbzero : 1 < b 0 := by simpa only [b, γ, Flow.map_zero_apply] using hbasezero
  have hderpos : ∀ s, g s = A → 0 < deriv g s := by
    intro s hs
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt (lgManifold n)
      (ρ := fun z => φ z.1 - A)
      ((contMDiff_potentialValue hφ).sub contMDiff_const) (hode y s hs.le)
    change HasDerivAt (fun r => g r - A) _ s at hd
    have hd' : HasDerivAt (fun r => g r - A) (deriv g s) s := (hg s).hasDerivAt.sub_const A
    rw [hd'.unique hd]
    exact (hboundary 1 (by simp) K hK).2 (γ s) (sub_eq_zero.mpr hs)
  have hbelow : ∀ s ≤ 0, g s ≤ A := by
    intro s hs
    rcases eq_or_lt_of_le hs with hs | hs
    · exact hs ▸ hgzero.le
    · by_contra hn
      have hh := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
        (fun r => (hg r).hasDerivAt) hderpos (le_of_not_ge hn) hs
      exact (not_lt_of_ge hgzero.le) hh
  have hnative : ∀ s ≤ 0, IsMIntegralCurveAt γ
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) s :=
    fun s hs => hode y s (hbelow s hs)
  have hstart : γ 0 ∈ tailoringLegendreConic I φEnd := by
    simpa only [γ, Flow.map_zero_apply] using hy
  have hex : ∃ t : ℝ, t < 0 ∧ b t = 1 := by
    by_contra hn
    have hbase : ∀ s ≤ 0, 1 < b s := by
      intro s hs
      rcases eq_or_lt_of_le hs with hs | hs
      · exact hs ▸ hbzero
      · by_contra hnot
        obtain ⟨t, ht, he⟩ := intermediate_value_Icc hs.le hb.continuous.continuousOn
          (show 1 ∈ Icc (b s) (b 0) from ⟨le_of_not_gt hnot, hbzero.le⟩)
        have htneg : t < 0 := by
          have htne : t ≠ 0 := by intro h; subst t; exact hbzero.ne he.symm
          exact lt_of_le_of_ne ht.2 htne
        exact hn ⟨t, htneg, he⟩
    have hcone : ∀ s ≤ 0, γ s ∈ tailoringLegendreConic I φEnd := by
      intro s hs
      have hr := hinv β hβi K hK (Icc s 0) (convex_Icc s 0).isPreconnected γ
        (fun t ht => hnative t ht.2)
        (fun t ht => (hbase t ht.2).le.trans (Complex.re_le_norm _))
        0 ⟨hs, le_rfl⟩ hstart
      exact (hr s ⟨le_rfl, hs⟩).1
    obtain ⟨M, hM⟩ := hcompact.bddAbove_image
      (Complex.continuous_re.comp (contMDiff_tailoringFamily_lgManifold I β 1).continuous).continuousOn
    obtain ⟨ε, hε, hm⟩ := hmargin β hβm M
    have hspeed : ∀ s ≤ 0, ε ≤ deriv b s := by
      intro s hs
      have hd := hasDerivAt_re_of_isMIntegralCurveAt (lgManifold n)
        (contMDiff_tailoringFamily_lgManifold I β 1) (hnative s hs)
      change HasDerivAt b _ s at hd
      rw [hd.deriv]
      apply hm (γ s) (hcone s hs) (hbase s hs).le _ K hK
      exact hM (mem_image_of_mem (fun z : LGSpace n => (tailoringFamily I β 1 z).re)
        (show γ s ∈ {z : LGSpace n | φ z.1 - D ^ 2 * β ^ 2 / 2 ≤ 0} from sub_nonpos.mpr (hbelow s hs)))
    let T : ℝ := (b 0 + 1) / ε
    have hT : 0 < T := div_pos (by linarith) hε
    have hsl := (convex_Icc (-T) (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      hb.continuous.continuousOn hb.differentiableOn
      (fun s hs => hspeed s (interior_subset hs).2)
      (-T) ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, le_rfl⟩ (by linarith)
    have heT : ε * T = b 0 + 1 := by dsimp only [T]; exact mul_div_cancel₀ _ hε.ne'
    have hbound := hbase (-T) (by linarith)
    simp only [sub_neg_eq_add, zero_add] at hsl
    rw [heT] at hsl
    linarith
  obtain ⟨a, ha, hea⟩ := hex
  obtain ⟨t, ht, he, hband⟩ := exists_last_level_crossing_before_zero hb.continuous ha hea hbzero
  have hr := hinv β hβi K hK (Icc t 0) (convex_Icc t 0).isPreconnected γ
    (fun s hs => hnative s hs.2)
    (fun s hs => (hband s hs).trans (Complex.re_le_norm _))
    0 ⟨ht.2.le, le_rfl⟩ hstart
  have hcγ := (hr t ⟨le_rfl, ht.2.le⟩).1
  have hnorm : 1 ≤ ‖tailoringFamily I β 1 (γ t)‖ :=
    he.ge.trans (Complex.re_le_norm _)
  have hh := tailoringEndpoint_height_lower_of_norm_ge_one I β (γ t) hnorm
  have hN : 0 < (I.vertices.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  have hlog : Real.log (I.vertices.card : ℝ) ≤ Real.log (2 * (I.vertices.card : ℝ)) :=
    Real.log_le_log hN (by linarith)
  obtain ⟨hpne, σ, hσ, hσne, hp, hθ⟩ := hcγ
  have hrealγ := hreal β hβr σ hσ (γ t) hp hθ (by linarith)
  have hcomplex : tailoringFamily I β 1 (γ t) = 1 := by
    have hval := he
    change (tailoringFamily I β 1 (γ t)).re = 1 at hval
    rw [hrealγ, Complex.ofReal_re] at hval
    rw [hrealγ, hval, Complex.ofReal_one]
  exact ⟨t, ht.2, ⟨hpne, σ, hσ, hσne, hp, hθ⟩, hcomplex⟩

end FsFltz
