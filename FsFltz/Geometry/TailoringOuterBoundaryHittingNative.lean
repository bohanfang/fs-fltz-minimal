import FsFltz.Geometry.TailoringOuterBoundaryHittingGeometry
import FsFltz.Geometry.TailoringOuterBoundaryHittingSmooth
import FsFltz.Geometry.TailoringFiniteNativeFlow

/-!
# Constructed native outer-boundary comparison

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1778–1817,
and `lem:hitting`, lines 1760–1775. A constructed cutoff action agrees
with the actual endpoint Liouville field on the entire compact potential
sublevel. Its unique literal outer-boundary map is bijective, and its
time and spatial map extend smoothly to open coefficient/initial-point
neighborhoods. The outer radius can be enlarged before choosing β.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology ContDiff Manifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}
local instance outerBoundaryNativeChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance outerBoundaryNativeIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- The actual potential boundary is a barrier in backward time for
every smooth regional native trajectory starting on that boundary. -/
private theorem outer_boundary_backward_sublevel
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {F : Flow ℝ (ℝ × LGSpace n)}
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2))
    {Z : (x : (lgManifold n).Point) → (lgManifold n).Tangent x}
    {K A : ℝ}
    (hode : ∀ y t, φ (F t (K, y)).2.1 ≤ A →
      IsMIntegralCurveAt (fun s => (F s (K, y)).2) Z t)
    (hboundary : ∀ z, φ z.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) z (Z z))
    {w : LGSpace n} (hw : φ w.1 = A) :
    ∀ s ≤ 0, φ (F s (K, w)).2.1 ≤ A := by
  let γ : ℝ → LGSpace n := fun s => (F s (K, w)).2
  let g : ℝ → ℝ := fun s => φ (γ s).1
  have hcurve : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (2 * n)) ∞ γ :=
    (hF.comp (contMDiff_id.prodMk contMDiff_const)).snd
  have hg : Differentiable ℝ g :=
    ((contMDiff_potentialValue hφ).comp hcurve).contDiff.differentiable (by simp)
  have hgzero : g 0 = A := by simpa only [g, γ, Flow.map_zero_apply] using hw
  have hderpos : ∀ s, g s = A → 0 < deriv g s := by
    intro s hs
    have hd := hasDerivAt_scalar_of_isMIntegralCurveAt (lgManifold n)
      (ρ := fun z => φ z.1 - A)
      ((contMDiff_potentialValue hφ).sub contMDiff_const) (hode w s hs.le)
    change HasDerivAt (fun r => g r - A) _ s at hd
    have hd' : HasDerivAt (fun r => g r - A) (deriv g s) s :=
      (hg s).hasDerivAt.sub_const A
    rw [hd'.unique hd]
    exact hboundary (γ s) (sub_eq_zero.mpr hs)
  intro s hs
  rcases eq_or_lt_of_le hs with hs | hs
  · exact hs ▸ hgzero.le
  · by_contra hn
    have hh := BoundaryOutwardAbsorptionMarking.level_lt_of_boundary_deriv_pos
      (fun r => (hg r).hasDerivAt) hderpos (le_of_not_ge hn) hs
    exact (not_lt_of_ge hgzero.le) hh

/-- A constructed parameter preserving action gives the actual outer
potential-level bijection, with unique finite positive times and smooth
open extensions of those same times and their spatial maps. -/
theorem tailoringEndpoint_exists_uniform_native_outer_boundary_bijection
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
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D ≥ D₀, ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ Kstar : ℝ,
      ∃ F : Flow ℝ (ℝ × LGSpace n),
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) ∧
        (∀ t p, (F t p).1 = p.1) ∧
        (∀ K ∈ Icc (0 : ℝ) Kstar, ∀ y t, φ (F t (K, y)).2.1 ≤ D ^ 2 * β ^ 2 / 2 →
          IsMIntegralCurveAt (fun s => (F s (K, y)).2)
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) ∧
        ∀ K ∈ Icc (0 : ℝ) Kstar, ∃ τ : LGSpace n → ℝ,
          (∀ y ∈ tailoringCoreSection I φEnd β,
            0 < τ y ∧ φ (F (τ y) (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 ∧
            (∀ s, φ (F s (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 → s = τ y) ∧
            ∀ s ∈ Icc (0 : ℝ) (τ y), (F s (K, y)).2 ∈ tailoringLegendreConic I φEnd ∧
              1 ≤ (tailoringFamily I β 1 (F s (K, y)).2).re) ∧
          BijOn (fun y => (F (τ y) (K, y)).2) (tailoringCoreSection I φEnd β)
            {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = D ^ 2 * β ^ 2 / 2} ∧
          ∀ x : TangentCoordinates n, lgCover x ∈ tailoringCoreSection I φEnd β →
            ∃ V : Set (ℝ × TangentCoordinates n), IsOpen V ∧ (K, x) ∈ V ∧
              ∃ τlocal : ℝ × TangentCoordinates n → ℝ,
                ContDiffOn ℝ ∞ τlocal V ∧ τlocal (K, x) = τ (lgCover x) ∧
                (∀ p ∈ V, φ (F (τlocal p) (p.1, lgCover p.2)).2.1 = D ^ 2 * β ^ 2 / 2) ∧
                ContMDiffOn 𝓘(ℝ, ℝ × TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
                  (fun p => (F (τlocal p) (p.1, lgCover p.2)).2) V := by
  classical
  obtain ⟨D₀, hD₀, hgeometry⟩ := tailoringEndpoint_exists_uniform_outer_conormal_base_gt_one
    I hφ hc hU hlower hupper hEnd1 hEnd Φ hΦeq hΦ₀ hR heq
  refine ⟨D₀, hD₀, ?_⟩
  intro D hDle
  have hD : 0 < D := hD₀.trans_le hDle
  obtain ⟨Bg, hBg, hgeom⟩ := hgeometry D hDle
  obtain ⟨Bh, _, hhit⟩ := tailoringEndpoint_exists_uniform_core_outer_boundary_hits
    I hφ hc hU hlower hupper hEnd1 hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq hD
  obtain ⟨Bb, _, hback⟩ := tailoringEndpoint_exists_uniform_outer_boundary_backward_hits
    I hφ hc hU hlower hupper hEnd1 hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq hD
  obtain ⟨Bd, _, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd.smooth hEnd.homogeneous hR heq hD
  obtain ⟨Bf, _, hflow⟩ := tailoringEndpoint_exists_uniform_finite_region_native_flow
    I hφ hc hU hlower hupper
  obtain ⟨Br, _, hretain⟩ := tailoringEndpoint_exists_uniform_ambient_conormal_forward_superlevel
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bs, _, hsmooth⟩ := tailoringEndpoint_exists_uniform_core_outer_boundary_smooth_hits
    I hφ hc hU hlower hupper hEnd1 hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq hD
  refine ⟨max Bg (max Bh (max Bb (max Bd (max Bf (max Br Bs))))),
    hBg.trans_le (le_max_left _ _), ?_⟩
  intro β hβ Kstar
  obtain ⟨hβg, hβh, hβb, hβd, hβf, hβr, hβs⟩ :
      Bg ≤ β ∧ Bh ≤ β ∧ Bb ≤ β ∧ Bd ≤ β ∧ Bf ≤ β ∧ Br ≤ β ∧ Bs ≤ β := by
    simpa only [max_le_iff] using hβ
  obtain ⟨hcompact, _, hboundary⟩ := hdata β hβd
  obtain ⟨V, F, _, hF, hfst, _, hnative⟩ := hflow β hβf Kstar
    {z : LGSpace n | φ z.1 - D ^ 2 * β ^ 2 / 2 ≤ 0} hcompact
  have hode (K : ℝ) (hK : K ∈ Icc (0 : ℝ) Kstar) (y : LGSpace n) (t : ℝ)
      (ht : φ (F t (K, y)).2.1 ≤ D ^ 2 * β ^ 2 / 2) :=
    hnative K hK y t (sub_nonpos.mpr ht)
  refine ⟨F, hF, hfst, hode, ?_⟩
  intro K hK
  let hits (y : tailoringCoreSection I φEnd β) :=
    hhit β hβh F hF K hK.1 (hode K hK) y.val y.property
      ((hgeom β hβg).1 y.val y.property)
  let τ : LGSpace n → ℝ := fun y => if hy : y ∈ tailoringCoreSection I φEnd β then
    (hits ⟨y, hy⟩).choose else 0
  have hτ (y : LGSpace n) (hy : y ∈ tailoringCoreSection I φEnd β) :
      0 < τ y ∧ φ (F (τ y) (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 ∧
      (∀ s, φ (F s (K, y)).2.1 = D ^ 2 * β ^ 2 / 2 → s = τ y) ∧
      ∀ s ∈ Icc (0 : ℝ) (τ y), (F s (K, y)).2 ∈ tailoringLegendreConic I φEnd ∧
        1 ≤ (tailoringFamily I β 1 (F s (K, y)).2).re := by
    simp only [τ, dite_eq_left hy]
    exact (hits ⟨y, hy⟩).choose_spec
  let π : LGSpace n → LGSpace n := fun y => (F (τ y) (K, y)).2
  have hmap : MapsTo π (tailoringCoreSection I φEnd β)
      {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = D ^ 2 * β ^ 2 / 2} := by
    intro y hy
    exact ⟨((hτ y hy).2.2.2 (τ y) ⟨(hτ y hy).1.le, le_rfl⟩).1, (hτ y hy).2.1⟩
  have hinverse (y : LGSpace n) : (F (-τ y) (K, π y)).2 = y := by
    have he : F (τ y) (K, y) = (K, π y) := Prod.ext (hfst _ _) rfl
    rw [← he, ← F.map_add, neg_add_cancel, F.map_zero_apply]
  have hinj : InjOn π (tailoringCoreSection I φEnd β) := by
    intro y hy z hz he
    let w := π y
    let γ : ℝ → LGSpace n := fun s => (F s (K, w)).2
    have hγy : γ (-τ y) = y := hinverse y
    have hγz : γ (-τ z) = z := by simpa only [γ, w, he] using hinverse z
    have hbelow := outer_boundary_backward_sublevel hφ hF (hode K hK)
      ((hboundary 1 (by simp) K hK.1).2) (hmap hy).2
    have hunique : -τ y = -τ z := by
      have hnotlt (a b : ℝ) (ha : γ a ∈ tailoringCoreSection I φEnd β)
          (hb : γ b ∈ tailoringCoreSection I φEnd β) (hbzero : b ≤ 0) : ¬ a < b := by
        intro hab
        have haeq : tailoringFamily I β 1 (γ a) = 1 := ha.2
        have hbeq : tailoringFamily I β 1 (γ b) = 1 := hb.2
        have hr := hretain β hβr K hK.1 γ a b hab.le
          (fun s hs => hode K hK w s (hbelow s (hs.2.trans hbzero))) ha.1
          (by simp only [haeq, Complex.one_re, le_refl])
        have hh := hr.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
        simp only [haeq, hbeq, Complex.one_re, lt_self_iff_false] at hh
      exact le_antisymm
        (le_of_not_gt (hnotlt (-τ z) (-τ y) (hγz.symm ▸ hz) (hγy.symm ▸ hy)
          (neg_nonpos.mpr (hτ y hy).1.le)))
        (le_of_not_gt (hnotlt (-τ y) (-τ z) (hγy.symm ▸ hy) (hγz.symm ▸ hz)
          (neg_nonpos.mpr (hτ z hz).1.le)))
    exact hγy.symm.trans ((congrArg γ hunique).trans hγz)
  have hsurj : SurjOn π (tailoringCoreSection I φEnd β)
      {z | z ∈ tailoringLegendreConic I φEnd ∧ φ z.1 = D ^ 2 * β ^ 2 / 2} := by
    intro w hw
    obtain ⟨t, ht, hz⟩ := hback β hβb F hF K hK.1 (hode K hK) w hw.1 hw.2
      ((hgeom β hβg).2 w hw.1 hw.2)
    let z := (F t (K, w)).2
    have he : F t (K, w) = (K, z) := Prod.ext (hfst _ _) rfl
    have hinv : (F (-t) (K, z)).2 = w := by
      rw [← he, ← F.map_add, neg_add_cancel, F.map_zero_apply]
    have htime : -t = τ z := (hτ z hz).2.2.1 (-t) (by simpa only [hinv] using hw.2)
    exact ⟨z, hz, by change (F (τ z) (K, z)).2 = w; rw [← htime]; exact hinv⟩
  refine ⟨τ, hτ, ⟨hmap, hinj, hsurj⟩, ?_⟩
  intro x hx
  obtain ⟨t, _, he, _, Vlocal, hVlocal, hxV, τlocal, hτlocal, hcenter, hlevel, hmaplocal⟩ :=
    hsmooth β hβs F hF K hK.1 (hode K hK) x hx ((hgeom β hβg).1 (lgCover x) hx)
  exact ⟨Vlocal, hVlocal, hxV, τlocal, hτlocal,
    hcenter.trans ((hτ (lgCover x) hx).2.2.1 t he), hlevel, hmaplocal⟩

end FsFltz
