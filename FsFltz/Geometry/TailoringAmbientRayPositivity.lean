import FsFltz.Geometry.TailoringCoreOutwardRay
import FsFltz.Analysis.TailoringPoissonPositivity

/-!
# Actual ambient transversality along the whole outward cone continuation

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1784–1804.
The field is determined by the updated primitive, for every nonnegative
base coefficient. The large-radius threshold is independent of that coefficient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz
open Geometry Geometry.SmoothManifold Set Filter
open scoped Topology ContDiff Manifold
variable {n : ℕ}

/-- The outward continuation is precisely on the increasing side of its
level-one section; in particular its endpoint values are at least one. -/
theorem IsStronglyCompatibleEndPotential.eventually_coreSection_outward_base_increasing
    {I : ToricInput n} {φEnd : RealSpace n → ℝ}
    (hEnd : IsStronglyCompatibleEndPotential I φEnd) :
    ∀ᶠ β in atTop, ∀ y ∈ tailoringCoreSection I φEnd β,
      StrictMonoOn (fun t : ℝ => (tailoringFamily I β 1 (t • y.1, y.2)).re) (Ici 1) ∧
      ∀ t : ℝ, 1 ≤ t → 1 ≤ (tailoringFamily I β 1 (t • y.1, y.2)).re := by
  filter_upwards [hEnd.eventually_coreSection_outward_ray] with β hray
  intro y hy
  have hd : ∀ t ∈ Ici (1 : ℝ), ∃ d : ℝ, 0 < d ∧
      HasDerivAt (fun r : ℝ => (tailoringFamily I β 1 (r • y.1, y.2)).re) d t := by
    intro t ht
    obtain ⟨_, _, _, d, hd, _, hder⟩ := hray y hy t ht
    refine ⟨d / t, div_pos hd (lt_of_lt_of_le zero_lt_one ht), ?_⟩
    convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hder using 1 <;> rfl
  have hcont : ContinuousOn (fun r : ℝ => (tailoringFamily I β 1 (r • y.1, y.2)).re)
      (Ici 1) := by
    intro t ht
    obtain ⟨d, _, hder⟩ := hd t ht
    exact hder.continuousAt.continuousWithinAt
  have hm := strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ)) hcont (by
    intro t ht
    obtain ⟨d, hd, hder⟩ := hd t (interior_subset ht)
    rwa [hder.deriv])
  refine ⟨hm, ?_⟩
  intro t ht
  have h := hm.monotoneOn (show (1 : ℝ) ∈ Ici 1 by simp) ht ht
  have hyfiber : tailoringFamily I β 1 y = 1 := hy.2
  simpa only [one_smul, Prod.eta, hyfiber, Complex.one_re] using h

/-- The actual updated ambient field has positive real derivative of the
endpoint function everywhere on the outward continuation of its section. -/
theorem tailoringEndpoint_exists_uniform_coreSection_outward_allK_transverse
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ y ∈ tailoringCoreSection I φEnd β,
      ∀ t : ℝ, 1 ≤ t → ∀ K : ℝ, 0 ≤ K → ∃ d : ℝ, 0 < d ∧
        complexDifferential (lgManifold n) (tailoringFamily I β 1) (t • y.1, y.2)
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β 1) K) (t • y.1, y.2)) = (d : ℂ) := by
  obtain ⟨Ba, hBa, hamb⟩ :=
    tailoringEndpoint_exists_uniform_coreSection_outward_ambient_liouville
      I hφ hc hlower hEnd hR heq
  obtain ⟨_, _, _, _, Bp, _, hpair⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨Br, hray⟩ := eventually_atTop.mp hEnd.eventually_coreSection_outward_ray
  refine ⟨max Ba (max Bp Br), hBa.trans_le (le_max_left _ _), ?_⟩
  intro β hβ y hy t ht K hK
  obtain ⟨a, ha, hda⟩ := hamb β ((le_max_left _ _).trans hβ) y hy t ht
  have hr := hray β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) y hy t ht
  let x : LGSpace n := (t • y.1, y.2)
  let hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower x
  let π := (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) x hnd
  have hπ : 0 ≤ π := (hpair β
    ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) 1 (by simp) x hnd).1
  have hden : 0 < 1 + K * π := by positivity
  let b : ℝ := (tailoringFamily I β 1 x).re
  have hb : 0 < b := hr.2.2.1
  have hf : tailoringFamily I β 1 x = (b : ℂ) := by
    have hv := hr.2.1
    change tailoringFamily I β 1 x = _ at hv
    rw [hv]
    simp only [b, hv, Complex.ofReal_re]
  refine ⟨(a + (K * π / 2) * b) / (1 + K * π), by positivity, ?_⟩
  rw [(lgManifold n).complexDifferential_liouvilleVector_rankTwoPrimitive
    (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1)
    K x hnd hden.ne', hda, hf]
  simp only [π, Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_div]

end FsFltz
