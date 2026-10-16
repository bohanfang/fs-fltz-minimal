import FsFltz.Geometry.CollarSmoothEvolution
import FsFltz.Geometry.FlowBridge

/-!
# Complete flow from a compact interior and cylindrical end

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 156–158, and
`sec:lean`, lines 805–814. The compact interior gives a uniform positive
local integration time. On the end, translation of the prescribed radial
integral curves gives the same two-sided lifetime at every point outside
an enlarged compact set. Uniform-time continuation produces all-real
curves; uniqueness supplies the action law, and smooth dependence supplies
joint `C∞` regularity. The resulting flow solves the specified field's
actual ODE in every chart.

The hypotheses contain the compact set, end curves and their coverage,
but no complete flow or completed Liouville manifold. Completion gluing,
the end's primitive and its radial equation are separate producers.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry
namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- A smooth field with radial integral curves covering the complement
of a compact set has a constructed smooth flow for every real time.
The end curves use logarithmic radius, so their field is `∂r` and points
outside the compact set have radius at least one. -/
theorem exists_completeLiouvilleFlow_of_cylindricalEnd {d : ℕ}
    (M : SmoothManifold d) (Z : (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothVectorField Z) {K : Set M.Point} (hK : IsCompact K)
    {B : Type*} (e : B → ℝ → M.Point)
    (hradial : ∀ b, IsMIntegralCurveOn (e b) Z (Ioi 0))
    (hcover : ∀ x ∉ K, ∃ b r, 1 ≤ r ∧ e b r = x) :
    Nonempty (CompleteLiouvilleFlow M Z) := by
  have hv := hZ.contMDiff_section
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨εK, hεK, H⟩ := CollarFlow.exists_compact_uniform_local_integralCurve hv₁ hK
  let ε : ℝ := min εK (1 / 2)
  have hε : 0 < ε := lt_min hεK (by norm_num)
  have hεKle : ε ≤ εK := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hlocal : ∀ x : M.Point, ∃ γ : ℝ → M.Point,
      γ 0 = x ∧ IsMIntegralCurveOn γ Z (Ioo (-ε) ε) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨γ, hγ₀, hγ⟩ := H x hx
      exact ⟨γ, hγ₀, hγ.mono (Ioo_subset_Ioo (neg_le_neg hεKle) hεKle)⟩
    · obtain ⟨b, r, hr, hbr⟩ := hcover x hx
      refine ⟨e b ∘ (· + r), by simpa only [comp_apply, zero_add] using hbr, ?_⟩
      apply ((hradial b).comp_add r).mono
      intro t ht
      change 0 < t + r
      have htlow := ht.1
      linarith
  have hglobal := exists_isMIntegralCurve_of_isMIntegralCurveOn hv₁ hε hlocal
  choose γ hγ₀ hγ using hglobal
  let φ : ℝ → M.Point → M.Point := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hcomp : ∀ s t x, φ (s + t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := CollarFlow.contMDiff_joint_of_isMIntegralCurve hv φ hself hγ
  let F : Flow ℝ M.Point := ⟨φ, hs.continuous, hcomp, hself⟩
  refine ⟨⟨F, hs, ?_⟩⟩
  intro x
  exact (isMIntegralCurve_iff_chart_solves M Z _
    ((hs.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp (hγ x)

end SmoothManifold
end FsFltz.Geometry
