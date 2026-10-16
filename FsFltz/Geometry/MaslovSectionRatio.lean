import FsFltz.Geometry.CanonicalBundle
import FsFltz.Geometry.FixedComplexMaslov

/-!
# The actual scalar ratio of two squared canonical sections

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
Equal compatible complex structures put two nonzero sections in the same
complex line. Its pointwise scalar ratio is derived, and its smoothness
is proved in the constructed local complex coframes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

/-- A nonzero squared canonical tensor generates its actual canonical line. -/
theorem exists_unique_squaredCanonicalTensor_ratio {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v)
    (s r : SquaredCanonicalTensor n)
    (hs : IsSquaredCanonicalTensor J s) (hr : IsSquaredCanonicalTensor J r)
    (hs0 : s ≠ 0) : ∃! c : ℂ, r = c • s := by
  obtain ⟨C, hC⟩ := exists_complexCoframe J hJ
  let e := squaredCanonicalFiberCoordinateEquiv C J hC
  let S : squaredCanonicalSubmodule J := ⟨s, hs⟩
  let R : squaredCanonicalSubmodule J := ⟨r, hr⟩
  have ha : e S ≠ 0 := by
    intro h
    have hz : S = 0 := e.injective (by simpa using h)
    exact hs0 (congrArg Subtype.val hz)
  have he : R = (e R / e S) • S := by
    apply e.injective
    simp only [map_smul, smul_eq_mul]
    exact (div_mul_cancel₀ (e R) ha).symm
  refine ⟨e R / e S, congrArg Subtype.val he, ?_⟩
  intro c hc
  apply smul_left_injective ℂ hs0
  exact hc.symm.trans (congrArg Subtype.val he)

namespace MaslovRepresentative

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s r : MaslovRepresentative M eta) (hJ : r.J = s.J)

include hJ in
theorem exists_unique_sectionRatio (x : M.Point) :
    ∃! c : ℂ, r.tensor x = c • s.tensor x :=
  exists_unique_squaredCanonicalTensor_ratio (s.J x) (s.compatible.2.1 x)
    (s.tensor x) (r.tensor x) (s.canonical x)
    (by rw [← hJ]; exact r.canonical x) (s.nowhereZero x)

/-- The derived scalar relating the two actual sections; no ratio is input. -/
def sectionRatio (x : M.Point) : ℂ :=
  Classical.choose (s.exists_unique_sectionRatio r hJ x).exists

theorem sectionRatio_spec (x : M.Point) :
    r.tensor x = s.sectionRatio r hJ x • s.tensor x :=
  Classical.choose_spec (s.exists_unique_sectionRatio r hJ x).exists

theorem sectionRatio_ne_zero (x : M.Point) : s.sectionRatio r hJ x ≠ 0 := by
  intro hz
  exact r.nowhereZero x ((s.sectionRatio_spec r hJ x).trans
    ((congrArg (fun c : ℂ => c • s.tensor x) hz).trans (zero_smul ℂ (s.tensor x))))

theorem sectionRatio_eq_one_of_tensor_eq (x : M.Point)
    (he : r.tensor x = s.tensor x) : s.sectionRatio r hJ x = 1 := by
  apply smul_left_injective ℂ (s.nowhereZero x)
  exact (s.sectionRatio_spec r hJ x).symm.trans (he.trans (one_smul ℂ (s.tensor x)).symm)

/-- Smoothness of the derived ratio follows from the two actual smooth
sections and the locally constructed invertible complex coframe. -/
theorem sectionRatio_smooth :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ (s.sectionRatio r hJ) := by
  intro a
  let c := chartAt (Model (2 * n)) a
  have ha : c a ∈ c.target := c.map_source (mem_chart_source _ a)
  obtain ⟨C₀, V, hVc, hVo, haV, hC, hinv, hCJ⟩ :=
    exists_smooth_local_complexCoframe c.open_target ha (s.compatible.1 a)
      (fun y hy => almostComplexInChart_sq M a s.J s.compatible.2.1 y hy)
  let C := fun y => projectedComplexCoframe C₀ (almostComplexInChart M a s.J y)
  let cs := fun y => squaredCoframeCoefficient (C y) (squaredTensorInChart M a s.tensor y)
  let cr := fun y => squaredCoframeCoefficient (C y) (squaredTensorInChart M a r.tensor y)
  have hs : ContDiffOn ℝ ∞ cs V :=
    contDiffOn_squaredCoframeCoefficient hC hinv ((s.smooth a).mono hVc)
  have hr : ContDiffOn ℝ ∞ cr V :=
    contDiffOn_squaredCoframeCoefficient hC hinv ((r.smooth a).mono hVc)
  have hn (y) (hy : y ∈ V) : cs y ≠ 0 :=
    s.coframeCoefficient_ne_zero a (C y) (hinv y hy) y (hVc hy) (hCJ y hy)
  have he (y) (hy : y ∈ V) : s.sectionRatio r hJ (c.symm y) = cr y / cs y := by
    have ht := s.sectionRatio_spec r hJ (c.symm y)
    have hcoeff : cr y = s.sectionRatio r hJ (c.symm y) * cs y := by
      change r.tensor (c.symm y) _ = _
      rw [ht]
      rfl
    rw [hcoeff, mul_div_cancel_right₀ _ (hn y hy)]
  have hd : ContDiffAt ℝ ∞ (fun y => s.sectionRatio r hJ (c.symm y)) (c a) := by
    have hdiv : ContDiffOn ℝ ∞ (fun y => cr y / cs y) V := by
      convert hr.mul (hs.inv hn) using 1
      funext y
      exact div_eq_mul_inv _ _
    apply (hdiv.contDiffAt (hVo.mem_nhds haV)).congr_of_eventuallyEq
    filter_upwards [hVo.mem_nhds haV] with y hy
    exact he y hy
  have hcs : ContMDiffAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ c a :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds (mem_chart_source _ a))
  apply (hd.contMDiffAt.comp a hcs).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ a)] with x hx
  exact congrArg (s.sectionRatio r hJ) (c.left_inv hx).symm

end MaslovRepresentative
end FsFltz.Geometry
