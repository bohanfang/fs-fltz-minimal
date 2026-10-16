import FsFltz.Analysis.SmoothRoundingProfile
import FsFltz.Analysis.RoundingProfileBoundary
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Mul

/-!
# Smooth convex gluing of an end potential

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 626–631.
The existing smooth convex maximum glues an end potential to a quadratic
near the origin. These analytic lemmas are prerequisites of the actual
compatible potential; they do not assert its existence.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz

namespace RoundingProfile

/-- A native rounding profile is monotone in the product order. -/
lemma monotone {eps : ℝ} (m : RoundingProfile eps) : Monotone m.toFun := by
  intro p q hpq
  exact (m.monotone_first p.2 hpq.1).trans (m.monotone_second q.1 hpq.2)

/-- A convex increasing profile composed with two convex functions is convex. -/
lemma convexOn_comp {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {eps : ℝ} (m : RoundingProfile eps) {s : Set E} {f g : E → ℝ}
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun x => m.toFun (f x, g x)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (m.monotone ⟨hf.2 hx hy ha hb hab, hg.2 hx hy ha hb hab⟩).trans
    (m.convex.2 (mem_univ (f x, g x)) (mem_univ (f y, g y)) ha hb hab)

end RoundingProfile

namespace SmoothRounding

/-- The constructed smooth maximum commutes with simultaneous translation. -/
lemma smoothMax_translate (eps x y t : ℝ) :
    smoothMax eps (x + t, y + t) = smoothMax eps (x, y) + t := by
  unfold smoothMax
  dsimp
  rw [show x + t - (y + t) = x - y by ring]
  ring

/-- Any shared convexity correction is preserved by the smooth maximum.
Taking the correction to be a positive quadratic retains uniform convexity. -/
lemma smoothMax_convexOn_sub {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {eps : ℝ} (heps : 0 < eps) {s : Set E} {f g q : E → ℝ}
    (hf : ConvexOn ℝ s (fun x => f x - q x))
    (hg : ConvexOn ℝ s (fun x => g x - q x)) :
    ConvexOn ℝ s (fun x => smoothMax eps (f x, g x) - q x) := by
  have h := (roundingProfile eps heps).convexOn_comp hf hg
  apply h.congr
  intro x _
  change smoothMax eps (f x - q x, g x - q x) = _
  have ht := smoothMax_translate eps (f x - q x) (g x - q x) (q x)
  simp only [sub_add_cancel] at ht
  linarith

/-- With a strict gap the smooth maximum is literally its first argument. -/
lemma smoothMax_eq_first {eps x y : ℝ} (heps : 0 < eps) (h : y + eps ≤ x) :
    smoothMax eps (x, y) = x := by
  rw [smoothMax_exact heps (x, y) (by
    dsimp
    rw [abs_of_nonneg (by linarith)]
    linarith), max_eq_left (by linarith)]

/-- With a strict gap the smooth maximum is literally its second argument. -/
lemma smoothMax_eq_second {eps x y : ℝ} (heps : 0 < eps) (h : x + eps ≤ y) :
    smoothMax eps (x, y) = y := by
  rw [smoothMax_exact heps (x, y) (by
    dsimp
    rw [abs_of_nonpos (by linarith)]
    linarith), max_eq_right (by linarith)]

/-- Smooth gluing across the one point where the end potential need not be
smooth: continuity and the strict gap supply an unchanged neighborhood. -/
lemma smoothMax_contDiff_of_gap_at_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eps : ℝ} (heps : 0 < eps) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (hgs : ∀ x ≠ 0, ContDiffAt ℝ ∞ g x) (hgap : g 0 + eps < f 0) :
    ContDiff ℝ ∞ (fun x => smoothMax eps (f x, g x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply hf.contDiffAt.congr_of_eventuallyEq
    have hneigh : ∀ᶠ x in 𝓝 (0 : E), g x + eps < f x :=
      (isOpen_lt (hg.add continuous_const) hf.continuous).eventually_mem hgap
    filter_upwards [hneigh] with x hx
    exact smoothMax_eq_first heps hx.le
  · exact (smoothMax_contDiff eps).contDiffAt.comp x
      (hf.contDiffAt.prodMk (hgs x hx))

end SmoothRounding

namespace PotentialExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit extension used in the compatible-potential construction. -/
def extend (f : E → ℝ) (a b eps : ℝ) (x : E) : ℝ :=
  SmoothRounding.smoothMax eps (a * ‖x‖ ^ 2 + b, f x)

/-- Convexity after subtracting a common quadratic survives the gluing. -/
theorem convex_sub_quadratic {f : E → ℝ} {a b c eps : ℝ}
    (heps : 0 < eps) (hca : c ≤ a)
    (hf : ConvexOn ℝ univ (fun x => f x - c * ‖x‖ ^ 2)) :
    ConvexOn ℝ univ (fun x => extend f a b eps x - c * ‖x‖ ^ 2) := by
  apply SmoothRounding.smoothMax_convexOn_sub heps _ hf
  have hnorm : ConvexOn ℝ (univ : Set E) (fun x => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have h := (hnorm.smul (sub_nonneg.mpr hca)).add_const b
  apply h.congr
  intro x _
  simp only [Pi.add_apply, smul_eq_mul]
  ring

/-- The extension is globally smooth, although the input is only smooth away
from the origin. -/
theorem contDiff_extend {f : E → ℝ} {a b eps : ℝ}
    (heps : 0 < eps) (heb : eps < b) (hf : Continuous f) (hf0 : f 0 = 0)
    (hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (extend f a b eps) := by
  apply SmoothRounding.smoothMax_contDiff_of_gap_at_zero heps
    ((contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const) hf hfs
  simpa [hf0] using heb

omit [InnerProductSpace ℝ E] in
/-- The extension equals the selected quadratic on an actual neighborhood of
the origin. -/
theorem eventually_extend_eq_quadratic {f : E → ℝ} {a b eps : ℝ}
    (heps : 0 < eps) (heb : eps < b) (hf : Continuous f) (hf0 : f 0 = 0) :
    ∀ᶠ x in 𝓝 (0 : E), extend f a b eps x = a * ‖x‖ ^ 2 + b := by
  have hq : Continuous (fun x : E => a * ‖x‖ ^ 2 + b) :=
    (continuous_const.mul (continuous_norm.pow 2)).add continuous_const
  have hgap : f 0 + eps < a * ‖(0 : E)‖ ^ 2 + b := by simpa [hf0] using heb
  filter_upwards [(isOpen_lt (hf.add continuous_const) hq).eventually_mem hgap]
    with x hx
  exact SmoothRounding.smoothMax_eq_first heps hx.le

omit [InnerProductSpace ℝ E] in
/-- A quantitative quadratic lower bound forces exact agreement outside a
finite radius; no asymptotic or germ equality replaces this assertion. -/
theorem extend_eq_of_radius {f : E → ℝ} {a b d eps R : ℝ}
    (heps : 0 < eps) (had : a ≤ d) (hR : 0 ≤ R)
    (hgap : b + eps ≤ (d - a) * R ^ 2)
    (hf : ∀ x, d * ‖x‖ ^ 2 ≤ f x) {x : E} (hx : R ≤ ‖x‖) :
    extend f a b eps x = f x := by
  apply SmoothRounding.smoothMax_eq_second heps
  have hsq : R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hmul := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr had)
  have hlower := hf x
  nlinarith

/-- A globally smooth extension with retained uniform convexity and literal
end agreement. The hypotheses concern the end function to be constructed,
not a geometric endpoint or comparison chain. -/
theorem exists_smooth_extension {f : E → ℝ} {a c d : ℝ}
    (hca : c ≤ a) (had : a < d) (hf : Continuous f) (hf0 : f 0 = 0)
    (hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x)
    (hconv : ConvexOn ℝ univ (fun x => f x - c * ‖x‖ ^ 2))
    (hlower : ∀ x, d * ‖x‖ ^ 2 ≤ f x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧
      ConvexOn ℝ univ (fun x => g x - c * ‖x‖ ^ 2) ∧
      (∀ᶠ x in 𝓝 (0 : E), g x = a * ‖x‖ ^ 2 + 1) ∧
      ∃ R > 0, ∀ x, R ≤ ‖x‖ → g x = f x := by
  refine ⟨extend f a 1 (1 / 2), contDiff_extend (by norm_num) (by norm_num)
    hf hf0 hfs, convex_sub_quadratic (by norm_num) hca hconv,
    eventually_extend_eq_quadratic (by norm_num) (by norm_num) hf hf0, ?_⟩
  let R := Real.sqrt ((3 / 2) / (d - a))
  have hda : 0 < d - a := sub_pos.mpr had
  have hq : 0 < (3 / 2 : ℝ) / (d - a) := div_pos (by norm_num) hda
  have hR : 0 < R := Real.sqrt_pos.mpr hq
  refine ⟨R, hR, fun x hx => extend_eq_of_radius (by norm_num) had.le hR.le ?_ hlower hx⟩
  dsimp [R]
  rw [Real.sq_sqrt hq.le, mul_div_cancel₀ _ hda.ne']
  norm_num

end PotentialExtension
end FsFltz
