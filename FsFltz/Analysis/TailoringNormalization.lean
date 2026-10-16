import FsFltz.Analysis.TailoringNormalizedMargin
import FsFltz.Analysis.OriginalRoundedBoundary

/-!
# Exact normalization at the coefficient-path/tailoring junction

Source: `geometric-part-fsf-proof.tex`, `eq:normalizedrounding`, lines
1259–1262 and the marked deformation, lines 1304–1314. The same profile,
literal full truncation and native primitive are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace FsFltz.Geometry.SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- Real scalar normalization squares the actual plane pullback primitive. -/
theorem planePullbackForm_const_smul {f : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f) (c : ℝ) :
    M.planePullbackForm (c • f) = c ^ 2 • M.planePullbackForm f := by
  have hd (x : M.Point) : complexDifferential M (c • f) x =
      c • complexDifferential M f x :=
    ((hf.mdifferentiable (by simp) x).hasMFDerivAt.const_smul c).mfderiv
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  change evalOne (M.planePullbackForm (c • f)) x (v 0) =
    c ^ 2 * evalOne (M.planePullbackForm f) x (v 0)
  rw [M.evalOne_planePullbackForm, M.evalOne_planePullbackForm, hd]
  simp only [Pi.smul_apply, smul_apply, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  ring

end FsFltz.Geometry.SmoothManifold

namespace FsFltz

open Geometry
variable {n : ℕ}

/-- The actual zero endpoint of tailoring is the normalized coefficient-one
endpoint of the preceding path. -/
theorem tailoringFamily_zero_scale (I : ToricInput n) (β : ℝ) :
    tailoringFamily I β 0 = Real.exp (-β) • W (I.alongCoefficientPath 1) := by
  funext y
  rw [tailoringFamily_zero, ← W_tailoringNormalizedInput,
    W_tailoringNormalizedInput_scale]
  rfl

/-- Native ambient primitives match exactly at the normalization junction. -/
theorem tailoringFamily_zero_rankTwoPrimitive (I : ToricInput n) (β K : ℝ)
    (α : (lgManifold n).Form 1) :
    (lgManifold n).rankTwoPrimitive α (tailoringFamily I β 0) K =
      (lgManifold n).rankTwoPrimitive α (W (I.alongCoefficientPath 1))
        (K / Real.exp β ^ 2) := by
  simp only [Geometry.SmoothManifold.rankTwoPrimitive]
  rw [tailoringFamily_zero_scale,
    (lgManifold n).planePullbackForm_const_smul
      (contMDiff_W_lgManifold (I.alongCoefficientPath 1)), smul_smul]
  simp only [Real.exp_neg, inv_pow, div_eq_mul_inv]

/-- The source's factor `R²` makes the rounded defining scalars identical. -/
theorem tailoringFamily_zero_normalized_rounding (I : ToricInput n)
    (β A : ℝ) (φ : LGSpace n → ℝ) (m : RoundingChoice) (y : LGSpace n) :
    m.profile.toFun (φ y - A,
      Real.exp β ^ 2 * (Complex.normSq (tailoringFamily I β 0 y) - 1)) =
    m.profile.toFun (φ y - A,
      Complex.normSq (W (I.alongCoefficientPath 1) y) - Real.exp β ^ 2) := by
  congr 1
  refine Prod.ext ?_ ?_
  · rfl
  rw [tailoringFamily_zero_scale]
  simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal, Real.exp_neg]
  field_simp

/-- Normalization preserves the entire marked fiber and its truncation. -/
theorem tailoringFamily_zero_truncation (I : ToricInput n) (β Aminus : ℝ)
    (φ : LGSpace n → ℝ) :
    {y | tailoringFamily I β 0 y = 1 ∧ φ y ≤ Aminus} =
      {y | W (I.alongCoefficientPath 1) y = (Real.exp β : ℂ) ∧ φ y ≤ Aminus} := by
  ext y
  rw [tailoringFamily_zero_scale]
  simp only [Set.mem_ofPred_eq, Pi.smul_apply, Complex.real_smul, Real.exp_neg,
    Complex.ofReal_inv]
  have hne : (Real.exp β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero β)
  rw [inv_mul_eq_iff_eq_mul₀ hne, mul_one]

end FsFltz
