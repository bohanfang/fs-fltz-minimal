import FsFltz.Analysis.FiniteSupportGrowth
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The fixed nonvanishing coefficient path to one

Source: `geometric-part-fsf-proof.tex`, `sec:parameters`, choice dependencies,
lines 490–499. A fixed logarithm of each input coefficient gives the stated
path. The principal complex logarithm is one permitted choice; it is only
evaluated at the fixed nonzero coefficient, so its branch has no bearing
on smoothness in the real path parameter. The path does not assume any
geometric deformation family or path-uniform end estimate.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ContDiff Topology

variable {n : ℕ}

/-- The source's explicit path `exp((1-t) ℓ_v)`, with the fixed principal
logarithm chosen for every nonzero input coefficient. -/
def coefficientPath (I : ToricInput n) (t : ℝ)
    (v : {v : Lattice n // v ∈ I.vertices}) : ℂ :=
  Complex.exp ((1 - (t : ℂ)) * Complex.log (I.coeff v))

/-- Each coefficient path is smooth for every real parameter, including
smooth extension across both endpoints of the comparison interval. -/
theorem coefficientPath_contDiff (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    ContDiff ℝ ∞ (fun t : ℝ => coefficientPath I t v) := by
  unfold coefficientPath
  have hcast : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hsub : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℂ) - (t : ℂ)) :=
    contDiff_const.sub hcast
  exact (hsub.mul contDiff_const).cexp

/-- Joint smoothness of the finite coefficient vector. -/
theorem coefficientPath_vector_contDiff (I : ToricInput n) :
    ContDiff ℝ ∞ (coefficientPath I) := by
  exact contDiff_pi.mpr (coefficientPath_contDiff I)

/-- The exponential path never meets zero, on the whole real line. -/
theorem coefficientPath_ne_zero (I : ToricInput n) (t : ℝ)
    (v : {v : Lattice n // v ∈ I.vertices}) : coefficientPath I t v ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem coefficientPath_zero (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) : coefficientPath I 0 v = I.coeff v := by
  simp [coefficientPath, Complex.exp_log (I.coeff_ne_zero v)]

@[simp] theorem coefficientPath_one (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) : coefficientPath I 1 v = 1 := by
  simp [coefficientPath]

/-- Only the nonzero coefficient tuple is replaced. The based lattice,
actual vertices, polytope and facet bases remain the original native data. -/
def ToricInput.alongCoefficientPath (I : ToricInput n) (t : ℝ) : ToricInput n :=
  { I with
    coeff := coefficientPath I t
    coeff_ne_zero := coefficientPath_ne_zero I t }

@[simp] theorem ToricInput.alongCoefficientPath_vertices (I : ToricInput n) (t : ℝ) :
    (I.alongCoefficientPath t).vertices = I.vertices := rfl

@[simp] theorem ToricInput.alongCoefficientPath_coeff (I : ToricInput n) (t : ℝ)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    (I.alongCoefficientPath t).coeff v = coefficientPath I t v := rfl

/-- The initial input itself is recovered, including the coefficient tuple. -/
@[simp] theorem ToricInput.alongCoefficientPath_zero (I : ToricInput n) :
    I.alongCoefficientPath 0 = I := by
  have hcoeff : coefficientPath I 0 = I.coeff := funext (coefficientPath_zero I)
  cases I
  simpa only [ToricInput.alongCoefficientPath, ToricInput.mk.injEq, true_and,
    heq_eq_eq] using hcoeff

@[simp] theorem ToricInput.alongCoefficientPath_one_coeff (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) : (I.alongCoefficientPath 1).coeff v = 1 := by
  exact coefficientPath_one I v

/-- The actual fan is literally unchanged along this coefficient path. -/
@[simp] theorem faceFan_alongCoefficientPath (I : ToricInput n) (t : ℝ) :
    faceFan (I.alongCoefficientPath t) = faceFan I := rfl

/-- Consequently the literal positive-cone FLTZ link is unchanged. -/
@[simp] theorem fltzLink_alongCoefficientPath (I : ToricInput n) (t : ℝ) :
    fltzLink (I.alongCoefficientPath t) = fltzLink I := rfl

/-- The geometric support height, used in all growth estimates, is unchanged. -/
@[simp] theorem supportHeight_alongCoefficientPath (I : ToricInput n) (t : ℝ)
    (u : RealSpace n) : supportHeight (I.alongCoefficientPath t) u = supportHeight I u := rfl

/-- Nonvanishing and compactness supply one positive lower and finite
upper coefficient norm bound over the entire prescribed parameter interval. -/
theorem ToricInput.coefficientPath_uniform_norm_bounds (I : ToricInput n) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : {v : Lattice n // v ∈ I.vertices},
        A ≤ ‖coefficientPath I t v‖ ∧ ‖coefficientPath I t v‖ ≤ B := by
  let S : Set (ℝ × {v : Lattice n // v ∈ I.vertices}) := Set.Icc 0 1 ×ˢ Set.univ
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hcont : Continuous (fun x : ℝ × {v : Lattice n // v ∈ I.vertices} =>
      ‖coefficientPath I x.1 x.2‖) := by
    apply continuous_prod_of_discrete_right.mpr
    intro v
    exact (coefficientPath_contDiff I v).continuous.norm
  obtain ⟨A, hA, hlow⟩ := hcompact.exists_forall_le' hcont.continuousOn
    (fun x _ => norm_pos_iff.mpr (coefficientPath_ne_zero I x.1 x.2))
  obtain ⟨B, hupp⟩ := hcompact.exists_bound_of_continuousOn (E := ℝ) hcont.continuousOn
  refine ⟨A, |B| + 1, hA, by positivity, ?_⟩
  intro t ht v
  have hx : (t, v) ∈ S := ⟨ht, Set.mem_univ _⟩
  refine ⟨hlow (t, v) hx, ?_⟩
  have hbound := hupp (t, v) hx
  simp only [Real.norm_of_nonneg (norm_nonneg _)] at hbound
  exact hbound.trans (by linarith [le_abs_self B])

end FsFltz
