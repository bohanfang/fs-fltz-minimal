import FsFltz.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

/-!
# Continuity on the torus and smoothness in representative coordinates

Source: `sec:data`, lines 68–85, and `sec:initial`, lines 261–262, in
`geoemtric-part-fsf.tex`. Continuity is proved on the actual product of quotient
circles. Smoothness on real representative coordinates is a separate fact;
the smooth quotient manifold and descended forms are still to be constructed.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators ContDiff

variable {n : ℕ}

@[fun_prop]
theorem continuous_pairing (v : Lattice n) : Continuous (pairing v) := by
  unfold pairing
  fun_prop

@[fun_prop]
theorem continuous_integralAngle (v : Lattice n) : Continuous (integralAngle v) := by
  unfold integralAngle
  fun_prop

@[fun_prop]
theorem continuous_character (v : Lattice n) : Continuous (character v) :=
  AddCircle.continuous_toCircle.comp (continuous_integralAngle v)

@[fun_prop]
theorem continuous_monomial (c : ℂ) (v : Lattice n) : Continuous (monomial c v) := by
  unfold monomial
  fun_prop

@[fun_prop]
theorem continuous_W (I : ToricInput n) : Continuous (W I) := by
  unfold W
  fun_prop

@[fun_prop]
theorem continuous_phi0 : Continuous (phi0 (n := n)) := by
  unfold phi0 realSquaredNorm
  fun_prop

/-- The lifted Laurent polynomial is smooth in all real logarithmic and angle
coordinates. This does not choose global real angles on the quotient. -/
theorem contDiff_W_representatives (I : ToricInput n) :
    ContDiff ℝ ∞ (fun x : RealSpace n × RealSpace n => W I (x.1, angleQuotient x.2)) := by
  simp only [W_angleQuotient, pairing]
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

end FsFltz
