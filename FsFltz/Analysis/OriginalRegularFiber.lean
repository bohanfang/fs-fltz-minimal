import FsFltz.Geometry.SymplecticBridge
import FsFltz.AnalyticGeometry
import FsFltz.Compactness

/-!
# Native regularity of every original far fiber

Source: `geoemtric-part-fsf.tex`, `g:initial`, line 373;
`geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 923–930.
The positive end derivative norm gives surjectivity of the actual manifold
differential of `W`, using its proved logarithmic coordinate formula.
Far values lie beyond the valid ambient bound by the attained magnitude
maximum. A smooth manifold realization of the whole fiber and its complete
restricted Liouville primitive remain separate constructions.
-/

noncomputable section
open scoped BigOperators Manifold ContDiff ComplexConjugate

namespace FsFltz

/-- At a point with positive native derivative norm, the actual logarithmic
covector covers every complex value. The proof constructs a preimage using
the normal vector `conj G * (z/a)`. -/
theorem dW_surjective_of_a_pos {n : ℕ} (I : ToricInput n)
    (y : LGSpace n) (ha : 0 < a I y) : Function.Surjective (dW I y) := by
  intro z
  obtain ⟨q, hq⟩ := tangentComplexCoordinates_surjective
    (fun j => conj (G I y j) * (z / (a I y : ℂ)))
  refine ⟨q, ?_⟩
  rw [dW_eq_evaluation, hq]
  have hsum : (∑ j, G I y j * conj (G I y j)) = (a I y : ℂ) := by
    simp only [a, Complex.ofReal_sum, Complex.mul_conj]
  simp only [CoordinateGeometry.evaluation, ← mul_assoc, ← Finset.sum_mul, hsum]
  have hane : (a I y : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  exact mul_div_cancel₀ z hane

namespace Geometry
open SmoothManifold

/-- The positive derivative norm gives surjectivity of the actual quotient
manifold differential, using the established native cover tangent bridge. -/
theorem complexDifferential_W_surjective_of_a_pos {n : ℕ} (I : ToricInput n)
    (y : (lgManifold n).Point) (ha : 0 < a I y) :
    Function.Surjective (complexDifferential (lgManifold n) (W I) y) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  intro z
  obtain ⟨q, hq⟩ := dW_surjective_of_a_pos I (lgCover x) ha z
  refine ⟨lgCoverTangent x q, ?_⟩
  rw [complexDifferential_W_lgCover, hq]

/-- The far-value region contains no critical point of `W`. The attained
magnitude maximum and valid ambient bound prove the positive derivative
norm; neither regularity nor a maximum certificate is supplied as input. -/
theorem complexDifferential_W_surjective_of_far_value {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (y : (lgManifold n).Point) (hy : R ≤ ‖W I y‖) :
    Function.Surjective (complexDifferential (lgManifold n) (W I) y) := by
  have hphi := phi0_gt_of_far_value I Aamb R
    (sublevelMaximumAttained I Aamb hamb.1.le) ((le_max_right _ _).trans_lt hR) y hy
  exact complexDifferential_W_surjective_of_a_pos I y (hamb.2 y hphi.le).1

/-- The literal positive real far-fiber value is regular in the precise
native sense required by `FullFiberModel.regularValue`. This includes rank
one and does not assume a smooth realization of the fiber. -/
theorem original_W_far_regularValue {n : ℕ} (I : ToricInput n)
    {Aamb R : ℝ} (hamb : AmbientEndBound I Aamb)
    (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)
    (y : (lgManifold n).Point) (hy : W I y = (R : ℂ)) :
    Function.Surjective (complexDifferential (lgManifold n) (W I) y) := by
  have hRpos : 0 < R := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hR)
  apply complexDifferential_W_surjective_of_far_value I hamb hR y
  rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]

end Geometry

end FsFltz
