import FsFltz.Geometry.PrescribedGradingBridge

/-!
# Pointwise compatibility of the prescribed ambient complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 220–243, and
`sec:lean`, lines 794–814. The actual exterior derivatives of `lambdaKForm`
and `lambdaCanForm` are invariant under the prescribed intrinsic complex
fields and positive on `(v, Jv)` for nonzero tangent vectors. The logarithmic
positivity holds for every `K ≥ 0`. Smoothness of the complex fields and
packaging the Maslov representatives are handled separately.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators ComplexConjugate

namespace FsFltz

namespace CoordinateGeometry

/-- Simultaneous standard complex rotation preserves both summands of the
coordinate symplectic form, for every real coefficient. -/
theorem omega_complexStructure_invariant {n : ℕ} (G q r : Fin n → ℂ) (K : ℝ) :
    omega G K (complexStructure q) (complexStructure r) = omega G K q r := by
  have hi (z w : ℂ) : conj (Complex.I * z) * (Complex.I * w) = conj z * w := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  unfold omega
  rw [evaluation_complexStructure, evaluation_complexStructure, hi]
  simp only [complexStructure, hi]

end CoordinateGeometry

namespace Geometry
open SmoothManifold

theorem omegaKCoordinates_coordinateComplexStructure_invariant {n : ℕ}
    (I : ToricInput n) (K : ℝ) (y : LGSpace n) (q r : TangentCoordinates n) :
    omegaKCoordinates I K y (coordinateComplexStructure n q) (coordinateComplexStructure n r) =
      omegaKCoordinates I K y q r := by
  change omegaKCoordinates I K y (complexStructureCoordinates q)
    (complexStructureCoordinates r) = _
  rw [omegaKCoordinates_eq_omega, tangentComplexCoordinates_complexStructure,
    tangentComplexCoordinates_complexStructure, CoordinateGeometry.omega_complexStructure_invariant,
    ← omegaKCoordinates_eq_omega]

theorem omega0Coordinates_coordinateComplexStructure_invariant {n : ℕ}
    (q r : TangentCoordinates n) :
    omega0Coordinates (coordinateComplexStructure n q) (coordinateComplexStructure n r) =
      omega0Coordinates q r := by
  unfold omega0Coordinates
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateComplexStructure_apply, Pi.neg_apply]
  ring

/-- The cotangent standard form is strictly positive on `(q,Jq)` for every
nonzero real tangent vector, including the vacuous rank-zero case. -/
theorem omega0Coordinates_coordinateComplexStructure_positive {n : ℕ}
    (q : TangentCoordinates n) (hq : q ≠ 0) :
    0 < omega0Coordinates q (coordinateComplexStructure n q) := by
  have he : ∃ j, q.1 j ≠ 0 ∨ q.2 j ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    exact Prod.ext (funext (fun j => (h j).1)) (funext (fun j => (h j).2))
  have hform : omega0Coordinates q (coordinateComplexStructure n q) =
      ∑ j, (q.1 j ^ 2 + q.2 j ^ 2) := by
    unfold omega0Coordinates
    apply Finset.sum_congr rfl
    intro j _
    simp only [coordinateComplexStructure_apply, Pi.neg_apply]
    ring
  rw [hform]
  apply Finset.sum_pos' (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨j, hj | hj⟩ := he
  · exact ⟨j, Finset.mem_univ _, add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hj) (sq_nonneg _)⟩
  · exact ⟨j, Finset.mem_univ _, add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hj)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual logarithmic exterior derivative is computed by the intrinsic
`du,dtheta` coframe at every quotient point and every tangent pair. -/
theorem exteriorDerivative_lambdaKForm_coframe {n : ℕ} (I : ToricInput n) (K : ℝ)
    (y : (lgManifold n).Point) (v w : (lgManifold n).Tangent y) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaKForm I K)) y v w =
      omegaKCoordinates I K y (lgTangentCoframe y v) (lgTangentCoframe y w) := by
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  obtain ⟨q, rfl⟩ := (lgCoverTangent_bijective x).2 v
  obtain ⟨r, rfl⟩ := (lgCoverTangent_bijective x).2 w
  rw [exteriorDerivative_lambdaKForm_lgCover, lgTangentCoframe_lgCover,
    lgTangentCoframe_lgCover]

set_option backward.isDefEq.respectTransparency false in
/-- The actual cotangent exterior derivative uses the intrinsic `dp,dtheta`
coframe, matching the source's vertical-first complex convention. -/
theorem exteriorDerivative_lambdaCanForm_coframe {n : ℕ}
    (y : (cotangentManifold n).Point) (v w : (cotangentManifold n).Tangent y) :
    evalTwo ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) y v w =
      omega0Coordinates (cotangentTangentCoframe y v) (cotangentTangentCoframe y w) := by
  obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
  obtain ⟨q, rfl⟩ := (cotangentCoverTangent_bijective x).2 v
  obtain ⟨r, rfl⟩ := (cotangentCoverTangent_bijective x).2 w
  rw [exteriorDerivative_lambdaCanForm_cotangentCover,
    cotangentTangentCoframe_cotangentCover, cotangentTangentCoframe_cotangentCover]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Symplectic invariance of the prescribed logarithmic complex field for
the actual exterior derivative, with no sign restriction on `K`. -/
theorem logarithmicAlmostComplexField_symplectic {n : ℕ} (I : ToricInput n) (K : ℝ)
    (y : (lgManifold n).Point) (v w : (lgManifold n).Tangent y) :
    evalTwo ((lgManifold n).exteriorDerivative (lambdaKForm I K)) y
      (logarithmicAlmostComplexField n y v) (logarithmicAlmostComplexField n y w) =
    evalTwo ((lgManifold n).exteriorDerivative (lambdaKForm I K)) y v w := by
  rw [exteriorDerivative_lambdaKForm_coframe, exteriorDerivative_lambdaKForm_coframe,
    lgTangentCoframe_almostComplex, lgTangentCoframe_almostComplex,
    omegaKCoordinates_coordinateComplexStructure_invariant]

/-- Strict positivity of the actual logarithmic exterior derivative under
the prescribed complex field for every `K ≥ 0`. -/
theorem logarithmicAlmostComplexField_positive {n : ℕ} (I : ToricInput n)
    {K : ℝ} (hK : 0 ≤ K) (y : (lgManifold n).Point)
    (v : (lgManifold n).Tangent y) (hv : v ≠ 0) :
    0 < evalTwo ((lgManifold n).exteriorDerivative (lambdaKForm I K)) y v
      (logarithmicAlmostComplexField n y v) := by
  rw [exteriorDerivative_lambdaKForm_coframe, lgTangentCoframe_almostComplex]
  apply omegaKCoordinates_complexStructure_pos I y hK
  intro h
  exact hv ((lgTangentCoframe_bijective y).1 (h.trans (map_zero _).symm))

/-- Symplectic invariance of the actual cotangent exterior derivative under
the prescribed cotangent complex field. -/
theorem cotangentAlmostComplexField_symplectic {n : ℕ}
    (y : (cotangentManifold n).Point) (v w : (cotangentManifold n).Tangent y) :
    evalTwo ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) y
      (cotangentAlmostComplexField n y v) (cotangentAlmostComplexField n y w) =
    evalTwo ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) y v w := by
  rw [exteriorDerivative_lambdaCanForm_coframe, exteriorDerivative_lambdaCanForm_coframe,
    cotangentTangentCoframe_almostComplex, cotangentTangentCoframe_almostComplex,
    omega0Coordinates_coordinateComplexStructure_invariant]

/-- Strict positivity of the actual cotangent exterior derivative under its
prescribed complex field. -/
theorem cotangentAlmostComplexField_positive {n : ℕ}
    (y : (cotangentManifold n).Point) (v : (cotangentManifold n).Tangent y) (hv : v ≠ 0) :
    0 < evalTwo ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) y v
      (cotangentAlmostComplexField n y v) := by
  rw [exteriorDerivative_lambdaCanForm_coframe, cotangentTangentCoframe_almostComplex]
  apply omega0Coordinates_coordinateComplexStructure_positive
  intro h
  exact hv ((cotangentTangentCoframe_bijective y).1 (h.trans (map_zero _).symm))

end Geometry
end FsFltz
