import FsFltz.Geometry.CanonicalLine
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Module.RingHom

/-!
# Complex coframes for arbitrary almost complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The equation `J² = -id` makes a real tangent
space into a complex vector space. A complex basis gives an actual coframe;
no pointwise frame or nonzero canonical tensor is assumed. The same
construction applies in dimension zero.
-/

noncomputable section

namespace FsFltz.Geometry

/-- A real complex structure on a `2n`-dimensional space admits continuous
complex coordinates. Continuity follows from finite real dimension. -/
theorem exists_complexCoordinates {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2 * n) (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v) :
    ∃ C : E ≃L[ℝ] (Fin n → ℂ), ∀ v, C (J v) = Complex.I • C v := by
  have hsq : J.toLinearMap * J.toLinearMap = -1 := by
    ext v
    exact hJ v
  let a : ℂ →ₐ[ℝ] Module.End ℝ E := Complex.liftAux J.toLinearMap hsq
  let : Module ℂ E := Module.compHom E a.toRingHom
  have hsmul (c : ℂ) (v : E) : c • v = c.re • v + c.im • J v := by
    change (a c) v = _
    rfl
  let : IsScalarTower ℝ ℂ E := ⟨by
    intro r c v
    simp only [hsmul, Complex.smul_re, Complex.smul_im,
      smul_add, smul_smul]
    rfl⟩
  let : Module.Finite ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have hdimC : Module.finrank ℂ E = n := by
    have h := Module.finrank_mul_finrank ℝ ℂ E
    rw [Complex.finrank_real_complex, hdim] at h
    omega
  let e : E ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofFinrankEq E (Fin n → ℂ) (by
    simpa using hdimC)
  refine ⟨(e.restrictScalars ℝ).toContinuousLinearEquiv, ?_⟩
  intro v
  change e (J v) = Complex.I • e v
  have hi : Complex.I • v = J v := by simp [hsmul]
  rw [← hi, e.map_smul]

/-- Every real almost complex structure in the ambient model has a complex
coframe, including the unique coframe on the zero-dimensional model. -/
theorem exists_complexCoframe {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    ∃ C : Model (2 * n) ≃L[ℝ] TangentCoordinates n,
      ∀ v, C (J v) = coordinateComplexStructure n (C v) := by
  obtain ⟨e, he⟩ := exists_complexCoordinates (n := n) (by simp [Model]) J hJ
  refine ⟨e.trans (complexifyTangentCoordinatesEquiv n).symm, ?_⟩
  intro v
  apply (complexifyTangentCoordinatesEquiv n).injective
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    complexifyTangentCoordinatesEquiv_apply, complexify_coordinateComplexStructure]
  change e (J v) = Complex.I • ((complexifyTangentCoordinatesEquiv n)
    ((complexifyTangentCoordinatesEquiv n).symm (e v)))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact he v

/-- Rank one holds for every almost complex structure, without an assumed
coframe or an assumed nonvanishing section. -/
theorem canonicalFiber_finrank_of_complexStructure {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    Module.finrank ℂ (canonicalSubmodule J) = 1 := by
  obtain ⟨C, hC⟩ := exists_complexCoframe J hJ
  exact canonicalFiber_finrank C J hC

theorem squaredCanonicalFiber_finrank_of_complexStructure {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    Module.finrank ℂ (squaredCanonicalSubmodule J) = 1 := by
  obtain ⟨C, hC⟩ := exists_complexCoframe J hJ
  exact squaredCanonicalFiber_finrank C J hC

/-- The natural multiplication map on genuine canonical tensor squares is
bijective for every almost complex structure. -/
theorem canonicalSquareMap_bijective {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    Function.Bijective (canonicalSquareMap J) := by
  obtain ⟨C, hC⟩ := exists_complexCoframe J hJ
  rw [← canonicalSquareEquiv_toLinearMap C J hC]
  exact (canonicalSquareEquiv C J hC).bijective

/-- The equivalence uses the natural multiplication map as its forward
map; the coframe is only used to prove that this map is bijective. -/
def canonicalSquareEquivOfComplexStructure {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    TensorProduct ℂ (canonicalSubmodule J) (canonicalSubmodule J) ≃ₗ[ℂ]
      squaredCanonicalSubmodule J :=
  LinearEquiv.ofBijective (canonicalSquareMap J) (canonicalSquareMap_bijective J hJ)

@[simp] theorem canonicalSquareEquivOfComplexStructure_toLinearMap {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v) :
    (canonicalSquareEquivOfComplexStructure J hJ).toLinearMap = canonicalSquareMap J := rfl

end FsFltz.Geometry
