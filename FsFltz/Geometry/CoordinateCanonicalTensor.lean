import FsFltz.Geometry.CoordinateCoframePullback

/-!
# Canonical-square coefficients in an arbitrary native coordinate model

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 794–814. The native interior and boundary–radial models
need not be definitionally the encoded ambient model. Inverse-coframe
evaluation recovers the scalar of an arbitrary prescribed canonical tensor;
reconstruction then identifies its whole pullback, rather than assuming a
coframe-generator representation of that tensor.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry

/-- Inverse-coframe evaluation of a tensor in the actual native coordinate
model. This is the same coefficient as `squaredCoframeCoefficient` when
the source is the encoded ambient model. -/
def coordinateSquaredCoframeCoefficient {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : F →L[ℝ] TangentCoordinates n)
    (s : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ) : ℂ :=
  s (fun i => C.inverse (verticalFrame n (i.elim id id)))

/-- The coefficient is independent of a linear identification used only
to express canonicality in the encoded tangent model. -/
theorem coordinateSquaredCoframeCoefficient_eq {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Model (2 * n) ≃L[ℝ] F)
    (C : F →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (s : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ) :
    coordinateSquaredCoframeCoefficient C s =
      squaredCoframeCoefficient (C.comp P.toContinuousLinearMap)
        (s.compContinuousLinearMap (fun _ => P.toContinuousLinearMap)) := by
  unfold coordinateSquaredCoframeCoefficient squaredCoframeCoefficient
  rw [hC.inverse_comp_of_left, ContinuousLinearMap.inverse_equiv]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- An arbitrary prescribed canonical square in native coordinates is
reconstructed from its inverse-coframe coefficient. The only use of `P`
is to express the existing canonical predicate in its encoded model. -/
theorem coordinateSquaredCoframe_reconstruction {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Model (2 * n) ≃L[ℝ] F)
    (C : F →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (J : F →L[ℝ] F)
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ)
    (hs : IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp (J.comp P.toContinuousLinearMap))
      (s.compContinuousLinearMap (fun _ => P.toContinuousLinearMap))) :
    s = coordinateSquaredCoframeCoefficient C s •
      (coordinateSquaredVolumeTensor n).compContinuousLinearMap (fun _ => C) := by
  have hCP : (C.comp P.toContinuousLinearMap).IsInvertible :=
    hC.comp ⟨P, rfl⟩
  have h := squaredCoframe_reconstruction (C.comp P.toContinuousLinearMap) hCP
    (P.symm.toContinuousLinearMap.comp (J.comp P.toContinuousLinearMap))
    (by intro v; simpa using hCJ (P v))
    (s.compContinuousLinearMap (fun _ => P.toContinuousLinearMap)) hs
  rw [← coordinateSquaredCoframeCoefficient_eq P C hC s] at h
  ext v
  have hv := congrArg (fun T => T (fun i => P.symm (v i))) h
  simpa [coframeSquaredGenerator] using hv

theorem coordinateSquaredCoframeCoefficient_ne_zero {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Model (2 * n) ≃L[ℝ] F)
    (C : F →L[ℝ] TangentCoordinates n) (hC : C.IsInvertible)
    (J : F →L[ℝ] F)
    (hCJ : ∀ v, C (J v) = coordinateComplexStructure n (C v))
    (s : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ)
    (hs : IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp (J.comp P.toContinuousLinearMap))
      (s.compContinuousLinearMap (fun _ => P.toContinuousLinearMap)))
    (hne : s ≠ 0) : coordinateSquaredCoframeCoefficient C s ≠ 0 := by
  intro hz
  have h := coordinateSquaredCoframe_reconstruction P C hC J hCJ s hs
  apply hne
  ext v
  have hv := congrArg (fun T => T v) h
  simpa only [hz, smul_apply, smul_eq_mul, zero_mul, zero_apply] using hv

/-- Smooth original tensor coefficients and an actual smooth invertible
coframe produce a smooth scalar coefficient in any native model. -/
theorem contDiffOn_coordinateSquaredCoframeCoefficient {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Set E}
    {C : E → F →L[ℝ] TangentCoordinates n}
    {s : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ}
    (hC : ContDiffOn ℝ ∞ C U) (hinv : ∀ x ∈ U, (C x).IsInvertible)
    (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (fun x => coordinateSquaredCoframeCoefficient (C x) (s x)) U := by
  have hi : ContDiffOn ℝ ∞ (fun x => (C x).inverse) U := by
    intro x hx
    exact (hinv x hx).contDiffAt_map_inverse.comp_contDiffWithinAt x (hC x hx)
  have hframe : ContDiffOn ℝ ∞
      (fun x (i : Fin n ⊕ Fin n) => (C x).inverse (verticalFrame n (i.elim id id))) U :=
    contDiffOn_pi.mpr (fun _ => hi.clm_apply contDiffOn_const)
  let ev := (ContinuousLinearMap.id ℝ
    (ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ)).flipMultilinear
  exact (ev.contDiff.comp_contDiffOn hframe).clm_apply hs

end FsFltz.Geometry
