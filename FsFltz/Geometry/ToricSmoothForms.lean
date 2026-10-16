import FsFltz.Geometry.SmoothForms
import FsFltz.Geometry.QuotientFormBridge

/-!
# Smoothness of the prescribed quotient primitives

The literal forms of `sec:data`, lines 68–97 of `geoemtric-part-fsf.tex`,
are smooth in their actual quotient atlases, including rank zero. Smoothness
is a foundation in the handoff `sec:lean`, lines 778–814; no end bound,
Liouville completeness, or geometric comparison is asserted here.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold

theorem isSmoothForm_lgAngleCovector {n : ℕ} (j : Fin n) :
    (lgManifold n).IsSmoothForm (covectorForm (lgManifold n) (lgAngleCovector j)) :=
  isSmoothForm_phaseCovector (lgManifold n) (contMDiff_lg_circleCoordinate j)

theorem isSmoothForm_cotangentAngleCovector {n : ℕ} (j : Fin n) :
    (cotangentManifold n).IsSmoothForm
      (covectorForm (cotangentManifold n) (cotangentAngleCovector j)) :=
  isSmoothForm_phaseCovector (cotangentManifold n) (contMDiff_cotangent_circleCoordinate j)

theorem isSmoothForm_lgLogCovector {n : ℕ} (j : Fin n) :
    (lgManifold n).IsSmoothForm (covectorForm (lgManifold n) (lgLogCovector j)) :=
  isSmoothForm_differentialCovector (lgManifold n) (contMDiff_lgLogCoordinate j)

theorem isSmoothForm_cotangentMomentumCovector {n : ℕ} (j : Fin n) :
    (cotangentManifold n).IsSmoothForm
      (covectorForm (cotangentManifold n) (cotangentMomentumCovector j)) :=
  isSmoothForm_differentialCovector (cotangentManifold n)
    (contMDiff_cotangentMomentumCoordinate j)

/-- Smoothness of the literal `sum u_j d theta_j`, with no global real angles. -/
theorem isSmoothForm_lambda0Form (n : ℕ) :
    (lgManifold n).IsSmoothForm (lambda0Form n) := by
  classical
  have h : lambda0Form n = ∑ j : Fin n,
      (fun y => y.1 j • covectorForm (lgManifold n) (lgAngleCovector j) y) := by
    funext y
    ext v
    simp [lambda0Form, covectorForm]
  rw [h]
  exact IsSmoothForm.sum Finset.univ _ (fun j _ =>
    (isSmoothForm_lgAngleCovector j).function_smul (contMDiff_lgLogCoordinate j))

theorem isSmoothForm_superpotentialPlaneForm {n : ℕ} (I : ToricInput n) :
    (lgManifold n).IsSmoothForm (superpotentialPlaneForm I) := by
  have hW := contMDiff_W_lgManifold I
  have hre : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => (W I y).re) :=
    Complex.reCLM.contDiff.contMDiff.comp hW
  have him : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞
      (fun y : (lgManifold n).Point => (W I y).im) :=
    Complex.imCLM.contDiff.contMDiff.comp hW
  have hdre := isSmoothForm_complexDifferential_comp (lgManifold n) hW Complex.reCLM
  have hdim := isSmoothForm_complexDifferential_comp (lgManifold n) hW Complex.imCLM
  have h := ((hdim.function_smul hre).sub (hdre.function_smul him)).smul (1 / 2 : ℝ)
  convert h using 1
  funext y
  ext v
  simp [superpotentialPlaneForm, covectorForm]

/-- The prescribed primitive is smooth for every real `K`; nonnegative `K`
is required later for symplecticity, not for smoothness. -/
theorem isSmoothForm_lambdaKForm {n : ℕ} (I : ToricInput n) (K : ℝ) :
    (lgManifold n).IsSmoothForm (lambdaKForm I K) :=
  (isSmoothForm_lambda0Form n).add ((isSmoothForm_superpotentialPlaneForm I).smul K)

theorem isSmoothForm_lambdaCanForm (n : ℕ) :
    (cotangentManifold n).IsSmoothForm (lambdaCanForm n) := by
  classical
  have h : lambdaCanForm n = ∑ j : Fin n,
      (fun y => y.2 j • covectorForm (cotangentManifold n) (cotangentAngleCovector j) y) := by
    funext y
    ext v
    simp [lambdaCanForm, covectorForm]
  rw [h]
  exact IsSmoothForm.sum Finset.univ _ (fun j _ =>
    (isSmoothForm_cotangentAngleCovector j).function_smul
      (contMDiff_cotangentMomentumCoordinate j))

end FsFltz.Geometry
