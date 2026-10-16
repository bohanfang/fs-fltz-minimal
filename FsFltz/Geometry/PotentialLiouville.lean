import FsFltz.Analysis.CompatiblePotentialLegendre
import FsFltz.Geometry.SymplecticBridge

/-!
# The adapted primitive and the actual cotangent Legendre map

Source: `geometric-part-fsf-proof.tex`, `sec:original`, lines 680–688,
and `prop:endpoint`, lines 1922–1934. All forms and maps are on the existing
quotient manifolds. The primitive is the literal sum of potential gradient
coefficients times the descended angular covectors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ}

/-- The literal primitive associated to a based real potential. -/
def lambdaPotentialForm (φ : RealSpace n → ℝ) : (lgManifold n).Form 1 :=
  covectorForm (lgManifold n)
    (fun y => ∑ j, coordinateGradient φ y.1 j • lgAngleCovector j y)

/-- The quotient Legendre map preserves the angular point and changes only
the momentum coordinates. -/
def legendreMap (Φ : RealSpace n → RealSpace n) :
    (lgManifold n).Point → (cotangentManifold n).Point :=
  fun y => (y.2, Φ y.1)

def inverseLegendreMap (Ψ : RealSpace n → RealSpace n) :
    (cotangentManifold n).Point → (lgManifold n).Point :=
  fun y => (Ψ y.2, y.1)

theorem contMDiff_legendreMap {Φ : RealSpace n → RealSpace n}
    (hΦ : ContDiff ℝ ∞ Φ) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ (legendreMap Φ) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : ChartedSpace (Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
  have h : ContMDiff (lgModel n) ((torusModel n).prod 𝓘(ℝ, RealSpace n)) ∞
      (fun y : LGSpace n => (y.2, Φ y.1)) :=
    contMDiff_snd.prodMk (hΦ.contMDiff.comp contMDiff_fst)
  exact (contMDiff_linearRechart_id (M := Cotangent n) (cotangentEuclideanEquiv n)).comp
    (h.comp (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n)))

theorem contMDiff_legendreMap_inv {Ψ : RealSpace n → RealSpace n}
    (hΨ : ContDiff ℝ ∞ Ψ) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞
      (inverseLegendreMap Ψ) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : ChartedSpace (Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
  have h : ContMDiff ((torusModel n).prod 𝓘(ℝ, RealSpace n)) (lgModel n) ∞
      (fun y : Cotangent n => (Ψ y.2, y.1)) :=
    (hΨ.contMDiff.comp contMDiff_snd).prodMk contMDiff_fst
  exact (contMDiff_linearRechart_id (M := LGSpace n) (lgEuclideanEquiv n)).comp
    (h.comp (contMDiff_linearRechart_id_symm (M := Cotangent n) (cotangentEuclideanEquiv n)))

/-- The literal quotient diffeomorphism obtained from a smooth Legendre
homeomorphism and its smooth inverse on the based real spaces. -/
def legendreDiffeomorph (Φ : RealSpace n ≃ₜ RealSpace n)
    (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm) :
    (lgManifold n).SmoothEquiv (cotangentManifold n) where
  toEquiv :=
    { toFun := legendreMap Φ
      invFun := fun y => (Φ.symm y.2, y.1)
      left_inv := fun y => by simp [legendreMap]
      right_inv := fun y => by simp [legendreMap] }
  contMDiff_toFun := contMDiff_legendreMap hΦ
  contMDiff_invFun := contMDiff_legendreMap_inv hΨ

@[simp] theorem legendreDiffeomorph_apply (Φ : RealSpace n ≃ₜ RealSpace n)
    (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm) (y : (lgManifold n).Point) :
    legendreDiffeomorph Φ hΦ hΨ y = (y.2, Φ y.1) := rfl

theorem cotangentAngleCovector_legendreMap {Φ : RealSpace n → RealSpace n}
    (hΦ : ContDiff ℝ ∞ Φ) (j : Fin n) (y : (lgManifold n).Point)
    (v : (lgManifold n).Tangent y) :
    cotangentAngleCovector j (legendreMap Φ y)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (legendreMap Φ) y v) =
        lgAngleCovector j y v := by
  have hd := mfderiv_comp_apply y
    ((contMDiff_cotangent_circleCoordinate j).mdifferentiable (by simp) (legendreMap Φ y))
    ((contMDiff_legendreMap hΦ).mdifferentiable (by simp) y) v
  change complexDifferential (lgManifold n) (lgCircleCoordinate j) y v =
    complexDifferential (cotangentManifold n) (cotangentCircleCoordinate j)
      (legendreMap Φ y)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (legendreMap Φ) y v) at hd
  simp only [cotangentAngleCovector, lgAngleCovector, phaseCovector_apply, ← hd]
  rfl

/-- Exact pullback of the canonical primitive, with the derivative of the
actual quotient Legendre map and no angular lift choice. -/
theorem pullback_lambdaCanForm_legendreMap {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    (lgManifold n).pullback (cotangentManifold n) (legendreMap (coordinateGradient φ))
      (lambdaCanForm n) = lambdaPotentialForm φ := by
  funext y
  ext vs
  simp [pullback, lambdaCanForm, lambdaPotentialForm, covectorForm, legendreMap]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a => coordinateGradient φ y.1 j * a)
    (cotangentAngleCovector_legendreMap (contDiff_coordinateGradient hφ) j y (vs 0))

theorem lambdaPotentialForm_lgCover (φ : RealSpace n → ℝ)
    (x q : TangentCoordinates n) :
    evalOne (lambdaPotentialForm φ) (lgCover x) (lgCoverTangent x q) =
      ∑ j, coordinateGradient φ x.1 j * q.2 j := by
  simp [lambdaPotentialForm, lgCover]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a => coordinateGradient φ x.1 j * a) (lgAngleCovector_lgCover j x q)

/-- Smoothness of the literal coefficient form follows from the smooth
potential; no pullback or form regularity certificate is assumed. -/
theorem isSmoothForm_lambdaPotentialForm {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : (lgManifold n).IsSmoothForm (lambdaPotentialForm φ) := by
  classical
  have hlog : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, RealSpace n) ∞
      (fun y : (lgManifold n).Point => y.1) := by
    let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    exact (contMDiff_fst : ContMDiff (lgModel n) 𝓘(ℝ, RealSpace n) ∞
      (Prod.fst : LGSpace n → _)).comp
      (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))
  have hgrad := (contDiff_coordinateGradient hφ).contMDiff.comp hlog
  have he : lambdaPotentialForm φ = ∑ j : Fin n,
      (fun y => coordinateGradient φ y.1 j • covectorForm (lgManifold n) (lgAngleCovector j) y) := by
    funext y
    ext v
    simp [lambdaPotentialForm, covectorForm]
  rw [he]
  exact IsSmoothForm.sum Finset.univ _ (fun j _ =>
    (isSmoothForm_lgAngleCovector j).function_smul
      ((contDiff_apply ℝ ℝ j).contMDiff.comp hgrad))

/-- Exact primitive identification yields nondegeneracy on every native
tangent space, because the proved Legendre diffeomorphism has invertible
actual derivative. -/
theorem isSymplecticOn_exteriorDerivative_lambdaPotentialForm
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ : ∀ x, Φ x = coordinateGradient φ x)
    (hΨ : ContDiff ℝ ∞ Φ.symm) :
    (lgManifold n).IsSymplecticOn
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) Set.univ := by
  have hs : ContDiff ℝ ∞ Φ := by
    have he : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦ
    rw [he]
    exact contDiff_coordinateGradient hφ
  let L := legendreDiffeomorph Φ hs hΨ
  have hp : (lgManifold n).pullback (cotangentManifold n) L (lambdaCanForm n) =
      lambdaPotentialForm φ := by
    have he : (L : (lgManifold n).Point → (cotangentManifold n).Point) =
        legendreMap (coordinateGradient φ) := by
      ext y
      simp [L, hΦ, legendreMap]
    rw [he]
    exact pullback_lambdaCanForm_legendreMap hφ
  have hd : (lgManifold n).exteriorDerivative (lambdaPotentialForm φ) =
      (lgManifold n).pullback (cotangentManifold n) L
        ((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) := by
    rw [← hp]
    exact (lgManifold n).exteriorDerivative_pullback (cotangentManifold n)
      L.toContMDiffMap (lambdaCanForm n) (isSmoothForm_lambdaCanForm n)
  apply ((lgManifold n).isSymplecticOn_exteriorDerivative_iff _
    (isSmoothForm_lambdaPotentialForm hφ) Set.univ).mpr
  intro y _ v hv
  apply (L.mfderivToContinuousLinearEquiv (by simp) y).injective
  rw [map_zero]
  apply nondegenerate_exteriorDerivative_lambdaCanForm (L y)
  intro w
  obtain ⟨u, rfl⟩ := (L.mfderivToContinuousLinearEquiv (by simp) y).surjective w
  have he := hv u
  rw [hd] at he
  convert he using 1
  apply congrArg (((cotangentManifold n).exteriorDerivative (lambdaCanForm n)) (L y))
  ext i
  fin_cases i <;> rfl

/-- The compatible potential construction supplies an actual strict
cotangent identification, in the fixed quotient spaces and with the literal
adapted primitive. This is the map used in `prop:endpoint`; constructing the
comparison chain and its full core is a subsequent obligation. -/
theorem _root_.FsFltz.ToricInput.exists_adapted_cotangent_identification (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ ∞ φ ∧
      (∃ R > 0, ∀ x, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ → φ x = φEnd x) ∧
      (lgManifold n).IsSymplecticOn
        ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) Set.univ ∧
      ∃ L : (lgManifold n).SmoothEquiv (cotangentManifold n),
        (∀ y, L y = (y.2, coordinateGradient φ y.1)) ∧
        (lgManifold n).pullback (cotangentManifold n) L (lambdaCanForm n) =
          lambdaPotentialForm φ := by
  obtain ⟨φEnd, φ, hstrong, _, _, hφs, _, _, hend,
    _, Φ, _, _, _, _, hΦ, hΦs, hΦinv⟩ := I.exists_compatiblePotential_with_legendre
  let L := legendreDiffeomorph Φ hΦs hΦinv
  refine ⟨φEnd, φ, hstrong, hφs, hend,
    isSymplecticOn_exteriorDerivative_lambdaPotentialForm hφs Φ hΦ hΦinv, L, ?_, ?_⟩
  · intro y
    simp [L, hΦ]
  · have he : (L : (lgManifold n).Point → (cotangentManifold n).Point) =
        legendreMap (coordinateGradient φ) := by
      ext y
      simp [L, hΦ, legendreMap]
    rw [he]
    exact pullback_lambdaCanForm_legendreMap hφs

end FsFltz.Geometry
