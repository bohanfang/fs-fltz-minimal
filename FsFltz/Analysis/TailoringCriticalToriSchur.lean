import FsFltz.Analysis.TailoringCriticalToriReduced

/-!
# Positivity of the actual reduced Hessian

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1512–1517.
Differentiate the actual affine and normal equations. The resulting
Schur form is positive because its lift is nonzero and the original
homogeneous potential has positive Hessian away from the origin.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

/-- The differentiated level and normal equations give the exact reduced
Hessian form on every parameter direction. -/
theorem face_reduced_hessian_identity {φ : RealSpace n → ℝ}
    (hd : Differentiable ℝ φ) {s : Finset (Lattice n)}
    {x : (s → ℝ) → RealSpace n} {a : (s → ℝ) → (s → ℝ)} {y : s → ℝ}
    (hx : DifferentiableAt ℝ x y) (ha : DifferentiableAt ℝ a y)
    (hφ : ContDiffAt ℝ ∞ φ (x y))
    (hlevel : (fun z => faceLevelMap s (x z)) =ᶠ[𝓝 y] (fun z v => 1 + z v))
    (hnormal : (fun z => coordinateGradient φ (x z)) =ᶠ[𝓝 y]
      (fun z => faceNormalMap s (a z))) :
    (faceLevelMap s).comp (fderiv ℝ x y) = ContinuousLinearMap.id ℝ (s → ℝ) ∧
    ∀ h : s → ℝ,
      (∑ v, fderiv ℝ a y h v * h v) =
        ∑ j, fderiv ℝ (coordinateGradient φ) (x y) (fderiv ℝ x y h) j *
          (fderiv ℝ x y h) j := by
  classical
  have hleft := (faceLevelMap s).hasFDerivAt.comp y hx.hasFDerivAt
  have hright : HasFDerivAt (fun z : s → ℝ => fun v => 1 + z v)
      (ContinuousLinearMap.id ℝ (s → ℝ)) y := by
    convert (hasFDerivAt_id y).const_add (fun _ : s => (1 : ℝ)) using 1
    ext z v
    rfl
  have hA : (faceLevelMap s).comp (fderiv ℝ x y) = ContinuousLinearMap.id ℝ (s → ℝ) :=
    hleft.unique (hright.congr_of_eventuallyEq hlevel)
  have hg := (contDiffAt_coordinateGradient hd hφ).differentiableAt (by simp)
  have hB := (hg.hasFDerivAt.comp y hx.hasFDerivAt).unique
    (((faceNormalMap s).hasFDerivAt.comp y ha.hasFDerivAt).congr_of_eventuallyEq hnormal)
  refine ⟨hA, fun h => ?_⟩
  have hAh := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L h) hA
  have hBh := congrArg (fun L : (s → ℝ) →L[ℝ] RealSpace n => L h) hB
  change faceLevelMap s (fderiv ℝ x y h) = h at hAh
  change fderiv ℝ (coordinateGradient φ) (x y) (fderiv ℝ x y h) =
    faceNormalMap s (fderiv ℝ a y h) at hBh
  rw [hBh, faceNormalMap_pairing, hAh]

/-- The Schur-Hessian inequality is produced on a neighborhood from the
actual equations and punctured-end positivity. -/
theorem IsStronglyCompatibleEndPotential.eventually_face_reduced_hessian_pos
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hd : Differentiable ℝ φ)
    {s : Finset (Lattice n)} {x : (s → ℝ) → RealSpace n}
    {a : (s → ℝ) → (s → ℝ)} (hx : ContDiffAt ℝ ∞ x 0)
    (ha : ContDiffAt ℝ ∞ a 0) (hxne : x 0 ≠ 0)
    (hlevel : (fun y => faceLevelMap s (x y)) =ᶠ[𝓝 0] (fun y v => 1 + y v))
    (hnormal : (fun y => coordinateGradient φ (x y)) =ᶠ[𝓝 0]
      (fun y => faceNormalMap s (a y))) :
    ∀ᶠ y : s → ℝ in 𝓝 0, ∀ h : s → ℝ, h ≠ 0 →
      0 < ∑ v, fderiv ℝ a y h v * h v := by
  have hxd : ∀ᶠ y in 𝓝 (0 : s → ℝ), DifferentiableAt ℝ x y :=
    ((hx.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun y hy => hy.differentiableAt_one
  have had : ∀ᶠ y in 𝓝 (0 : s → ℝ), DifferentiableAt ℝ a y :=
    ((ha.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      fun y hy => hy.differentiableAt_one
  have hnonzero : ∀ᶠ y in 𝓝 (0 : s → ℝ), x y ≠ 0 :=
    hx.continuousAt.eventually (eventually_ne_nhds hxne)
  filter_upwards [hxd, had, hnonzero, hlevel.eventuallyEq_nhds,
    hnormal.eventuallyEq_nhds] with y hxy hay hny hly hnormaly h hh
  obtain ⟨hA, hform⟩ := face_reduced_hessian_identity hd hxy hay (hφ.smooth _ hny)
    hly hnormaly
  rw [hform]
  apply hφ.native_hessian_pos hd hny
  intro hzero
  have he := congrArg (fun L : (s → ℝ) →L[ℝ] (s → ℝ) => L h) hA
  change faceLevelMap s (fderiv ℝ x y h) = h at he
  rw [hzero, map_zero] at he
  exact hh he.symm

/-- Construct the actual reduced coefficient and its positive Hessian
from the strong potential and finite toric face, retaining the same
constrained minimizer throughout. -/
theorem IsStronglyCompatibleEndPotential.exists_actual_faceReducedCoefficient_pos_hessian
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ) (hφ1 : ContDiff ℝ 1 φ)
    {c : ℝ} (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun u : EuclideanSpace ℝ (Fin n) =>
      φ ((EuclideanSpace.equiv (Fin n) ℝ) u) - c * ‖u‖ ^ 2))
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ x : (s → ℝ) → RealSpace n,
      x 0 ∈ polarFace I s ∧ IsMinOn φ (polarFace I s) (x 0) ∧
      ContDiffAt ℝ ∞ x 0 ∧ ContDiffAt ℝ ∞ (faceReducedPotential φ x) 0 ∧
      ContDiffAt ℝ ∞ (faceReducedCoefficient φ x) 0 ∧
      (∀ v, 0 < faceReducedCoefficient φ x 0 v) ∧
      (∀ᶠ y in 𝓝 0,
        x y ∈ faceCoordinateSlice s y ∧
        coordinateGradient φ (x y) = faceNormalMap s (faceReducedCoefficient φ x y) ∧
        IsMinOn φ (faceCoordinateSlice s y) (x y) ∧
        (∀ z ∈ faceCoordinateSlice s y,
          IsMinOn φ (faceCoordinateSlice s y) z → z = x y) ∧
        ∀ h : s → ℝ, h ≠ 0 →
          0 < ∑ v, fderiv ℝ (faceReducedCoefficient φ x) y h v * h v) := by
  obtain ⟨x, hx₀, hm₀, hxs, hψs, has, ha₀, hsol⟩ :=
    hφ.exists_actual_faceReducedCoefficient hφ1 hc hconv hs hsne hsproper
  obtain ⟨v, hv⟩ := hsne
  have hxne : x 0 ≠ 0 := ne_zero_of_mem_polarFacet I v ⟨hx₀.1, hx₀.2 v hv⟩
  have hpos := hφ.eventually_face_reduced_hessian_pos (hφ1.differentiable (by simp))
    hxs has hxne
    (hsol.mono fun y hy => (mem_faceCoordinateSlice_iff s y (x y)).mp hy.1)
    (hsol.mono fun y hy => hy.2.1)
  refine ⟨x, hx₀, hm₀, hxs, hψs, has, ha₀, ?_⟩
  filter_upwards [hsol, hpos] with y hy hp
  exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, hp⟩

end FsFltz
