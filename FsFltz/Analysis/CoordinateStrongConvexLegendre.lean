import FsFltz.Analysis.CoordinateLegendre
import FsFltz.Analysis.StrongConvexLegendre

/-!
# The homogeneous Legendre inverse in native coordinates

Canonical change-of-norm transport of the actual `C¹` gradient homeomorphism
and its punctured smooth inverse. The immediate consumer is the homogeneous
compatible potential in `lem:potential` of `geometric-part-fsf-proof.tex`,
lines 636–642.
-/

noncomputable section

open Function Set
open scoped ContDiff

namespace FsFltz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The native coordinate gradient homeomorphism for a globally `C¹`,
uniformly convex potential with quadratic growth. -/
def strongConvexCoordinateGradientHomeomorph {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x)) :
    (ι → ℝ) ≃ₜ (ι → ℝ) :=
  (EuclideanSpace.equiv ι ℝ).symm.toHomeomorph.trans
    ((strongConvexGradientHomeomorph (hφ.comp (EuclideanSpace.equiv ι ℝ).contDiff)
      hc hconv hlower).trans (EuclideanSpace.equiv ι ℝ).toHomeomorph)

@[simp]
theorem strongConvexCoordinateGradientHomeomorph_apply {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (u : ι → ℝ) :
    strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower u = coordinateGradient φ u :=
  (coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by norm_num)) u).symm

@[simp]
theorem strongConvexCoordinateGradientHomeomorph_coe {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x)) :
    (strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower : (ι → ℝ) → (ι → ℝ)) =
      coordinateGradient φ := funext (strongConvexCoordinateGradientHomeomorph_apply
        hφ hc hconv hlower)

/-- The canonical coordinate gradient of a smooth potential is locally smooth. -/
theorem contDiffAt_coordinateGradient {φ : (ι → ℝ) → ℝ} {u : ι → ℝ}
    (hd : Differentiable ℝ φ) (hs : ContDiffAt ℝ ∞ φ u) :
    ContDiffAt ℝ ∞ (coordinateGradient φ) u := by
  let e := EuclideanSpace.equiv ι ℝ
  have he : coordinateGradient φ = fun v => e (gradient (φ ∘ e) (e.symm v)) :=
    funext (coordinateGradient_eq_euclidean_gradient hd)
  rw [he]
  have hφe : ContDiffAt ℝ ∞ (φ ∘ e) (e.symm u) := by
    apply ContDiffAt.comp (e.symm u) _ e.contDiff.contDiffAt
    simpa only [e.apply_symm_apply] using hs
  exact e.contDiff.contDiffAt.comp u
    ((contDiffAt_gradient hφe).comp u e.symm.contDiff.contDiffAt)

/-- The homogeneous Legendre homeomorphism on the actual punctured native
coordinate spaces. -/
def puncturedCoordinateGradientHomeomorph {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (hφ0 : coordinateGradient φ 0 = 0) :
    {u : ι → ℝ // u ≠ 0} ≃ₜ {p : ι → ℝ // p ≠ 0} := by
  let H := strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower
  apply H.subtype
  intro u
  constructor
  · intro hu hz
    apply hu
    apply H.injective
    simpa [H, hφ0] using hz
  · intro hu hz
    exact hu (by simpa [H, hz] using hφ0)

@[simp]
theorem puncturedCoordinateGradientHomeomorph_apply {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (hφ0 : coordinateGradient φ 0 = 0) (u : {u : ι → ℝ // u ≠ 0}) :
    (puncturedCoordinateGradientHomeomorph hφ hc hconv hlower hφ0 u).val =
      coordinateGradient φ u.val :=
  strongConvexCoordinateGradientHomeomorph_apply hφ hc hconv hlower u.val

/-- Smoothness of the inverse homogeneous Legendre map in native coordinates. -/
theorem contDiffAt_symm_strongConvexCoordinateGradientHomeomorph
    {φ : (ι → ℝ) → ℝ} {c d : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (hφ0 : coordinateGradient φ 0 = 0)
    (hs : ∀ u ≠ 0, ContDiffAt ℝ ∞ φ u) (hd : 0 < d)
    (hb : ∀ x : EuclideanSpace ℝ ι, x ≠ 0 → ∀ v, d * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v)
    {p : ι → ℝ} (hp : p ≠ 0) :
    ContDiffAt ℝ ∞ (strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower).symm p := by
  let e := EuclideanSpace.equiv ι ℝ
  have h0 : gradient (φ ∘ e) 0 = 0 := by
    apply e.injective
    have he := coordinateGradient_eq_euclidean_gradient (hφ.differentiable (by norm_num)) 0
    simpa only [map_zero, hφ0] using he.symm
  have hs' : ∀ x : EuclideanSpace ℝ ι, x ≠ 0 → ContDiffAt ℝ ∞ (φ ∘ e) x := by
    intro x hx
    apply ContDiffAt.comp x _ e.contDiff.contDiffAt
    apply hs
    intro hz
    apply hx
    apply e.injective
    simpa using hz
  have hp' : e.symm p ≠ 0 := by
    intro hz
    apply hp
    have := congrArg e hz
    simpa using this
  have hInv := contDiffAt_symm_strongConvexGradientHomeomorph (hφ.comp e.contDiff) hc
    hconv hlower h0 hs' hd hb hp'
  exact e.contDiff.contDiffAt.comp p (hInv.comp p e.symm.contDiff.contDiffAt)

/-- Ambient coordinate smoothness of the homogeneous Legendre map away from zero. -/
theorem contDiffOn_strongConvexCoordinateGradientHomeomorph
    {φ : (ι → ℝ) → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (hs : ∀ u ≠ 0, ContDiffAt ℝ ∞ φ u) :
    ContDiffOn ℝ ∞ (strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower)
      ({0}ᶜ : Set (ι → ℝ)) := by
  intro u hu
  simpa using (contDiffAt_coordinateGradient (hφ.differentiable (by norm_num))
    (hs u (by simpa using hu))).contDiffWithinAt

/-- Ambient coordinate smoothness of the homogeneous inverse away from zero. -/
theorem contDiffOn_symm_strongConvexCoordinateGradientHomeomorph
    {φ : (ι → ℝ) → ℝ} {c d : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : 0 < c)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ ι =>
      φ ((EuclideanSpace.equiv ι ℝ) x) - c * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ ι, c * ‖x‖ ^ 2 ≤ φ ((EuclideanSpace.equiv ι ℝ) x))
    (hφ0 : coordinateGradient φ 0 = 0)
    (hs : ∀ u ≠ 0, ContDiffAt ℝ ∞ φ u) (hd : 0 < d)
    (hb : ∀ x : EuclideanSpace ℝ ι, x ≠ 0 → ∀ v, d * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv ι ℝ)) x) v) v) :
    ContDiffOn ℝ ∞ (strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower).symm
      ({0}ᶜ : Set (ι → ℝ)) := by
  intro p hp
  exact (contDiffAt_symm_strongConvexCoordinateGradientHomeomorph hφ hc hconv hlower hφ0
    hs hd hb (by simpa using hp)).contDiffWithinAt

end FsFltz
