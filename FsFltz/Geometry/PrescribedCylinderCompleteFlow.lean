import FsFltz.Geometry.PrescribedCylinderRadial
import FsFltz.Geometry.CylindricalCompleteFlow

/-!
# Complete flow on a prescribed raw ambient from its cylinder primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 805–821. The actual outward radial curves are derived
from `exp(r) α` and then supply uniform continuation outside a compact set.
The constructed flow lives on precisely the input manifold and primitive.

The indexed signed cylinder parametrizations, their full primitive
pullback identities, and their compact-complement coverage are explicit
conditional gluing hypotheses. This module does not construct that
half-infinite attachment from the finite intrinsic collar, nor assert a
native completion realization or inclusion marking.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry.PrescribedCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The prescribed primitive on indexed signed half-infinite cylinder charts
produces an all-real smooth flow of the canonical Liouville field on the
same raw ambient `X`. Compact coverage is an explicit gluing hypothesis;
the radial integral curves and field smoothness are derived here. -/
theorem exists_completeLiouvilleFlow_of_prescribedCylinder {d : ℕ}
    (X : SmoothManifold d) (lambda : X.Form 1) (hlambda : X.IsSmoothForm lambda)
    (hnd : ∀ x, X.Nondegenerate (X.exteriorDerivative lambda) x)
    {ι : Type*} (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (V : ι → Set E) (hV : ∀ i, IsOpen (V i))
    (F : ι → ℝ × E → X.Point)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) ∞
      (F i) (Ioi (-δ i) ×ˢ V i))
    (α : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ) (hα : ∀ i, ContDiffOn ℝ ∞ (α i) (V i))
    (hprimitive : ∀ i p, p ∈ Ioi (-δ i) ×ˢ V i →
      (lambda (F i p)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) (F i) p) = cylinderPrimitive (α i) p)
    (hsurj : ∀ i p, p ∈ Ioi (-δ i) ×ˢ V i →
      Function.Surjective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, Model d) (F i) p))
    {K : Set X.Point} (hK : IsCompact K)
    (hcover : ∀ x ∉ K, ∃ i y r, y ∈ V i ∧ 1 ≤ r ∧ F i (r, y) = x) :
    Nonempty (CompleteLiouvilleFlow X (X.liouvilleVector lambda)) := by
  let B := Σ i, V i
  let e : B → ℝ → X.Point := fun b r => F b.1 (r, b.2.val)
  have hradial : ∀ b, IsMIntegralCurveOn (e b) (X.liouvilleVector lambda) (Ioi 0) := by
    intro b
    have h := isMIntegralCurveOn_radial X lambda hlambda (F b.1) (hV b.1)
      (hF b.1) (α b.1) (hα b.1) (hprimitive b.1) (hsurj b.1)
      (fun p _ => hnd (F b.1 p)) b.2.property
    apply h.mono
    intro r hr
    change -δ b.1 < r
    change 0 < r at hr
    linarith [hδ b.1]
  apply X.exists_completeLiouvilleFlow_of_cylindricalEnd (X.liouvilleVector lambda)
    (X.isSmoothVectorField_liouvilleVector lambda hlambda hnd) hK e hradial
  intro x hx
  obtain ⟨i, y, r, hy, hr, heq⟩ := hcover x hx
  exact ⟨⟨i, ⟨y, hy⟩⟩, r, hr, heq⟩

end FsFltz.Geometry.PrescribedCylinder
