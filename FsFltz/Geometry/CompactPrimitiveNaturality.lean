import FsFltz.Geometry.CompletionGluing
import FsFltz.Geometry.IntrinsicExteriorNaturality
import FsFltz.Geometry.BoundaryPresentationBridge
import FsFltz.Geometry.BoundaryNondegeneracy
import FsFltz.Geometry.FormScalarDerivative

/-!
# Constant-scale Liouville maps on the compact carrier

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 171–189; and `sec:lean`, lines 783–814.
Equality of smooth primitives on the compact carrier determines their actual
exterior derivatives there, including full ambient tangents at the boundary.
The native half-space inclusion and its bijective differential supply that
boundary argument. Constant scaling then forces the prescribed
compact presentation to transport the Liouville fields.

This is a foundation about a supplied extension-space presentation. It does
not represent all native compact diffeomorphisms or assert the geometric target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

/-- Equality on the carrier suffices to identify the full exterior derivative
at its boundary; equality off the carrier is unnecessary. -/
theorem exteriorDerivative_eqOn_of_eqOn {d : ℕ} (D : CompactDomain d)
    (α β : D.extension.Form 1) (hα : D.extension.IsSmoothForm α)
    (hβ : D.extension.IsSmoothForm β) (heq : ∀ x ∈ D.carrier, α x = β x) :
    ∀ x ∈ D.carrier,
      D.extension.exteriorDerivative α x = D.extension.exteriorDerivative β x := by
  cases d with
  | zero =>
      intro x _
      ext vs
      have hv : vs 0 = 0 := PiLp.ext (fun j => Fin.elim0 j)
      rw [ContinuousAlternatingMap.map_coord_zero _ 0 hv,
        ContinuousAlternatingMap.map_coord_zero _ 0 hv]
  | succ k =>
      intro x hx
      let z : D.Point := ⟨x, hx⟩
      let i : D.Point → D.extension.Point := Subtype.val
      have hp : (fun y : D.Point => (α (i y)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i y)) =
          (fun y : D.Point => (β (i y)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i y)) := by
        funext y
        rw [heq y.val y.property]
      have hd := congrArg IntrinsicLiouville.exteriorDerivative hp
      rw [IntrinsicLiouville.exteriorDerivative_pullback_from_boundaryless
          D.extension i D.contMDiff_subtype_val α hα,
        IntrinsicLiouville.exteriorDerivative_pullback_from_boundaryless
          D.extension i D.contMDiff_subtype_val β hβ] at hd
      have hs := LinearMap.injective_iff_surjective.mp
        (D.injective_mfderiv_subtype_val z)
      ext vs
      choose ws hws using fun j => hs (vs j)
      have hws' : ∀ j, mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          Subtype.val z (ws j) = vs j := hws
      have he := congrArg (fun η => η z ws) hd
      change (D.extension.exteriorDerivative α x) (fun j =>
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) Subtype.val z (ws j)) =
        (D.extension.exteriorDerivative β x) (fun j =>
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) Subtype.val z (ws j)) at he
      simpa only [hws'] using he

end CompactDomain

namespace DomainPresentationEquiv

variable {d : ℕ} {D E : LiouvilleDomain d}

/-- Exterior derivative transport for the prescribed compact map follows
from constant-scale primitive equality only on the compact carrier. -/
theorem exteriorDerivative_scaled_on_carrier
    (h : DomainPresentationEquiv D.domain E.domain) (c : ℝ)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x)
    (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier)
    (v w : D.domain.extension.Tangent x) :
    evalTwo (D.domain.extension.pullback E.domain.extension h.extensionEquiv
      (E.domain.extension.exteriorDerivative E.liouville.primitive)) x v w =
      c * evalTwo (D.domain.extension.exteriorDerivative D.liouville.primitive) x v w := by
  have hd := D.domain.exteriorDerivative_eqOn_of_eqOn
    (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive)
    (c • D.liouville.primitive)
    (D.domain.extension.isSmoothForm_pullback_one E.domain.extension
      h.extensionEquiv.toContMDiffMap E.liouville.primitive E.liouville.smooth_primitive)
    (D.liouville.smooth_primitive.smul c) hp x hx
  have hn : D.domain.extension.exteriorDerivative
      (D.domain.extension.pullback E.domain.extension h.extensionEquiv E.liouville.primitive) =
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        (E.domain.extension.exteriorDerivative E.liouville.primitive) :=
    D.domain.extension.exteriorDerivative_pullback E.domain.extension
      h.extensionEquiv.toContMDiffMap E.liouville.primitive E.liouville.smooth_primitive
  have hpoint := (congrFun hn x).symm.trans hd
  change (D.domain.extension.pullback E.domain.extension h.extensionEquiv
    (E.domain.extension.exteriorDerivative E.liouville.primitive) x) ![v, w] = _
  rw [hpoint]
  have he := D.domain.extension.evalTwo_exteriorDerivative_smul
    (fun _ => c) D.liouville.primitive contMDiff_const
    D.liouville.smooth_primitive x v w
  change evalTwo (D.domain.extension.exteriorDerivative
    (fun y => c • D.liouville.primitive y)) x v w = _
  simpa only [scalarDerivative, mfderiv_const, zero_apply,
    zero_mul, add_zero, sub_zero] using he

/-- A constant-scale compact Liouville presentation carries the
actual Liouville field on the whole carrier, including its boundary. -/
theorem map_field_of_scaled_primitive
    (h : DomainPresentationEquiv D.domain E.domain) (c : ℝ)
    (hp : ∀ x ∈ D.domain.carrier,
      D.domain.extension.pullback E.domain.extension h.extensionEquiv
        E.liouville.primitive x = c • D.liouville.primitive x)
    (x : D.domain.extension.Point) (hx : x ∈ D.domain.carrier) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv x
      (D.liouville.field x) = E.liouville.field (h.extensionEquiv x) := by
  have hy := (h.mem_carrier_iff x).mpr hx
  apply E.domain.extension.liouvilleEquation_unique E.liouville.primitive
    (h.extensionEquiv x) (E.liouville.symplectic.2.2 _ hy) _
    (E.liouville.contraction _ hy)
  intro w
  obtain ⟨v, rfl⟩ := (h.extensionEquiv.mfderivToContinuousLinearEquiv (by simp) x).surjective w
  have hd := h.exteriorDerivative_scaled_on_carrier c hp x hx (D.liouville.field x) v
  have he := congrArg (fun A => A (fun _ => v)) (hp x hx)
  change evalOne E.liouville.primitive (h.extensionEquiv x)
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv x v) =
      c * evalOne D.liouville.primitive x v at he
  have hvec : (fun j : Fin 2 =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv x
        (![D.liouville.field x, v] j)) =
      ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.extensionEquiv x
        (D.liouville.field x), mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
        h.extensionEquiv x v] := by
    funext j
    fin_cases j <;> rfl
  simp only [evalTwo, pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, hvec] at hd
  exact hd.trans ((congrArg (fun a => c * a) (D.liouville.contraction x hx v)).trans he.symm)

end DomainPresentationEquiv
end FsFltz.Geometry
