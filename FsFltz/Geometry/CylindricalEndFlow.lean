import FsFltz.Geometry.CylindricalEnd
import FsFltz.Geometry.CylindricalLiouville

/-!
# Radial integral curves of the constructed stretched end

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 156–158, and
`sec:lean`, lines 805–814. The derivative of the actual end curve is
computed from the boundary flow collar and the proved scalar inverse.
It supplies the radial ODE needed for compact-interior continuation.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule for the actual end curve, with its explicit reciprocal stretch speed. -/
theorem endMap_hasMFDerivAt (x : D.neighborhoodDomain.boundary.Point) (r : ℝ)
    (hr : -C.width < r) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun t => C.endMap (x, t)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((deriv (CollarStretch.stretch C.width) (CollarStretch.inverse C.positive_width r))⁻¹ •
          C.localizedDomain.liouville.field (C.endMap (x, r)))) := by
  let γ : ℝ → C.localizedDomain.domain.extension.Point := fun t => C.endMap (x, t)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ r :=
    ((C.smooth_endMap_on.contMDiffAt (C.endStrip.isOpen.mem_nhds
      (show (x, r) ∈ C.endStrip from ⟨mem_univ _, hr⟩))).comp r
      ((contMDiff_const.prodMk contMDiff_id) r)).mdifferentiableAt (by simp)
  have hi := hasMFDerivAt_iff_hasFDerivAt.mpr
    (CollarStretch.inverse_hasDerivAt C.positive_width r).hasFDerivAt
  have hode := (C.solves x (CollarStretch.inverse C.positive_width r)
    (CollarStretch.inverse_mem_collar C.positive_width hr)).comp r hi
  have heq : (Subtype.val : C.neighborhood → D.neighborhoodDomain.extension.Point) ∘ γ
      =ᶠ[𝓝 r] (fun t => C.flow (CollarStretch.inverse C.positive_width t)
        (D.neighborhoodDomain.boundaryInclusion.map x)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
    exact C.endMap_val (x, t) ht
  have hactual := hode.congr_of_eventuallyEq_abuse heq
  have hcomp := mfderiv_comp (f := γ)
    (g := (Subtype.val : C.neighborhood → D.neighborhoodDomain.extension.Point)) r
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)) hγ
  erw [D.neighborhoodDomain.extension.mfderiv_restrict_val C.neighborhood (γ r)] at hcomp
  simp only [ContinuousLinearMap.id_comp] at hcomp
  apply hγ.hasMFDerivAt.congr_mfderiv
  rw [← hcomp, hactual.mfderiv]
  apply ContinuousLinearMap.ext
  intro s
  change ℝ at s
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply]
  change (s * (deriv (CollarStretch.stretch C.width)
    (CollarStretch.inverse C.positive_width r))⁻¹) •
    D.neighborhoodStructure.field
      (C.flow (CollarStretch.inverse C.positive_width r)
        (D.neighborhoodDomain.boundaryInclusion.map x)) =
    s • ((deriv (CollarStretch.stretch C.width)
      (CollarStretch.inverse C.positive_width r))⁻¹ •
        D.neighborhoodStructure.field (C.endMap (x, r)).val)
  rw [C.endMap_val (x, r) hr]
  simp only [map, smul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical stretched field has the computed reciprocal speed at every actual end point. -/
theorem stretchedField_endMap (x : D.neighborhoodDomain.boundary.Point) (r : ℝ)
    (hr : -C.width < r) :
    C.stretchedField (C.endMap (x, r)) =
      (deriv (CollarStretch.stretch C.width) (CollarStretch.inverse C.positive_width r))⁻¹ •
        C.localizedDomain.liouville.field (C.endMap (x, r)) := by
  let p : C.strip := ⟨(x, CollarStretch.inverse C.positive_width r), mem_univ _,
    CollarStretch.inverse_mem_collar C.positive_width hr⟩
  have he : C.collarPoint p = C.endMap (x, r) := by
    apply Subtype.ext
    exact (C.endMap_val (x, r) hr).symm
  have hf := C.stretchedField_collarPoint p
  rw [he] at hf
  exact hf

/-- The actual end curves solve the actual stretched Liouville field's ODE
throughout the open radial source, including the seam at zero. -/
theorem endMap_isMIntegralCurveOn (x : D.neighborhoodDomain.boundary.Point) :
    IsMIntegralCurveOn (fun r => C.endMap (x, r)) C.stretchedField (Ioi (-C.width)) := by
  intro r hr
  rw [C.stretchedField_endMap x r hr]
  exact (C.endMap_hasMFDerivAt x r hr).hasMFDerivWithinAt

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
