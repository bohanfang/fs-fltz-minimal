import FsFltz.Geometry.CompletionLocalization
import FsFltz.Geometry.CollarStretch
import FsFltz.Geometry.SmoothForms

/-!
# A smooth stretched primitive on the localized collar extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. Stretch the positive collar radius to infinity and multiply
the original primitive by the corresponding exponential factor. The factor
is one on the compact domain, so the two formulas glue smoothly on the
actual open cover consisting of its interior and the collar image.

This module constructs the primitive, rather than assuming an extension.
The symplectic differential and the complete Liouville flow are subsequent
foundations; no geometric comparison theorem is asserted.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

/-- The genuine radial weight on the original neighborhood. It differs
from one only in the positive collar. -/
def radialWeight (z : D.neighborhoodDomain.extension.Point) : ℝ :=
  if hz : z ∈ C.image then
    Real.exp (CollarStretch.stretch C.width (C.coordinates ⟨z, hz⟩).2 -
      (C.coordinates ⟨z, hz⟩).2)
  else 1

theorem radialWeight_image (z : C.image) :
    C.radialWeight z.val = Real.exp
      (CollarStretch.stretch C.width (C.coordinates z).2 - (C.coordinates z).2) := by
  simp only [radialWeight, dite_eq_left z.property]

theorem radialWeight_positive (z : D.neighborhoodDomain.extension.Point) :
    0 < C.radialWeight z := by
  unfold radialWeight
  split_ifs
  · exact Real.exp_pos _
  · exact zero_lt_one

/-- The original compact primitive is unchanged pointwise. -/
theorem radialWeight_carrier (z : D.neighborhoodDomain.extension.Point)
    (hz : z ∈ D.neighborhoodDomain.carrier) : C.radialWeight z = 1 := by
  unfold radialWeight
  split_ifs with hi
  · let y : C.image := ⟨z, hi⟩
    have hr : (C.coordinates y).2 ≤ 0 := by
      apply (C.side (C.coordinates y).1 (C.coordinates y).2
        (C.coordinates_mem_strip y).2).mp
      change C.map (C.coordinates y) ∈ D.neighborhoodDomain.carrier
      rw [C.map_coordinates y]
      exact hz
    have he := CollarStretch.stretch_eq_self C.positive_width
      (le_trans hr (div_nonneg C.positive_width.le (by norm_num : (0 : ℝ) ≤ 3)))
    change Real.exp (CollarStretch.stretch C.width (C.coordinates y).2 -
      (C.coordinates y).2) = 1
    simp only [he, sub_self, Real.exp_zero]
  · rfl

/-- Smoothness on the actual collar image comes from the constructed
inverse coordinates and the explicit smooth scalar stretch. -/
theorem smooth_radialWeight_image : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
    (fun z : C.image => C.radialWeight z.val) := by
  have hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
      (fun z : C.image => (C.coordinates z).2) :=
    contMDiff_snd.comp C.smooth_coordinates
  intro z
  have hs := (CollarStretch.stretch_contDiffAt (C.coordinates_mem_strip z).2.2).contMDiffAt
  have hsm := hs.comp z (hρ z)
  have hexp := Real.contDiff_exp.contDiffAt.contMDiffAt.comp z (hsm.sub (hρ z))
  apply hexp.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => C.radialWeight_image y)

/-- The weight is smooth on the entire localized extension. On its compact
interior it is locally the constant one; the collar supplies the other chart. -/
theorem smooth_radialWeight : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
    (fun z : C.neighborhood => C.radialWeight z.val) := by
  intro z
  have hsm : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ C.radialWeight z.val := by
    rcases z.property with hi | hi
    · apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds hi] with y hy
      exact C.radialWeight_carrier y (interior_subset hy)
    · exact (contMDiffAt_subtype_iff (U := C.image) (f := C.radialWeight)
        (x := ⟨z.val, hi⟩)).mp (C.smooth_radialWeight_image ⟨z.val, hi⟩)
  exact hsm.comp z (contMDiff_subtype_val z)

/-- The actual primitive on the open localized manifold, with the positive
collar stretched to infinite Liouville radius. -/
def stretchedPrimitive : C.localizedDomain.domain.extension.Form 1 :=
  fun z => C.radialWeight z.val • C.localizedDomain.liouville.primitive z

theorem smooth_stretchedPrimitive :
    C.localizedDomain.domain.extension.IsSmoothForm C.stretchedPrimitive :=
  C.localizedDomain.liouville.smooth_primitive.function_smul C.smooth_radialWeight

/-- The compact coefficients remain precisely the original coefficients. -/
theorem stretchedPrimitive_carrier (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    C.stretchedPrimitive z = C.localizedDomain.liouville.primitive z := by
  change C.radialWeight z.val • C.localizedDomain.liouville.primitive z = _
  rw [C.radialWeight_carrier z.val hz, one_smul]

/-- Each original finite collar point is a point of the actual localized
ambient manifold, not an abstract cylindrical presentation. -/
def collarPoint (p : C.strip) : C.localizedDomain.domain.extension.Point :=
  ⟨C.stripMap p, Or.inr ⟨p, rfl⟩⟩

theorem smooth_collarPoint : ContMDiff ((𝓘(ℝ, Model (d - 1))).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, Model d) ∞ C.collarPoint :=
  (ContMDiff.subtypeVal_comp_iff C.neighborhood C.collarPoint).mp C.smooth_stripMap

/-- The exponential factor on the actual collar, expressed in its original
finite radius. -/
theorem radialWeight_stripMap (p : C.strip) :
    C.radialWeight (C.stripMap p) =
      Real.exp (CollarStretch.stretch C.width p.val.2 - p.val.2) := by
  change C.radialWeight (C.imageMap p).val = _
  rw [C.radialWeight_image (C.imageMap p), C.coordinates_imageMap]

/-- The actual radius on the collar image, extended by zero elsewhere.
Only its restriction to that image is required to be smooth. -/
def radius (z : D.neighborhoodDomain.extension.Point) : ℝ :=
  if hz : z ∈ C.image then (C.coordinates ⟨z, hz⟩).2 else 0

theorem radius_image (z : C.image) : C.radius z.val = (C.coordinates z).2 := by
  simp only [radius, dite_eq_left z.property]

theorem radius_map (p : D.neighborhoodDomain.boundary.Point × ℝ) (hp : p ∈ C.strip) :
    C.radius (C.map p) = p.2 := by
  change C.radius (C.imageMap ⟨p, hp⟩).val = p.2
  rw [C.radius_image, C.coordinates_imageMap]

theorem smooth_radius_image : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
    (fun z : C.image => C.radius z.val) := by
  apply (contMDiff_snd.comp C.smooth_coordinates).congr
  exact fun y => C.radius_image y

theorem smoothAt_radius (z : D.neighborhoodDomain.extension.Point) (hz : z ∈ C.image) :
    ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ C.radius z :=
  (contMDiffAt_subtype_iff (U := C.image) (f := C.radius) (x := ⟨z, hz⟩)).mp
    (C.smooth_radius_image ⟨z, hz⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual Liouville field differentiates its actual flow-collar
radius to one. This follows from the collar ODE and inverse coordinates. -/
theorem scalarDerivative_radius_field (p : D.neighborhoodDomain.boundary.Point × ℝ)
    (hp : p ∈ C.strip) :
    D.neighborhoodDomain.extension.scalarDerivative C.radius (C.map p)
      (D.neighborhoodStructure.field (C.map p)) = 1 := by
  have hz : C.map p ∈ C.image := ⟨⟨p, hp⟩, rfl⟩
  have hρ := (C.smoothAt_radius (C.map p) hz).mdifferentiableAt (by simp)
  have hode := C.solves p.1 p.2 hp.2
  have hcomp := hρ.hasMFDerivAt.comp p.2 hode
  have heq : (fun t : ℝ => C.radius (C.flow t
      (D.neighborhoodDomain.boundaryInclusion.map p.1))) =ᶠ[𝓝 p.2] id := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with t ht
    exact C.radius_map (p.1, t) ⟨mem_univ _, ht⟩
  have hid := (hasFDerivAt_id (𝕜 := ℝ) p.2).congr_of_eventuallyEq heq
  have he := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1)
    ((hasMFDerivAt_iff_hasFDerivAt.mp hcomp).unique hid)
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) C.radius (C.map p)
    ((1 : ℝ) • D.neighborhoodStructure.field (C.map p)) = (1 : ℝ) at he
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) C.radius (C.map p)
    (D.neighborhoodStructure.field (C.map p)) = (1 : ℝ)
  simpa only [one_smul] using he

/-- The radial multiplier is the explicit scalar expression in the
actual radius throughout the collar image. -/
theorem radialWeight_eq_exp_radius (z : D.neighborhoodDomain.extension.Point)
    (hz : z ∈ C.image) : C.radialWeight z =
      Real.exp (CollarStretch.stretch C.width (C.radius z) - C.radius z) := by
  rw [C.radialWeight_image ⟨z, hz⟩, C.radius_image ⟨z, hz⟩]

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
