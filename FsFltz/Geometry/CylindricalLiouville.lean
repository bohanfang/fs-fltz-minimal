import FsFltz.Geometry.CylindricalPrimitive
import FsFltz.Geometry.FormScalarDerivative
import FsFltz.Geometry.CylindricalSymplectic

/-!
# Symplecticity and Liouville field of the constructed stretched primitive

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. The variable-scalar product rule derives the actual differential
of the primitive, and the cylindrical kernel calculation proves its
nondegeneracy. The canonical contraction solution then supplies its smooth
Liouville field. No complete flow or completion is assumed.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
namespace LiouvilleDomain.FlowCollar

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

set_option backward.isDefEq.respectTransparency false in
/-- Localization retains pointwise nondegeneracy on its whole open manifold. -/
theorem localized_nondegenerate (z : C.localizedDomain.domain.extension.Point) :
    C.localizedDomain.domain.extension.Nondegenerate
      (C.localizedDomain.domain.extension.exteriorDerivative
        C.localizedDomain.liouville.primitive) z := by
  intro v hv
  apply D.neighborhood_nondegenerate z.val v
  intro w
  have he := hv w
  unfold evalTwo at he ⊢
  change ((D.neighborhoodDomain.extension.restrict C.neighborhood).exteriorDerivative
    ((D.neighborhoodDomain.extension.restrict C.neighborhood).pullback
      D.neighborhoodDomain.extension Subtype.val D.neighborhoodStructure.primitive) z)
    ![v, w] = 0 at he
  rw [D.neighborhoodDomain.extension.exteriorDerivative_restrict C.neighborhood
    D.neighborhoodStructure.primitive D.neighborhoodStructure.smooth_primitive z] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- The localized original field solves contraction throughout the open extension. -/
theorem localized_contraction (z : C.localizedDomain.domain.extension.Point)
    (v : C.localizedDomain.domain.extension.Tangent z) :
    evalTwo (C.localizedDomain.domain.extension.exteriorDerivative
      C.localizedDomain.liouville.primitive) z (C.localizedDomain.liouville.field z) v =
      evalOne C.localizedDomain.liouville.primitive z v := by
  unfold evalTwo evalOne
  change ((D.neighborhoodDomain.extension.restrict C.neighborhood).exteriorDerivative
    ((D.neighborhoodDomain.extension.restrict C.neighborhood).pullback
      D.neighborhoodDomain.extension Subtype.val D.neighborhoodStructure.primitive) z)
    ![D.neighborhoodStructure.field z.val, v] =
    ((D.neighborhoodDomain.extension.restrict C.neighborhood).pullback
      D.neighborhoodDomain.extension Subtype.val D.neighborhoodStructure.primitive z)
      (fun _ => v)
  rw [D.neighborhoodDomain.extension.exteriorDerivative_restrict C.neighborhood
    D.neighborhoodStructure.primitive D.neighborhoodStructure.smooth_primitive z,
    D.neighborhoodDomain.extension.pullback_restrict_val C.neighborhood
      D.neighborhoodStructure.primitive z]
  exact D.neighborhood_contraction z.val v

/-- The radius remains the actual manifold derivative after localization. -/
theorem scalarDerivative_localized_radius (z : C.localizedDomain.domain.extension.Point)
    (hz : z.val ∈ C.image) (v : C.localizedDomain.domain.extension.Tangent z) :
    C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z v =
      D.neighborhoodDomain.extension.scalarDerivative C.radius z.val v := by
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y : C.neighborhood => C.radius y.val) z v = _
  have hcomp := mfderiv_comp (f := (Subtype.val : C.neighborhood →
    D.neighborhoodDomain.extension.Point)) (g := C.radius) z
    ((C.smoothAt_radius z.val hz).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  erw [D.neighborhoodDomain.extension.mfderiv_restrict_val C.neighborhood z] at hcomp
  exact congrArg (fun A => A v) hcomp

set_option backward.isDefEq.respectTransparency false in
/-- The true collar radius has derivative one along the localized original field. -/
theorem scalarDerivative_localized_radius_field
    (z : C.localizedDomain.domain.extension.Point) (hz : z.val ∈ C.image) :
    C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z
      (C.localizedDomain.liouville.field z) = 1 := by
  rw [C.scalarDerivative_localized_radius z hz]
  change D.neighborhoodDomain.extension.scalarDerivative C.radius z.val
    (D.neighborhoodStructure.field z.val) = 1
  let y : C.image := ⟨z.val, hz⟩
  have he := C.scalarDerivative_radius_field (C.coordinates y) (C.coordinates_mem_strip y)
  rwa [C.map_coordinates y] at he

/-- The explicit one-variable multiplier has its actual chain-rule derivative. -/
theorem radialMultiplier_hasDerivAt {r : ℝ} (hr : r < C.width) :
    HasDerivAt (fun t => Real.exp (CollarStretch.stretch C.width t - t))
      (Real.exp (CollarStretch.stretch C.width r - r) *
        (deriv (CollarStretch.stretch C.width) r - 1)) r := by
  exact (Real.hasDerivAt_exp _).comp r
    (((CollarStretch.stretch_contDiffAt hr).differentiableAt (by simp)).hasDerivAt.sub
      (hasDerivAt_id r))

set_option backward.isDefEq.respectTransparency false in
/-- The radial weight derivative is computed from the actual inverse collar
coordinates, with no supplied differential certificate. -/
theorem scalarDerivative_radialWeight_image
    (z : C.localizedDomain.domain.extension.Point) (hz : z.val ∈ C.image)
    (v : C.localizedDomain.domain.extension.Tangent z) :
    C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radialWeight y.val) z v =
      C.radialWeight z.val * (deriv (CollarStretch.stretch C.width) (C.radius z.val) - 1) *
        C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z v := by
  have hr : C.radius z.val < C.width := by
    rw [C.radius_image ⟨z.val, hz⟩]
    exact (C.coordinates_mem_strip ⟨z.val, hz⟩).2.2
  have hρ := (C.smoothAt_radius z.val hz).comp z (contMDiff_subtype_val z)
  have hq := hasMFDerivAt_iff_hasFDerivAt.mpr (C.radialMultiplier_hasDerivAt hr).hasFDerivAt
  have hc := hq.comp z (hρ.mdifferentiableAt (by simp)).hasMFDerivAt
  have heq : (fun y : C.neighborhood => C.radialWeight y.val) =ᶠ[𝓝 z]
      (fun y => Real.exp (CollarStretch.stretch C.width (C.radius y.val) - C.radius y.val)) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (C.image.isOpen.mem_nhds hz)] with y hy
    exact C.radialWeight_eq_exp_radius y.val hy
  have hd := (hc.congr_of_eventuallyEq_abuse heq).mfderiv
  have hv := congrArg (fun A => A v) hd
  change C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radialWeight y.val) z v =
    (ContinuousLinearMap.toSpanSingleton ℝ
      (Real.exp (CollarStretch.stretch C.width (C.radius z.val) - C.radius z.val) *
        (deriv (CollarStretch.stretch C.width) (C.radius z.val) - 1)))
      (C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z v) at hv
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    ← C.radialWeight_eq_exp_radius z.val hz, mul_comm, mul_left_comm, mul_assoc] using hv

set_option backward.isDefEq.respectTransparency false in
/-- Inside the compact interior the weight is locally constant, so its actual
derivative is zero. -/
theorem scalarDerivative_radialWeight_interior
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z.val ∈ interior D.neighborhoodDomain.carrier)
    (v : C.localizedDomain.domain.extension.Tangent z) :
    C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radialWeight y.val) z v = 0 := by
  have heq : (fun y : C.neighborhood => C.radialWeight y.val) =ᶠ[𝓝 z]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (isOpen_interior.mem_nhds hz)] with y hy
    exact C.radialWeight_carrier y.val (interior_subset hy)
  have he := heq.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, ℝ))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ)
    (fun y : C.neighborhood => C.radialWeight y.val) z v = (0 : ℝ)
  rw [he, mfderiv_const]
  rfl

/-- The derived cylindrical formula evaluates the actual new exterior derivative. -/
theorem evalTwo_stretchedDerivative_image
    (z : C.localizedDomain.domain.extension.Point) (hz : z.val ∈ C.image)
    (v w : C.localizedDomain.domain.extension.Tangent z) :
    evalTwo (C.localizedDomain.domain.extension.exteriorDerivative C.stretchedPrimitive) z v w =
      C.radialWeight z.val *
        (evalTwo (C.localizedDomain.domain.extension.exteriorDerivative
          C.localizedDomain.liouville.primitive) z v w +
        (deriv (CollarStretch.stretch C.width) (C.radius z.val) - 1) *
          (C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z v *
            evalOne C.localizedDomain.liouville.primitive z w -
           C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z w *
            evalOne C.localizedDomain.liouville.primitive z v)) := by
  rw [show C.stretchedPrimitive = (fun y => C.radialWeight y.val •
    C.localizedDomain.liouville.primitive y) from rfl]
  rw [C.localizedDomain.domain.extension.evalTwo_exteriorDerivative_smul
    (fun y => C.radialWeight y.val) C.localizedDomain.liouville.primitive
    C.smooth_radialWeight C.localizedDomain.liouville.smooth_primitive,
    C.scalarDerivative_radialWeight_image z hz v,
    C.scalarDerivative_radialWeight_image z hz w]
  ring

/-- On the compact interior the new differential is exactly the original one. -/
theorem evalTwo_stretchedDerivative_interior
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z.val ∈ interior D.neighborhoodDomain.carrier)
    (v w : C.localizedDomain.domain.extension.Tangent z) :
    evalTwo (C.localizedDomain.domain.extension.exteriorDerivative C.stretchedPrimitive) z v w =
      evalTwo (C.localizedDomain.domain.extension.exteriorDerivative
        C.localizedDomain.liouville.primitive) z v w := by
  rw [show C.stretchedPrimitive = (fun y => C.radialWeight y.val •
    C.localizedDomain.liouville.primitive y) from rfl]
  rw [C.localizedDomain.domain.extension.evalTwo_exteriorDerivative_smul
    (fun y => C.radialWeight y.val) C.localizedDomain.liouville.primitive
    C.smooth_radialWeight C.localizedDomain.liouville.smooth_primitive,
    C.scalarDerivative_radialWeight_interior z hz v,
    C.scalarDerivative_radialWeight_interior z hz w,
    C.radialWeight_carrier z.val (interior_subset hz)]
  ring

/-- The actual derivative of the constructed primitive is nondegenerate at
every point of the localized manifold. -/
theorem stretched_nondegenerate (z : C.localizedDomain.domain.extension.Point) :
    C.localizedDomain.domain.extension.Nondegenerate
      (C.localizedDomain.domain.extension.exteriorDerivative C.stretchedPrimitive) z := by
  rcases z.property with hi | hi
  · intro v hv
    apply C.localized_nondegenerate z v
    intro w
    rw [← C.evalTwo_stretchedDerivative_interior z hi v w]
    exact hv w
  · apply C.localizedDomain.domain.extension.nondegenerate_of_cylindricalDerivative
      C.localizedDomain.liouville.primitive C.stretchedPrimitive z
      (C.localizedDomain.liouville.field z)
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) (fun y : C.neighborhood => C.radius y.val) z)
      (C.localized_nondegenerate z) (C.localized_contraction z)
      (C.scalarDerivative_localized_radius_field z hi)
      (a := deriv (CollarStretch.stretch C.width) (C.radius z.val))
      (f := C.radialWeight z.val)
    · have hr : C.radius z.val < C.width := by
        rw [C.radius_image ⟨z.val, hi⟩]
        exact (C.coordinates_mem_strip ⟨z.val, hi⟩).2.2
      exact (CollarStretch.stretch_deriv_pos C.positive_width hr).ne'
    · exact (C.radialWeight_positive z.val).ne'
    · exact C.evalTwo_stretchedDerivative_image z hi

/-- Smoothness and `d² = 0` upgrade the proved kernel calculation to the
actual symplectic structure on the entire localized manifold. -/
theorem stretched_symplectic : C.localizedDomain.domain.extension.IsSymplecticOn
    (C.localizedDomain.domain.extension.exteriorDerivative C.stretchedPrimitive) univ :=
  (C.localizedDomain.domain.extension.isSymplecticOn_exteriorDerivative_iff
    C.stretchedPrimitive C.smooth_stretchedPrimitive univ).mpr
    (fun z _ => C.stretched_nondegenerate z)

/-- The field is selected by the actual primitive's contraction equation. -/
def stretchedField (z : C.localizedDomain.domain.extension.Point) :
    C.localizedDomain.domain.extension.Tangent z :=
  C.localizedDomain.domain.extension.liouvilleVector C.stretchedPrimitive z

theorem smooth_stretchedField :
    C.localizedDomain.domain.extension.IsSmoothVectorField C.stretchedField :=
  C.localizedDomain.domain.extension.isSmoothVectorField_liouvilleVector
    C.stretchedPrimitive C.smooth_stretchedPrimitive C.stretched_nondegenerate

theorem stretchedField_contraction (z : C.localizedDomain.domain.extension.Point)
    (v : C.localizedDomain.domain.extension.Tangent z) :
    evalTwo (C.localizedDomain.domain.extension.exteriorDerivative C.stretchedPrimitive)
      z (C.stretchedField z) v = evalOne C.stretchedPrimitive z v :=
  C.localizedDomain.domain.extension.liouvilleVector_contraction C.stretchedPrimitive z
    (C.localizedDomain.domain.extension.liouvilleEquation_exists C.stretchedPrimitive z
      (C.stretched_nondegenerate z)) v

set_option backward.isDefEq.respectTransparency false in
/-- On the collar the new Liouville field is the original one divided by
the true positive radial stretch derivative. -/
theorem stretchedField_image (z : C.localizedDomain.domain.extension.Point)
    (hz : z.val ∈ C.image) :
    C.stretchedField z = (deriv (CollarStretch.stretch C.width) (C.radius z.val))⁻¹ •
      C.localizedDomain.liouville.field z := by
  apply C.localizedDomain.domain.extension.liouvilleVector_eq C.stretchedPrimitive z
    (C.stretched_nondegenerate z)
  intro w
  let a := deriv (CollarStretch.stretch C.width) (C.radius z.val)
  let Z := C.localizedDomain.liouville.field z
  have ha : a ≠ 0 := by
    apply (CollarStretch.stretch_deriv_pos C.positive_width ?_).ne'
    rw [C.radius_image ⟨z.val, hz⟩]
    exact (C.coordinates_mem_strip ⟨z.val, hz⟩).2.2
  have hαZ : evalOne C.localizedDomain.liouville.primitive z Z = 0 := by
    rw [← C.localized_contraction z Z]
    exact (C.localizedDomain.domain.extension.exteriorDerivative
      C.localizedDomain.liouville.primitive z).map_eq_zero_of_eq ![Z, Z]
      (i := 0) (j := 1) rfl (by decide)
  have hω : evalTwo (C.localizedDomain.domain.extension.exteriorDerivative
      C.localizedDomain.liouville.primitive) z (a⁻¹ • Z) w =
      a⁻¹ * evalOne C.localizedDomain.liouville.primitive z w := by
    rw [evalTwo_smul_left, C.localized_contraction]
  have hρ : C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z
      (a⁻¹ • Z) = a⁻¹ := by
    unfold scalarDerivative
    rw [map_smul]
    change a⁻¹ * C.localizedDomain.domain.extension.scalarDerivative
      (fun y => C.radius y.val) z Z = _
    rw [C.scalarDerivative_localized_radius_field z hz, mul_one]
  have hα : evalOne C.localizedDomain.liouville.primitive z (a⁻¹ • Z) = 0 := by
    rw [evalOne_smul, hαZ, mul_zero]
  rw [C.evalTwo_stretchedDerivative_image z hz]
  change C.radialWeight z.val *
    (evalTwo (C.localizedDomain.domain.extension.exteriorDerivative
      C.localizedDomain.liouville.primitive) z (a⁻¹ • Z) w + (a - 1) *
      (C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z (a⁻¹ • Z) *
        evalOne C.localizedDomain.liouville.primitive z w -
       C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radius y.val) z w *
        evalOne C.localizedDomain.liouville.primitive z (a⁻¹ • Z))) = _
  rw [hω, hρ, hα]
  change _ = C.radialWeight z.val * evalOne C.localizedDomain.liouville.primitive z w
  field_simp
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The same scaling formula at each actual finite collar point. -/
theorem stretchedField_collarPoint (p : C.strip) :
    C.stretchedField (C.collarPoint p) =
      (deriv (CollarStretch.stretch C.width) p.val.2)⁻¹ •
        C.localizedDomain.liouville.field (C.collarPoint p) := by
  rw [C.stretchedField_image (C.collarPoint p) ⟨p, rfl⟩]
  change (deriv (CollarStretch.stretch C.width) (C.radius (C.map p.val)))⁻¹ • _ = _
  rw [C.radius_map p.val p.property]

/-- The stretch derivative is one on an actual open neighborhood of every
nonpositive radius; this includes the boundary seam. -/
theorem stretch_deriv_eq_one_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    deriv (CollarStretch.stretch C.width) r = 1 := by
  have hr' : r < C.width / 3 := by linarith [C.positive_width]
  have heq : CollarStretch.stretch C.width =ᶠ[𝓝 r] id := by
    filter_upwards [Iio_mem_nhds hr'] with t ht
    exact CollarStretch.stretch_eq_self C.positive_width ht.le
  exact ((hasDerivAt_id r).congr_of_eventuallyEq heq).deriv

/-- On the compact interior, contraction uniqueness recovers the original
localized Liouville field. -/
theorem stretchedField_interior (z : C.localizedDomain.domain.extension.Point)
    (hz : z.val ∈ interior D.neighborhoodDomain.carrier) :
    C.stretchedField z = C.localizedDomain.liouville.field z := by
  apply C.localizedDomain.domain.extension.liouvilleVector_eq C.stretchedPrimitive z
    (C.stretched_nondegenerate z)
  intro v
  rw [C.evalTwo_stretchedDerivative_interior z hz]
  have hc : z ∈ C.localizedDomain.domain.carrier := by
    change z.val ∈ D.neighborhoodDomain.carrier
    exact interior_subset hz
  unfold evalOne
  rw [C.stretchedPrimitive_carrier z hc]
  exact C.localized_contraction z v

set_option backward.isDefEq.respectTransparency false in
/-- The complete compact piece, including the boundary, retains precisely
the original localized field. -/
theorem stretchedField_carrier (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    C.stretchedField z = C.localizedDomain.liouville.field z := by
  rcases z.property with hi | hi
  · exact C.stretchedField_interior z hi
  · have hr : C.radius z.val ≤ 0 := by
      rw [C.radius_image ⟨z.val, hi⟩]
      apply (C.side (C.coordinates ⟨z.val, hi⟩).1 (C.coordinates ⟨z.val, hi⟩).2
        (C.coordinates_mem_strip ⟨z.val, hi⟩).2).mp
      change C.map (C.coordinates ⟨z.val, hi⟩) ∈ D.neighborhoodDomain.carrier
      rw [C.map_coordinates ⟨z.val, hi⟩]
      exact hz
    rw [C.stretchedField_image z hi, C.stretch_deriv_eq_one_of_nonpos hr,
      inv_one, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Under both native open-subset inclusions the new field agrees with the
original supplied compact-domain field. -/
theorem stretchedField_original_carrier (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    C.stretchedField z = D.liouville.field z.val.val := by
  rw [C.stretchedField_carrier z hz]
  exact D.neighborhood_field z.val hz

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
