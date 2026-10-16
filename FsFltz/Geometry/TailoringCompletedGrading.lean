import FsFltz.Geometry.RankTwoMaslov
import FsFltz.Geometry.CylindricalCompletion

/-!
# Maslov representatives under the actual cylindrical stretch

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030;
`geoemtric-part-fsf.tex`, `def:pair`, lines 142–158.
The completion primitive is a positive variable multiple of the native
primitive. Its differential is obtained by a rank-two shear and a positive
scalar. This constructs its compatible field and nonzero canonical square;
it does not assume completed grading data. Joint parameter extension and
the prescribed marked-edge comparisons remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

variable {n : ℕ} {M : SmoothManifold (2 * n)}

namespace SmoothManifold

/-- Inverse chart derivatives of an open restriction retain the actual
native tangent coordinates on the restricted chart target. -/
theorem inverseChartTangentMap_restrict {d : ℕ} (N : SmoothManifold d)
    (U : TopologicalSpace.Opens N.Point) (a : U) {y : Model d}
    (hy : y ∈ (chartAt (Model d) a).target) :
    (N.restrict U).inverseChartTangentMap a y = N.inverseChartTangentMap a.val y := by
  let c := chartAt (Model d) a
  let b := chartAt (Model d) a.val
  have hsub : c.target ⊆ b.target := b.subtypeRestr_target_subset ⟨a⟩
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hy
  have heq : (fun z => (c.symm z).val) =ᶠ[𝓝 y] b.symm := by
    filter_upwards [c.open_target.mem_nhds hy] with z hz
    exact b.subtypeRestr_symm_apply ⟨a⟩ hz
  have hb := ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a.val).mdifferentiableAt_symm (hsub hy)).hasMFDerivAt.congr_of_eventuallyEq_abuse heq
  have hcomp := mfderiv_comp y
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)) hc
  erw [N.mfderiv_restrict_val U (c.symm y)] at hcomp
  exact hcomp.symm.trans hb.mfderiv

/-- Open restriction also retains the forward chart derivative. -/
theorem chartTangentMap_restrict {d : ℕ} (N : SmoothManifold d)
    (U : TopologicalSpace.Opens N.Point) (a x : U)
    (hx : x ∈ (chartAt (Model d) a).source) :
    (N.restrict U).chartTangentMap a x = N.chartTangentMap a.val x.val := by
  have hcomp := mfderiv_comp x
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a.val).mdifferentiableAt hx.2)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  erw [N.mfderiv_restrict_val U x] at hcomp
  exact hcomp

end SmoothManifold

theorem almostComplexInChart_restrict (U : TopologicalSpace.Opens M.Point)
    (J : AlmostComplexField M) (a : U) {y : Model (2 * n)}
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    almostComplexInChart (M.restrict U) a (fun x => J x.val) y =
      almostComplexInChart M a.val J y := by
  have hval : ((chartAt (Model (2 * n)) a).symm y).val =
      (chartAt (Model (2 * n)) a.val).symm y :=
    (chartAt (Model (2 * n)) a.val).subtypeRestr_symm_apply ⟨a⟩ hy
  change ((M.restrict U).chartTangentMap a ((chartAt (Model (2 * n)) a).symm y)).comp
    ((J _).comp ((M.restrict U).inverseChartTangentMap a y)) = _
  rw [M.chartTangentMap_restrict U a _ ((chartAt (Model (2 * n)) a).map_target hy),
    M.inverseChartTangentMap_restrict U a hy, hval]
  rfl

theorem squaredTensorInChart_restrict (U : TopologicalSpace.Opens M.Point)
    (s : M.Point → SquaredCanonicalTensor n) (a : U) {y : Model (2 * n)}
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    squaredTensorInChart (M.restrict U) a (fun x => s x.val) y =
      squaredTensorInChart M a.val s y := by
  have hval : ((chartAt (Model (2 * n)) a).symm y).val =
      (chartAt (Model (2 * n)) a.val).symm y :=
    (chartAt (Model (2 * n)) a.val).subtypeRestr_symm_apply ⟨a⟩ hy
  change (s _).compContinuousLinearMap (fun _ => (M.restrict U).inverseChartTangentMap a y) = _
  rw [M.inverseChartTangentMap_restrict U a hy, hval]
  rfl

namespace MaslovRepresentative

/-- Restriction to an actual open subset constructs native Maslov data
without changing their tangent-coordinate values. -/
def restrict {η : M.Form 2} (s : MaslovRepresentative M η)
    (U : TopologicalSpace.Opens M.Point) :
    MaslovRepresentative (M.restrict U) (fun x => η x.val) where
  J := fun x => s.J x.val
  tensor := fun x => s.tensor x.val
  compatible := by
    refine ⟨?_, fun x => s.compatible.2.1 x.val,
      fun x => s.compatible.2.2.1 x.val, fun x => s.compatible.2.2.2 x.val⟩
    intro a
    exact ((s.compatible.1 a.val).mono
      ((chartAt (Model (2 * n)) a.val).subtypeRestr_target_subset ⟨a⟩)).congr
      (fun _ hy => almostComplexInChart_restrict U s.J a hy)
  canonical := fun x => s.canonical x.val
  smooth := by
    intro a
    exact ((s.smooth a.val).mono
      ((chartAt (Model (2 * n)) a.val).subtypeRestr_target_subset ⟨a⟩)).congr
      (fun _ hy => squaredTensorInChart_restrict U s.tensor a hy)
  nowhereZero := fun x => s.nowhereZero x.val

/-- A primitive representative restricts with the actual exterior derivative. -/
def restrictPrimitive {α : M.Form 1} (s : MaslovRepresentative M (M.exteriorDerivative α))
    (hα : M.IsSmoothForm α) (U : TopologicalSpace.Opens M.Point) :
    MaslovRepresentative (M.restrict U)
      ((M.restrict U).exteriorDerivative ((M.restrict U).pullback M Subtype.val α)) where
  J := (s.restrict U).J
  tensor := (s.restrict U).tensor
  compatible := by
    rw [funext (M.exteriorDerivative_restrict U α hα)]
    exact (s.restrict U).compatible
  canonical := (s.restrict U).canonical
  smooth := (s.restrict U).smooth
  nowhereZero := (s.restrict U).nowhereZero

end MaslovRepresentative

/-- The covector appearing in the differential of a positive variable
multiple of a primitive. -/
def normalizedWeightDifferential (w : M.Point → ℝ) (x : M.Point) :
    M.Tangent x →L[ℝ] ℝ := (w x)⁻¹ • differentialCovector M w x

theorem isSmoothForm_normalizedWeightDifferential (w : M.Point → ℝ)
    (hw : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) :
    M.IsSmoothForm (covectorForm M (normalizedWeightDifferential w)) := by
  convert (isSmoothForm_differentialCovector M hw).function_smul (hw.inv₀ hw0) using 1
  funext x
  ext v
  rfl

namespace MaslovRepresentative

/-- Construct the smooth canonical square for a positive rescaling whose
actual derivative has nonzero shear denominator. -/
def rescalePrimitive {α : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative α))
    (hα : M.IsSmoothForm α) (Z : (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothVectorField Z)
    (hcon : ∀ x v, evalTwo (M.exteriorDerivative α) x (Z x) v = evalOne α x v)
    (w : M.Point → ℝ) (hw : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ w)
    (hwpos : ∀ x, 0 < w x)
    (hden : ∀ x, 1 + normalizedWeightDifferential w x (Z x) ≠ 0) :
    MaslovRepresentative M (M.exteriorDerivative (fun x => w x • α x)) := by
  let p := normalizedWeightDifferential w
  have hp := isSmoothForm_normalizedWeightDifferential w hw (fun x => (hwpos x).ne')
  have hd : ∀ x, 1 + 1 * p x (Z x) ≠ 0 := by simpa using hden
  let q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ := fun x =>
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Model (2 * n))
      (F := ℝ) (0 : Fin 1)).symm (α x)
  have hq (x : M.Point) (v : M.Tangent x) : q x v = evalOne α x v := rfl
  have hform (x : M.Point) (v u : M.Tangent x) :
      evalTwo (M.exteriorDerivative (fun y => w y • α y)) x v u =
        w x * (evalTwo (M.exteriorDerivative α) x v u +
          (p x v * q x u - q x v * p x u)) := by
    rw [M.evalTwo_exteriorDerivative_smul w α hw hα]
    simp only [p, normalizedWeightDifferential, smul_apply,
      smul_eq_mul, hq]
    change w x * _ + _ - _ = w x * (_ +
      ((w x)⁻¹ * M.scalarDerivative w x v * _ - _ * ((w x)⁻¹ * M.scalarDerivative w x u)))
    field_simp [(hwpos x).ne']
    ring
  have hcompat (x : M.Point) := rankTwoShearComplex_compatible
    (SymplecticAlgebra.twoFormBilin (M.exteriorDerivative α x).toAlternatingMap)
    (SymplecticAlgebra.twoFormBilin_isAlt (M.exteriorDerivative α x).toAlternatingMap)
    (p x) (q x) (Z x) (hcon x) 1 (hd x) (s.J x)
    (s.compatible.2.2.1 x) (s.compatible.2.2.2 x)
  refine
    { J := fun x => rankTwoShearComplex (p x) (Z x) 1 (s.J x)
      tensor := fun x => rankTwoShearTensor (p x) (Z x) 1 (s.tensor x)
      compatible := ⟨isSmoothAlmostComplexField_rankTwoShearComplex M p Z 1 hp hZ hd
        s.J s.compatible.1, ?_, ?_, ?_⟩
      canonical := fun x => rankTwoShearTensor_canonical (p x) (Z x) 1 (hd x)
        (s.J x) (s.tensor x) (s.canonical x)
      smooth := isSmoothSquaredTensorSection_rankTwoShearTensor M p Z 1 hp hZ s.tensor s.smooth
      nowhereZero := fun x => rankTwoShearTensor_ne_zero (p x) (Z x) 1 (hd x)
        (s.tensor x) (s.nowhereZero x) }
  · intro x v
    exact rankTwoShearComplex_sq (p x) (Z x) 1 (hd x) (s.J x) (s.compatible.2.1 x) v
  · intro x v u
    rw [hform, hform]
    congr 1
    simpa only [one_mul, SymplecticAlgebra.twoFormBilin_apply,
      ContinuousAlternatingMap.coe_toAlternatingMap, evalTwo] using (hcompat x).1 v u
  · intro x v hv
    rw [hform]
    apply mul_pos (hwpos x)
    simpa only [one_mul, SymplecticAlgebra.twoFormBilin_apply,
      ContinuousAlternatingMap.coe_toAlternatingMap, evalTwo] using (hcompat x).2 v hv

end MaslovRepresentative

namespace LiouvilleDomain.FlowCollar

variable {D : LiouvilleDomain (2 * n)} (C : FlowCollar D)

/-- The collar's actual radial weight has a positive shear denominator:
on its collar this is the derivative of the specified stretch, and in the
interior it is one. -/
theorem normalizedRadialWeight_denominator_positive
    (z : C.localizedDomain.domain.extension.Point) :
    0 < 1 + normalizedWeightDifferential (M := C.localizedDomain.domain.extension) (fun y => C.radialWeight y.val) z
      (C.localizedDomain.liouville.field z) := by
  change 0 < 1 + (C.radialWeight z.val)⁻¹ *
    C.localizedDomain.domain.extension.scalarDerivative (fun y => C.radialWeight y.val) z
      (C.localizedDomain.liouville.field z)
  rcases z.property with hz | hz
  · rw [C.scalarDerivative_radialWeight_interior z hz, mul_zero, add_zero]
    exact zero_lt_one
  · rw [C.scalarDerivative_radialWeight_image z hz,
      C.scalarDerivative_localized_radius_field z hz, mul_one,
      ← mul_assoc, inv_mul_cancel₀ (C.radialWeight_positive z.val).ne', one_mul]
    have hr : C.radius z.val < C.width := by
      rw [C.radius_image ⟨z.val, hz⟩]
      exact (C.coordinates_mem_strip ⟨z.val, hz⟩).2.2
    simpa only [add_sub_cancel] using CollarStretch.stretch_deriv_pos C.positive_width hr

/-- The actual completion has a smooth compatible structure and nonzero
canonical square, constructed from native data on the open collar
neighborhood. No section or complex structure on the completion is assumed. -/
def cylindricalMaslov
    (s : MaslovRepresentative C.localizedDomain.domain.extension
      (C.localizedDomain.domain.extension.exteriorDerivative C.localizedDomain.liouville.primitive)) :
    MaslovRepresentative C.cylindricalCompletion.ambient.manifold
      (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
        C.cylindricalCompletion.ambient.primitive) :=
  s.rescalePrimitive C.localizedDomain.liouville.smooth_primitive
    C.localizedDomain.liouville.field C.localizedDomain.liouville.smooth_field
    C.localized_contraction (fun y => C.radialWeight y.val) C.smooth_radialWeight
    (fun y => C.radialWeight_positive y.val)
    (fun z => (C.normalizedRadialWeight_denominator_positive z).ne')

/-- The native weight is identically one on a genuine neighborhood of each
compact point, including the compact boundary. -/
theorem radialWeight_eventually_one_of_mem_carrier
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    (fun y : C.localizedDomain.domain.extension.Point => C.radialWeight y.val) =ᶠ[𝓝 z]
      (fun _ => (1 : ℝ)) := by
  by_cases hi : z.val ∈ C.image
  · have hr : C.radius z.val ≤ 0 := by
      rw [C.radius_image ⟨z.val, hi⟩]
      apply (C.side (C.coordinates ⟨z.val, hi⟩).1 (C.coordinates ⟨z.val, hi⟩).2
        (C.coordinates_mem_strip ⟨z.val, hi⟩).2).mp
      change C.map (C.coordinates ⟨z.val, hi⟩) ∈ D.neighborhoodDomain.carrier
      rw [C.map_coordinates]
      exact hz
    have hsmall : C.radius z.val < C.width / 3 :=
      hr.trans_lt (div_pos C.positive_width (by norm_num))
    have hcont := (C.smoothAt_radius z.val hi).continuousAt.comp
      continuous_subtype_val.continuousAt
    have hnb := hcont.eventually (isOpen_Iio.mem_nhds hsmall)
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (C.image.isOpen.mem_nhds hi), hnb] with y hy hsmall'
    change C.radius y.val < C.width / 3 at hsmall'
    rw [C.radialWeight_eq_exp_radius y.val hy,
      CollarStretch.stretch_eq_self C.positive_width (le_of_lt hsmall'), sub_self,
      Real.exp_zero]
  · have hzint : z.val ∈ interior D.neighborhoodDomain.carrier :=
      z.property.resolve_right hi
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (isOpen_interior.mem_nhds hzint)] with y hy
    exact C.radialWeight_carrier y.val (interior_subset hy)

/-- The stretching covector vanishes on the whole compact carrier, with
boundary derivatives justified by the open neighborhood identity. -/
theorem normalizedRadialWeightDifferential_eq_zero_of_mem_carrier
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    normalizedWeightDifferential (M := C.localizedDomain.domain.extension) (fun y => C.radialWeight y.val) z = 0 := by
  have hd := (C.radialWeight_eventually_one_of_mem_carrier z hz).mfderiv_eq
    (I := 𝓘(ℝ, Model (2 * n))) (I' := 𝓘(ℝ, ℝ))
  rw [mfderiv_const] at hd
  change (C.radialWeight z.val)⁻¹ •
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun y => C.radialWeight y.val) z = 0
  rw [hd, ContinuousLinearMap.comp_zero, smul_zero]

/-- Both pieces of the completed Maslov representative retain the exact
native values on the compact carrier, including every boundary point. -/
theorem cylindricalMaslov_eq_on_carrier
    (s : MaslovRepresentative C.localizedDomain.domain.extension
      (C.localizedDomain.domain.extension.exteriorDerivative C.localizedDomain.liouville.primitive))
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    (C.cylindricalMaslov s).J z = s.J z ∧
      (C.cylindricalMaslov s).tensor z = s.tensor z := by
  change rankTwoShearComplex (normalizedWeightDifferential (M := C.localizedDomain.domain.extension) (fun y => C.radialWeight y.val) z)
      (C.localizedDomain.liouville.field z) 1 (s.J z) = s.J z ∧
    rankTwoShearTensor (normalizedWeightDifferential (M := C.localizedDomain.domain.extension) (fun y => C.radialWeight y.val) z)
      (C.localizedDomain.liouville.field z) 1 (s.tensor z) = s.tensor z
  rw [C.normalizedRadialWeightDifferential_eq_zero_of_mem_carrier z hz]
  constructor
  · simp [rankTwoShearComplex, rankTwoShear]
  · ext v
    simp [rankTwoShearTensor, rankTwoShear]

/-- A representative on the original domain's extension produces one on
this actual cylindrical completion. Both open restrictions are constructed,
and the stretched compatible structure and tensor are outputs. -/
def cylindricalMaslovOfNative
    (s : MaslovRepresentative D.domain.extension
      (D.domain.extension.exteriorDerivative D.liouville.primitive)) :
    MaslovRepresentative C.cylindricalCompletion.ambient.manifold
      (C.cylindricalCompletion.ambient.manifold.exteriorDerivative
        C.cylindricalCompletion.ambient.primitive) :=
  C.cylindricalMaslov
    ((s.restrictPrimitive D.liouville.smooth_primitive D.symplecticNeighborhood).restrictPrimitive
      D.neighborhoodStructure.smooth_primitive C.neighborhood)

/-- The representative produced on the actual completion recovers the
original native complex structure and full tensor on the compact domain. -/
theorem cylindricalMaslovOfNative_eq_on_carrier
    (s : MaslovRepresentative D.domain.extension
      (D.domain.extension.exteriorDerivative D.liouville.primitive))
    (z : C.localizedDomain.domain.extension.Point)
    (hz : z ∈ C.localizedDomain.domain.carrier) :
    (C.cylindricalMaslovOfNative s).J z = s.J z.val.val ∧
      (C.cylindricalMaslovOfNative s).tensor z = s.tensor z.val.val :=
  C.cylindricalMaslov_eq_on_carrier _ z hz

end LiouvilleDomain.FlowCollar
end FsFltz.Geometry
