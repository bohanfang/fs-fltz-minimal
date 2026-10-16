import FsFltz.Geometry.BoundaryCharts

/-!
# Restricting compact extension presentations

Source: `geoemtric-part-fsf.tex`, the smooth-extension conventions and
`def:pair`, lines 119–160, and the completion handoff `sec:lean`, lines 783–814.
An extension manifold may be replaced by any open neighborhood of the compact
carrier. The carrier is pulled back under the native open-subset inclusion;
the boundary manifold and its defining functions are retained. The native
charts are restrictions of the original charts. The inclusion has identity
tangent map, so regularity and the actual defining-function derivatives are
preserved. No completion existence is assumed by this construction.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry

namespace SmoothManifold

/-- The native smooth manifold on an open subset, with Mathlib's restricted
atlas and the induced topology. -/
abbrev restrict {d : ℕ} (M : SmoothManifold d) (U : TopologicalSpace.Opens M.Point) :
    SmoothManifold d where
  Point := U
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

/-- The differential of the native open-subset inclusion is the identity on
the model tangent fiber. -/
theorem mfderiv_restrict_val {d : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (x : U) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (Subtype.val : U → M.Point) x =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Model d) x) := by
  have he := mfderiv_comp (f := (Subtype.val : U → M.Point))
    (g := chartAt (Model d) x.val) x
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x.val).mdifferentiableAt
      (mem_chart_source _ _))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  have ha := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model d)) (x := x.val)
  have hb := mfderiv_extChartAt_self (I := 𝓘(ℝ, Model d)) (x := x)
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (chartAt (Model d) x.val) x.val = _ at ha
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (chartAt (Model d) x) x = _ at hb
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (chartAt (Model d) x) x = _ at he
  erw [ha, hb] at he
  exact he.symm

/-- The actual smooth open-subset inclusion. -/
def restrictInclusion {d : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) : (M.restrict U).SmoothEmbedding M where
  map := ⟨Subtype.val, contMDiff_subtype_val⟩
  embedding := Topology.IsEmbedding.subtypeVal
  immersion := by
    intro x
    change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (Subtype.val : U → M.Point) x)
    erw [M.mfderiv_restrict_val U x]
    exact Function.injective_id

theorem mfderiv_comp_restrict_val {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (U : TopologicalSpace.Opens M.Point)
    {f : M.Point → N.Point} (x : U)
    (hf : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x.val) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) (fun y : U => f y.val) x =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) f x.val := by
  have he := mfderiv_comp (f := (Subtype.val : U → M.Point)) (g := f) x hf
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  erw [M.mfderiv_restrict_val U x] at he
  exact he

end SmoothManifold

namespace CompactDomain

variable {d : ℕ} (D : CompactDomain d)
    (U : TopologicalSpace.Opens D.extension.Point) (hU : D.carrier ⊆ U)

include hU in
/-- Restriction preserves the entire carrier, not only its boundary. -/
theorem image_restrict_carrier :
    (Subtype.val : U → D.extension.Point) '' (Subtype.val ⁻¹' D.carrier) = D.carrier := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hU hx⟩, hx, rfl⟩

theorem frontier_restrict_carrier :
    frontier ((Subtype.val : U → D.extension.Point) ⁻¹' D.carrier) =
      Subtype.val ⁻¹' frontier D.carrier :=
  (U.isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
    continuous_subtype_val D.carrier).symm

private def restrictBoundaryMap (x : D.boundary.Point) : U :=
  ⟨D.boundaryInclusion.map x, hU (D.compact.isClosed.frontier_subset (by
    rw [← D.boundary_range]
    exact ⟨x, rfl⟩))⟩

private theorem smooth_restrictBoundaryMap :
    ContMDiff 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) ∞ (D.restrictBoundaryMap U hU) :=
  (ContMDiff.subtypeVal_comp_iff U _).mp D.boundaryInclusion.map.contMDiff

private def restrictBoundaryInclusion :
    D.boundary.SmoothEmbedding (D.extension.restrict U) where
  map := ⟨D.restrictBoundaryMap U hU, D.smooth_restrictBoundaryMap U hU⟩
  embedding := Topology.IsEmbedding.of_comp
    (D.smooth_restrictBoundaryMap U hU).continuous continuous_subtype_val
    D.boundaryInclusion.embedding
  immersion := by
    intro x v w hvw
    apply D.boundaryInclusion.immersion x
    have he := mfderiv_comp (f := D.restrictBoundaryMap U hU)
      (g := (Subtype.val : U → D.extension.Point)) x
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
      ((D.smooth_restrictBoundaryMap U hU).mdifferentiableAt (by simp))
    change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.boundaryInclusion.map x = _ at he
    erw [he]
    exact congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (Subtype.val : U → D.extension.Point) (D.restrictBoundaryMap U hU x)) hvw

private def restrictDefining (x : U)
    (hx : x ∈ frontier (Subtype.val ⁻¹' D.carrier)) :
    BoundaryDefiningFunction (D.extension.restrict U) (Subtype.val ⁻¹' D.carrier) x := by
  have hx' : x.val ∈ frontier D.carrier := by
    rw [D.frontier_restrict_carrier U] at hx
    exact hx
  let B := D.defining x.val hx'
  refine
    { neighbourhood := Subtype.val ⁻¹' B.neighbourhood
      open_neighbourhood := B.open_neighbourhood.preimage continuous_subtype_val
      mem_neighbourhood := B.mem_neighbourhood
      rho := fun y => B.rho y.val
      smooth_rho := B.smooth_rho.comp contMDiff_subtype_val.contMDiffOn (fun _ hy => hy)
      sublevel := fun y hy => B.sublevel y.val hy
      zero_level := ?_
      regular := ?_ }
  · intro y hy
    rw [D.frontier_restrict_carrier U]
    exact B.zero_level y.val hy
  · have hρ := (B.smooth_rho.contMDiffAt
      (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
    have he := mfderiv_comp (f := (Subtype.val : U → D.extension.Point)) (g := B.rho) x hρ
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
    erw [D.extension.mfderiv_restrict_val U x] at he
    exact fun hz => B.regular (he.symm.trans hz)

/-- Replace the extension by any open neighborhood of the compact carrier.
The boundary presentation remains the original one and all local defining
equations are literally restrictions. -/
abbrev restrict : CompactDomain d where
  extension := D.extension.restrict U
  carrier := Subtype.val ⁻¹' D.carrier
  compact := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, D.image_restrict_carrier U hU]
    exact D.compact
  defining := D.restrictDefining U
  boundary := D.boundary
  boundaryInclusion := D.restrictBoundaryInclusion U hU
  boundary_range := by
    rw [D.frontier_restrict_carrier U]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change D.boundaryInclusion.map x ∈ frontier D.carrier
      rw [← D.boundary_range]
      exact ⟨x, rfl⟩
    · intro hy
      obtain ⟨x, hx⟩ : ∃ x, D.boundaryInclusion.map x = y.val := by
        rw [← D.boundary_range] at hy
        exact hy
      exact ⟨x, Subtype.ext hx⟩
  zero_boundary := D.zero_boundary

@[simp] theorem restrict_carrier : (D.restrict U hU).carrier = Subtype.val ⁻¹' D.carrier := rfl

@[simp] theorem restrict_boundary : (D.restrict U hU).boundary = D.boundary := rfl

@[simp] theorem restrict_boundaryInclusion_val (x : D.boundary.Point) :
    ((D.restrict U hU).boundaryInclusion.map x).val = D.boundaryInclusion.map x := rfl

/-- The compact domain itself is unchanged as a topological space. -/
def restrictPointHomeomorph : (D.restrict U hU).Point ≃ₜ D.Point where
  toFun := fun x => ⟨x.val.val, x.property⟩
  invFun := fun x => ⟨⟨x.val, hU x.property⟩, x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end CompactDomain

end FsFltz.Geometry
