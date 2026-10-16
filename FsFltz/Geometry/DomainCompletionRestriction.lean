import FsFltz.Geometry.DomainRestriction
import FsFltz.Geometry.BoundaryNondegeneracy

/-!
# Liouville data and supplied completions under extension restriction

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Restricting the extension around the compact carrier preserves
the actual primitive, its differential, the field and outwardness. A supplied
completion restricts to the same completed ambient, with the same complete
flow and end map. Thus its embedded compact piece and full flow core are
unchanged. This transport does not construct a completion from a compact
Liouville domain; the collar/gluing existence bridge remains separate.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- Open-subset pullback is literal restriction on the native tangent fibers. -/
theorem pullback_restrict_val {d k : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (η : M.Form k) (x : U) :
    (M.restrict U).pullback M (Subtype.val : U → M.Point) η x = η x.val := by
  unfold pullback
  erw [M.mfderiv_restrict_val U x]
  ext v
  rfl

/-- The actual exterior derivative restricts with the primitive. -/
theorem exteriorDerivative_restrict {d k : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (η : M.Form k) (hη : M.IsSmoothForm η) (x : U) :
    (M.restrict U).exteriorDerivative ((M.restrict U).pullback M Subtype.val η) x =
      M.exteriorDerivative η x.val := by
  have he := (M.restrict U).exteriorDerivative_pullback M
    (M.restrictInclusion U).map η hη
  exact (congrFun he x).trans (M.pullback_restrict_val U _ x)

theorem pullback_comp_restrict_val {d e k : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (U : TopologicalSpace.Opens M.Point)
    (f : M.SmoothMap N) (η : N.Form k) (x : U) :
    (M.restrict U).pullback N (fun y : U => f y.val) η x = M.pullback N f η x.val := by
  unfold pullback
  rw [M.mfderiv_comp_restrict_val N U x (f.contMDiff.mdifferentiableAt (by simp))]
  rfl

/-- The restriction of a smooth vector field in native tangent fibers. -/
def restrictVector {d : ℕ} (M : SmoothManifold d) (U : TopologicalSpace.Opens M.Point)
    (Z : (x : M.Point) → M.Tangent x) (x : U) : (M.restrict U).Tangent x := Z x.val

theorem vectorInChart_restrict {d : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (Z : (x : M.Point) → M.Tangent x)
    (a : U) {y : Model d} (hy : y ∈ (chartAt (Model d) a).target) :
    (M.restrict U).vectorInChart a (M.restrictVector U Z) y =
      M.vectorInChart a.val Z y := by
  let b := (chartAt (Model d) a).symm y
  have hb : b.val ∈ (chartAt (Model d) a.val).source :=
    ((chartAt (Model d) a).map_target hy).2
  have hval : b.val = (chartAt (Model d) a.val).symm y :=
    (chartAt (Model d) a.val).subtypeRestr_symm_apply ⟨a⟩ hy
  have he := mfderiv_comp (f := (Subtype.val : U → M.Point))
    (g := chartAt (Model d) a.val) b
    ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a.val).mdifferentiableAt hb)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (chartAt (Model d) a) b = _ at he
  erw [M.mfderiv_restrict_val U b] at he
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (chartAt (Model d) a) b (Z b.val) = _
  rw [he]
  exact congrArg (fun z => M.chartTangentMap a.val z (Z z)) hval

theorem isSmoothVectorField_restrict {d : ℕ} (M : SmoothManifold d)
    (U : TopologicalSpace.Opens M.Point) (Z : (x : M.Point) → M.Tangent x)
    (hZ : M.IsSmoothVectorField Z) :
    (M.restrict U).IsSmoothVectorField (M.restrictVector U Z) := by
  intro a
  apply ((hZ a.val).mono
    ((chartAt (Model d) a.val).subtypeRestr_target_subset ⟨a⟩)).congr
  intro y hy
  exact M.vectorInChart_restrict U Z a hy

end SmoothManifold

namespace CompactDomain

/-- The boundary primitive is identical after restriction of the extension. -/
theorem boundaryForm_restrict {d : ℕ} (D : CompactDomain d)
    (U : TopologicalSpace.Opens D.extension.Point) (hU : D.carrier ⊆ U)
    (α : D.extension.Form 1) :
    (D.restrict U hU).boundaryForm ((D.extension.restrict U).pullback
      D.extension Subtype.val α) = D.boundaryForm α := by
  have he := D.boundary.pullback_comp (D.extension.restrict U) D.extension
    ((D.restrict U hU).boundaryInclusion.map.contMDiff.mdifferentiable (by simp))
    ((D.extension.restrictInclusion U).map.contMDiff.mdifferentiable (by simp)) α
  exact he.symm

end CompactDomain

namespace LiouvilleStructure

variable {d : ℕ} {D : CompactDomain d} (L : LiouvilleStructure D)
    (U : TopologicalSpace.Opens D.extension.Point) (hU : D.carrier ⊆ U)

/-- Preserve all actual Liouville data while replacing the extension by an
open neighborhood of its compact carrier. -/
def restrict : LiouvilleStructure (D.restrict U hU) where
  primitive := (D.extension.restrict U).pullback D.extension Subtype.val L.primitive
  smooth_primitive := (D.extension.restrict U).isSmoothForm_pullback_one D.extension
    (D.extension.restrictInclusion U).map L.primitive L.smooth_primitive
  symplectic := by
    apply ((D.extension.restrict U).isSymplecticOn_exteriorDerivative_iff _
      ((D.extension.restrict U).isSmoothForm_pullback_one D.extension
        (D.extension.restrictInclusion U).map L.primitive L.smooth_primitive) _).mpr
    intro x hx v hv
    apply L.symplectic.2.2 x.val hx
    intro w
    have he := hv w
    change evalTwo ((D.extension.restrict U).exteriorDerivative
      ((D.extension.restrict U).pullback D.extension Subtype.val L.primitive)) x v w = 0 at he
    unfold evalTwo at he ⊢
    rw [D.extension.exteriorDerivative_restrict U L.primitive L.smooth_primitive x] at he
    exact he
  field := D.extension.restrictVector U L.field
  smooth_field := D.extension.isSmoothVectorField_restrict U L.field L.smooth_field
  contraction := by
    intro x hx v
    change evalTwo ((D.extension.restrict U).exteriorDerivative
      ((D.extension.restrict U).pullback D.extension Subtype.val L.primitive)) x
      (L.field x.val) v = evalOne ((D.extension.restrict U).pullback
        D.extension Subtype.val L.primitive) x v
    unfold evalTwo evalOne
    rw [D.extension.exteriorDerivative_restrict U L.primitive L.smooth_primitive x,
      D.extension.pullback_restrict_val U L.primitive x]
    exact L.contraction x.val hx v
  outward := by
    intro x hx
    have hx' : x.val ∈ frontier D.carrier := by
      rw [D.frontier_restrict_carrier U] at hx
      exact hx
    let B := D.defining x.val hx'
    have hρ := (B.smooth_rho.contMDiffAt
      (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
    have he := mfderiv_comp (f := (Subtype.val : U → D.extension.Point)) (g := B.rho) x hρ
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp))
    erw [D.extension.mfderiv_restrict_val U x] at he
    change (0 : ℝ) < (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ)
      (fun y : U => B.rho y.val) x (L.field x.val) : ℝ)
    exact (congrArg (fun A => (A (L.field x.val) : ℝ)) he).trans_gt (L.outward x.val hx')

@[simp] theorem restrict_primitive (x : U) :
    (L.restrict U hU).primitive x = L.primitive x.val :=
  D.extension.pullback_restrict_val U L.primitive x

@[simp] theorem restrict_field (x : U) : (L.restrict U hU).field x = L.field x.val := rfl

end LiouvilleStructure

namespace LiouvilleDomain

/-- Restriction of a Liouville domain's extension preserves its compact piece. -/
abbrev restrict {d : ℕ} (D : LiouvilleDomain d)
    (U : TopologicalSpace.Opens D.domain.extension.Point) (hU : D.domain.carrier ⊆ U) :
    LiouvilleDomain d where
  domain := D.domain.restrict U hU
  liouville := D.liouville.restrict U hU

end LiouvilleDomain

namespace Completion

variable {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (U : TopologicalSpace.Opens D.domain.extension.Point) (hU : D.domain.carrier ⊆ U)

private theorem restrict_compact_image :
    (fun x : U => C.inclusion.map x.val) '' (D.domain.restrict U hU).carrier =
      C.inclusion.map '' D.domain.carrier := by
  change (C.inclusion.map ∘ (Subtype.val : U → D.domain.extension.Point)) ''
    (Subtype.val ⁻¹' D.domain.carrier) = _
  rw [image_comp, D.domain.image_restrict_carrier U hU]

/-- Restrict a supplied completion to an open extension neighborhood. Its
completed manifold, primitive, complete flow and cylindrical end are retained.
This construction makes no assertion that every domain has a completion. -/
abbrev restrict : Completion (D.restrict U hU) where
  ambient := C.ambient
  inclusion :=
    { map := ⟨fun x : U => C.inclusion.map x.val,
        C.inclusion.map.contMDiff.comp contMDiff_subtype_val⟩
      embedding := C.inclusion.embedding.comp Topology.IsEmbedding.subtypeVal
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
          (fun y : U => C.inclusion.map y.val) x)
        rw [D.domain.extension.mfderiv_comp_restrict_val C.ambient.manifold U x
          (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))]
        exact C.inclusion.immersion x.val }
  primitive_on_domain := by
    intro x hx
    change (D.domain.extension.restrict U).pullback C.ambient.manifold
      (fun y : U => C.inclusion.map y.val) C.ambient.primitive x =
        (D.liouville.restrict U hU).primitive x
    rw [D.domain.extension.pullback_comp_restrict_val C.ambient.manifold U
      C.inclusion.map C.ambient.primitive x, D.liouville.restrict_primitive]
    exact C.primitive_on_domain x.val hx
  field_on_domain := by
    intro x hx
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (fun y : U => C.inclusion.map y.val) x (D.liouville.field x.val) = _
    rw [D.domain.extension.mfderiv_comp_restrict_val C.ambient.manifold U x
      (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))]
    exact C.field_on_domain x.val hx
  endMap := C.endMap
  smooth_endMap := C.smooth_endMap
  end_flow := C.end_flow
  end_embedding := C.end_embedding
  end_immersion := C.end_immersion
  end_primitive := by
    intro x r v s
    change _ = Real.exp r * evalOne ((D.domain.restrict U hU).boundaryForm
      ((D.domain.extension.restrict U).pullback D.domain.extension Subtype.val
        D.liouville.primitive)) x v
    rw [D.domain.boundaryForm_restrict U hU]
    exact C.end_primitive x r v s
  covering := by
    change (fun x : U => C.inclusion.map x.val) '' (D.domain.restrict U hU).carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) = univ
    rw [C.restrict_compact_image U hU]
    exact C.covering
  overlap := by
    intro x r hr
    change C.endMap (x, r) ∉
      (fun x : U => C.inclusion.map x.val) '' (D.domain.restrict U hU).carrier
    rw [C.restrict_compact_image U hU]
    exact C.overlap x r hr

/-- The compact image in the completed ambient is exactly unchanged. -/
theorem image_restrict_carrier :
    (C.restrict U hU).inclusion.map '' (D.restrict U hU).domain.carrier =
      C.inclusion.map '' D.domain.carrier :=
  C.restrict_compact_image U hU

/-- Restriction preserves the whole intrinsic core, with its all-forward-time
flow condition, through the original open-subset inclusion. -/
theorem core_restrict :
    (C.restrict U hU).core = (Subtype.val : U → D.domain.extension.Point) ⁻¹' C.core := by
  ext x
  change (x.val ∈ D.domain.carrier ∧ ∀ t : ℝ, 0 ≤ t →
    C.ambient.completeFlow.flow t (C.inclusion.map x.val) ∈
      (C.restrict U hU).inclusion.map '' (D.restrict U hU).domain.carrier) ↔
    x.val ∈ C.core
  rw [C.image_restrict_carrier U hU]
  rfl

/-- The full embedded flow core is the same subset of the same completion. -/
theorem image_core_restrict :
    (C.restrict U hU).inclusion.map '' (C.restrict U hU).core =
      C.inclusion.map '' C.core := by
  rw [(C.restrict U hU).image_core_eq_flowCore, C.image_restrict_carrier U hU,
    C.image_core_eq_flowCore]

/-- A specified inclusion marking descends to the restricted compact
presentation, including its original all-real-time flow-induced equation. -/
def restrictInclusionMarking (X : CompleteLiouvilleManifold d)
    (i : D.domain.Point → X.manifold.Point) (q : InclusionMarking C X i) :
    InclusionMarking (C.restrict U hU) X
      (fun x => i (D.domain.restrictPointHomeomorph U hU x)) where
  equiv := q.equiv
  primitive := q.primitive
  inclusion := by
    intro x
    exact q.inclusion (D.domain.restrictPointHomeomorph U hU x)
  flow_induced := q.flow_induced

end Completion

end FsFltz.Geometry
