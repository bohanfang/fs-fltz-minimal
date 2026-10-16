import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.ZeroDimensional
import FsFltz.Geometry.BoundaryAtlas

/-!
# Construction of zero-dimensional completions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814 and 825–830. A compact zero-dimensional domain has an open,
finite carrier. Restrict its extension to this carrier using the native
open-subset construction. The restricted primitive and vector field vanish,
the complete flow is the identity for every real time, and the end is empty.
This constructs an actual `Completion` without assuming one.

Restriction is necessary for this presentation: `Completion.inclusion` embeds
the whole extension, while the completion of a finite domain has no points
outside its compact piece.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

/-- Native charts make every zero-dimensional smooth manifold discrete. -/
theorem discreteTopology_of_dimension_zero (M : SmoothManifold 0) :
    DiscreteTopology M.Point := by
  let : Subsingleton (Model 0) := ⟨fun _ _ => PiLp.ext (fun i => Fin.elim0 i)⟩
  let : DiscreteTopology (Model 0) := inferInstance
  exact ChartedSpace.discreteTopology (Model 0) M.Point

/-- The zero-dimensional tangent space contains only the zero vector. -/
theorem tangent_eq_zero_of_dimension_zero (M : SmoothManifold 0)
    (x : M.Point) (v : M.Tangent x) : v = 0 := by
  exact PiLp.ext (fun i => Fin.elim0 i)

/-- In dimension zero every one-form is the zero form. -/
theorem oneForm_eq_zero_of_dimension_zero (M : SmoothManifold 0) (α : M.Form 1) :
    α = 0 := by
  funext x
  ext v
  exact (α x).map_coord_zero (0 : Fin 1) (M.tangent_eq_zero_of_dimension_zero x (v 0))

end SmoothManifold

namespace CompactDomain

/-- The carrier is itself an open extension neighborhood in dimension zero. -/
def carrierOpen_of_dimension_zero (D : CompactDomain 0) :
    TopologicalSpace.Opens D.extension.Point := by
  let : DiscreteTopology D.extension.Point := D.extension.discreteTopology_of_dimension_zero
  exact ⟨D.carrier, isOpen_discrete D.carrier⟩

@[simp] theorem mem_carrierOpen_of_dimension_zero (D : CompactDomain 0)
    (x : D.extension.Point) : x ∈ D.carrierOpen_of_dimension_zero ↔ x ∈ D.carrier := Iff.rfl

end CompactDomain

namespace LiouvilleDomain

/-- The original compact piece, presented with precisely its open carrier as
extension. Its smooth primitive and field are the original restrictions. -/
abbrev carrierRestriction_of_dimension_zero (D : LiouvilleDomain 0) : LiouvilleDomain 0 :=
  D.restrict D.domain.carrierOpen_of_dimension_zero (fun _ hx => hx)

@[simp] theorem carrierRestriction_carrier_of_dimension_zero (D : LiouvilleDomain 0) :
    D.carrierRestriction_of_dimension_zero.domain.carrier = univ := by
  ext x
  exact iff_true_intro x.property

/-- The restricted domain retains the same finite compact piece. -/
theorem carrierRestriction_finite_of_dimension_zero (D : LiouvilleDomain 0) :
    D.carrierRestriction_of_dimension_zero.domain.carrier.Finite :=
  D.carrierRestriction_of_dimension_zero.domain.finite_of_dimension_zero

/-- Native diffeomorphism of the compact point spaces; it is defined also
when the original compact domain is empty. -/
def carrierRestrictionDiffeomorph_of_dimension_zero (D : LiouvilleDomain 0) :
    letI := D.carrierRestriction_of_dimension_zero.domain.zeroChartedSpace
    letI := D.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      D.carrierRestriction_of_dimension_zero.domain.Point D.domain.Point ∞ := by
  letI := D.carrierRestriction_of_dimension_zero.domain.zeroChartedSpace
  letI := D.domain.zeroChartedSpace
  letI := D.carrierRestriction_of_dimension_zero.domain.discreteTopology_zero
  letI := D.domain.discreteTopology_zero
  exact
    { toEquiv := (D.domain.restrictPointHomeomorph D.domain.carrierOpen_of_dimension_zero
        (fun _ hx => hx)).toEquiv
      contMDiff_toFun := contMDiff_of_discreteTopology
      contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem carrierRestrictionDiffeomorph_val_of_dimension_zero (D : LiouvilleDomain 0)
    (x : D.carrierRestriction_of_dimension_zero.domain.Point) :
    (D.carrierRestrictionDiffeomorph_of_dimension_zero x).val = x.val.val := rfl

/-- Localization keeps the actual original primitive at every compact point. -/
theorem carrierRestriction_primitive_of_dimension_zero (D : LiouvilleDomain 0)
    (x : D.carrierRestriction_of_dimension_zero.domain.extension.Point) :
    D.carrierRestriction_of_dimension_zero.liouville.primitive x =
      D.liouville.primitive x.val :=
  D.liouville.restrict_primitive D.domain.carrierOpen_of_dimension_zero (fun _ hx => hx) x

/-- Localization keeps the actual original vector field in the native tangent
fibers, rather than introducing a different Liouville structure. -/
theorem carrierRestriction_field_of_dimension_zero (D : LiouvilleDomain 0)
    (x : D.carrierRestriction_of_dimension_zero.domain.extension.Point) :
    D.carrierRestriction_of_dimension_zero.liouville.field x = D.liouville.field x.val := rfl

private def carrierCompleteFlow (D : LiouvilleDomain 0) :
    CompleteLiouvilleFlow D.carrierRestriction_of_dimension_zero.domain.extension
      D.carrierRestriction_of_dimension_zero.liouville.field where
  flow := Flow.id ℝ _
  smooth_action := contMDiff_snd
  solves := by
    intro x t a _
    change HasDerivAt (fun _ : ℝ => chartAt (Model 0) a x)
      (D.carrierRestriction_of_dimension_zero.domain.extension.chartTangentMap a x
        (D.carrierRestriction_of_dimension_zero.liouville.field x)) t
    have hz : D.carrierRestriction_of_dimension_zero.domain.extension.chartTangentMap a x
        (D.carrierRestriction_of_dimension_zero.liouville.field x) = 0 :=
      PiLp.ext (fun i => Fin.elim0 i)
    rw [hz]
    exact hasDerivAt_const t (chartAt (Model 0) a x)

/-- Complete ambient on the finite carrier, with the actual restricted
primitive and field and an explicitly constructed all-real-time flow. -/
def carrierCompleteManifold_of_dimension_zero (D : LiouvilleDomain 0) :
    CompleteLiouvilleManifold 0 where
  manifold := D.carrierRestriction_of_dimension_zero.domain.extension
  primitive := D.carrierRestriction_of_dimension_zero.liouville.primitive
  smooth_primitive := D.carrierRestriction_of_dimension_zero.liouville.smooth_primitive
  symplectic := by
    have h := D.carrierRestriction_of_dimension_zero.liouville.symplectic
    rw [D.carrierRestriction_carrier_of_dimension_zero] at h
    exact h
  field := D.carrierRestriction_of_dimension_zero.liouville.field
  smooth_field := D.carrierRestriction_of_dimension_zero.liouville.smooth_field
  contraction := fun x => D.carrierRestriction_of_dimension_zero.liouville.contraction x x.property
  completeFlow := D.carrierCompleteFlow

/-- Actual completion existence in dimension zero. The inclusion is identity,
and the empty boundary contributes no cylindrical points. -/
def carrierCompletion_of_dimension_zero (D : LiouvilleDomain 0) :
    Completion D.carrierRestriction_of_dimension_zero := by
  let E := D.carrierRestriction_of_dimension_zero
  let : IsEmpty E.domain.boundary.Point := E.domain.zero_boundary rfl
  exact
    { ambient := D.carrierCompleteManifold_of_dimension_zero
      inclusion :=
        { map := ContMDiffMap.id
          embedding := Topology.IsEmbedding.id
          immersion := fun x => by
            change Function.Injective (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) id x)
            rw [mfderiv_id]
            exact Function.injective_id }
      primitive_on_domain := fun x _ => congrFun (E.domain.extension.pullback_id E.liouville.primitive) x
      field_on_domain := fun x _ => by
        change mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) id x (E.liouville.field x) = _
        rw [mfderiv_id]
        rfl
      endMap := fun p => isEmptyElim p.1
      smooth_endMap := contMDiff_of_discreteTopology
      end_flow := fun x => isEmptyElim x
      end_embedding := Topology.IsEmbedding.of_subsingleton _
      end_immersion := fun p => isEmptyElim p.1
      end_primitive := fun x => isEmptyElim x
      covering := by
        apply eq_univ_of_forall
        intro x
        exact Or.inl ⟨x, x.property, rfl⟩
      overlap := fun x => isEmptyElim x }

/-- No supplied completion is needed for the zero-dimensional construction. -/
theorem nonempty_carrierCompletion_of_dimension_zero (D : LiouvilleDomain 0) :
    Nonempty (Completion D.carrierRestriction_of_dimension_zero) :=
  ⟨D.carrierCompletion_of_dimension_zero⟩

@[simp] theorem carrierCompletion_primitive_of_dimension_zero (D : LiouvilleDomain 0) :
    D.carrierCompletion_of_dimension_zero.ambient.primitive = 0 :=
  D.carrierRestriction_of_dimension_zero.domain.extension.oneForm_eq_zero_of_dimension_zero _

@[simp] theorem carrierCompletion_field_of_dimension_zero (D : LiouvilleDomain 0)
    (x : D.carrierRestriction_of_dimension_zero.domain.extension.Point) :
    D.carrierCompletion_of_dimension_zero.ambient.field x = (0 : Model 0) :=
  D.carrierRestriction_of_dimension_zero.domain.extension.tangent_eq_zero_of_dimension_zero x _

@[simp] theorem carrierCompletion_flow_of_dimension_zero (D : LiouvilleDomain 0)
    (t : ℝ) (x : D.carrierRestriction_of_dimension_zero.domain.extension.Point) :
    D.carrierCompletion_of_dimension_zero.ambient.completeFlow.flow t x = x := rfl

/-- The constructed completion's full intrinsic core is the whole finite domain. -/
@[simp] theorem carrierCompletion_core_of_dimension_zero (D : LiouvilleDomain 0) :
    D.carrierCompletion_of_dimension_zero.core = univ := by
  rw [Completion.core_eq_carrier_of_dimension_zero, D.carrierRestriction_carrier_of_dimension_zero]

/-- The newly constructed full core is the original compact carrier under
the actual open-subset inclusion. This consumes the constructed completion
and the stationary-flow core theorem, with no completion hypothesis. -/
theorem image_carrierCompletion_core_of_dimension_zero (D : LiouvilleDomain 0) :
    (Subtype.val : D.carrierRestriction_of_dimension_zero.domain.extension.Point →
      D.domain.extension.Point) '' D.carrierCompletion_of_dimension_zero.core = D.domain.carrier := by
  rw [Completion.core_eq_carrier_of_dimension_zero]
  exact D.domain.image_restrict_carrier D.domain.carrierOpen_of_dimension_zero (fun _ hx => hx)

end LiouvilleDomain

end FsFltz.Geometry
