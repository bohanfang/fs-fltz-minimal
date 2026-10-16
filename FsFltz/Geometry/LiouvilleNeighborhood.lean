import FsFltz.Geometry.DomainCompletionRestriction
import FsFltz.Geometry.FamilyLiouville

/-!
# A genuine symplectic neighborhood of a compact Liouville domain

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–158, and `sec:lean`,
lines 783–814. Nondegeneracy is open in the actual smooth chart coefficients.
Restricting to that open locus gives a primitive with symplectic differential
on the entire extension. Its canonical Liouville field satisfies contraction
there, not merely on the compact carrier, and agrees with the supplied field
on the carrier. This is a prerequisite for a two-sided Liouville collar;
no collar, complete flow or completion is assumed or constructed here.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace SmoothManifold

/-- Nondegeneracy of a smooth two-form is an open condition on the actual
manifold, obtained from invertibility of its chart contraction operator. -/
theorem isOpen_nondegenerate {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (heta : M.IsSmoothForm eta) :
    IsOpen {x | M.Nondegenerate eta x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let c := chartAt (Model d) x
  let A : Model d → Model d →L[ℝ] Model d :=
    fun y => chartContraction (M.formInChart x eta y)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A c.target :=
    contDiffOn_const.clm_comp (hcur.comp_contDiffOn (heta x))
  have hxs : x ∈ c.source := mem_chart_source _ _
  have hxt : c x ∈ c.target := c.map_source hxs
  have hinv : (A (c x)).IsInvertible := by
    apply chartContraction_invertible
    apply M.nondegenerate_formInChart eta x hxt
    change M.Nondegenerate eta (c.symm (c x))
    rwa [c.left_inv hxs]
  have hev : ∀ᶠ y in 𝓝 (c x), (A y).IsInvertible :=
    (hA.continuousOn.continuousAt (c.open_target.mem_nhds hxt)).eventually_mem
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hinv)
  filter_upwards [c.open_source.mem_nhds hxs, (c.continuousAt hxs).eventually hev] with y hy hi
  have hnd := M.nondegenerate_of_formInChart eta x (c.map_source hy)
    (nondegenerate_of_chartContraction_invertible _ hi)
  change M.Nondegenerate eta (c.symm (c y)) at hnd
  simpa only [c.left_inv hy] using hnd

end SmoothManifold

namespace LiouvilleDomain

variable {d : ℕ} (D : LiouvilleDomain d)

/-- The open nondegeneracy locus of the given primitive, rather than a
neighborhood supplied as extra input. -/
def symplecticNeighborhood : TopologicalSpace.Opens D.domain.extension.Point :=
  ⟨{x | D.domain.extension.Nondegenerate
    (D.domain.extension.exteriorDerivative D.liouville.primitive) x},
    D.domain.extension.isOpen_nondegenerate _ D.liouville.symplectic.1⟩

theorem carrier_subset_symplecticNeighborhood :
    D.domain.carrier ⊆ D.symplecticNeighborhood :=
  D.liouville.symplectic.2.2

/-- The same compact domain on a symplectic open extension. -/
abbrev neighborhoodDomain : CompactDomain d :=
  D.domain.restrict D.symplecticNeighborhood D.carrier_subset_symplecticNeighborhood

private abbrev restrictedStructure : LiouvilleStructure D.neighborhoodDomain :=
  D.liouville.restrict D.symplecticNeighborhood D.carrier_subset_symplecticNeighborhood

theorem neighborhood_nondegenerate (x : D.neighborhoodDomain.extension.Point) :
    D.neighborhoodDomain.extension.Nondegenerate
      (D.neighborhoodDomain.extension.exteriorDerivative D.restrictedStructure.primitive) x := by
  change ∀ v, (∀ w, _) → v = 0
  intro v hv
  apply x.property v
  intro w
  have he := hv w
  unfold SmoothManifold.evalTwo at he ⊢
  erw [D.domain.extension.exteriorDerivative_restrict D.symplecticNeighborhood
    D.liouville.primitive D.liouville.smooth_primitive x] at he
  exact he

/-- The canonical field agrees with the supplied field everywhere on the
compact carrier, although no contraction law off that carrier was assumed. -/
theorem neighborhood_liouvilleVector_eq (x : D.neighborhoodDomain.extension.Point)
    (hx : x ∈ D.neighborhoodDomain.carrier) :
    D.neighborhoodDomain.extension.liouvilleVector D.restrictedStructure.primitive x =
      D.liouville.field x.val :=
  (D.restrictedStructure.field_eq_liouvilleVector x hx).symm

/-- Replace only the off-carrier field by the canonical contraction solution.
This produces a smooth Liouville structure whose equation holds on an actual
open neighborhood, and preserves outwardness on the original boundary. -/
def neighborhoodStructure : LiouvilleStructure D.neighborhoodDomain where
  primitive := D.restrictedStructure.primitive
  smooth_primitive := D.restrictedStructure.smooth_primitive
  symplectic := D.restrictedStructure.symplectic
  field := D.neighborhoodDomain.extension.liouvilleVector D.restrictedStructure.primitive
  smooth_field := D.neighborhoodDomain.extension.isSmoothVectorField_liouvilleVector _
    D.restrictedStructure.smooth_primitive D.neighborhood_nondegenerate
  contraction := fun x _ => D.neighborhoodDomain.extension.liouvilleVector_contraction _ x
    (D.neighborhoodDomain.extension.liouvilleEquation_exists _ x (D.neighborhood_nondegenerate x))
  outward := by
    intro x hx
    have hxc : x ∈ D.neighborhoodDomain.carrier :=
      D.neighborhoodDomain.compact.isClosed.frontier_subset hx
    rw [← D.restrictedStructure.field_eq_liouvilleVector x hxc]
    exact D.restrictedStructure.outward x hx

/-- Symplecticity now holds on the entire localized extension. -/
theorem neighborhood_symplectic : D.neighborhoodDomain.extension.IsSymplecticOn
    (D.neighborhoodDomain.extension.exteriorDerivative D.neighborhoodStructure.primitive) univ :=
  (D.neighborhoodDomain.extension.isSymplecticOn_exteriorDerivative_iff _
    D.neighborhoodStructure.smooth_primitive _).mpr (fun x _ => D.neighborhood_nondegenerate x)

/-- The actual contraction equation holds on both sides of the boundary. -/
theorem neighborhood_contraction (x : D.neighborhoodDomain.extension.Point) (v) :
    SmoothManifold.evalTwo
      (D.neighborhoodDomain.extension.exteriorDerivative D.neighborhoodStructure.primitive) x
      (D.neighborhoodStructure.field x) v =
      SmoothManifold.evalOne D.neighborhoodStructure.primitive x v :=
  D.neighborhoodDomain.extension.liouvilleVector_contraction _ x
    (D.neighborhoodDomain.extension.liouvilleEquation_exists _ x (D.neighborhood_nondegenerate x)) v

/-- The localized primitive is the original primitive under the actual
open-subset inclusion. -/
theorem neighborhood_primitive (x : D.neighborhoodDomain.extension.Point) :
    D.neighborhoodStructure.primitive x = D.liouville.primitive x.val :=
  D.domain.extension.pullback_restrict_val D.symplecticNeighborhood _ x

/-- Canonical replacement changes no field value on the compact domain. -/
theorem neighborhood_field (x : D.neighborhoodDomain.extension.Point)
    (hx : x ∈ D.neighborhoodDomain.carrier) :
    D.neighborhoodStructure.field x = D.liouville.field x.val :=
  D.neighborhood_liouvilleVector_eq x hx

/-- The boundary primitive used for the collar is exactly the original one. -/
theorem neighborhood_boundaryForm :
    D.neighborhoodDomain.boundaryForm D.neighborhoodStructure.primitive =
      D.domain.boundaryForm D.liouville.primitive :=
  D.domain.boundaryForm_restrict D.symplecticNeighborhood
    D.carrier_subset_symplecticNeighborhood D.liouville.primitive

end LiouvilleDomain
end FsFltz.Geometry
