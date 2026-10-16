import FsFltz.Geometry.DomainRestriction
import FsFltz.Geometry.BoundaryPresentationBridge

/-!
# Native compact atlases under open extension restriction

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Restricting a compact domain's ambient extension to an open
neighborhood of its full carrier preserves its native smooth presentation.
Both smooth directions are proved from the actual ambient inclusions and
their native chart correspondence. The zero-dimensional case uses the
already constructed discrete atlases.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompactDomain

variable {d : ℕ} [NeZero d] (D : CompactDomain d)
  (U : TopologicalSpace.Opens D.extension.Point) (hU : D.carrier ⊆ U)

local instance restrictionNativeChartedSpace :
    ChartedSpace (EuclideanHalfSpace d) (D.restrict U hU).Point :=
  (D.restrict U hU).halfSpaceChartedSpace

/-- Point reassociation is smooth from the restricted native compact atlas
to the original one, by composition of the actual ambient inclusions. -/
theorem contMDiff_restrictPointHomeomorph :
    ContMDiff (𝓡∂ d) (𝓡∂ d) ∞ (D.restrictPointHomeomorph U hU) := by
  apply D.contMDiff_iff_subtype_val.mpr
  exact (D.extension.restrictInclusion U).map.contMDiff.comp
    (D.restrict U hU).contMDiff_subtype_val

/-- The inverse point reassociation is smooth into the restricted native
atlas, using the open-subset inclusion's smooth-map equivalence. -/
theorem contMDiff_restrictPointHomeomorph_symm :
    ContMDiff (𝓡∂ d) (𝓡∂ d) ∞ (D.restrictPointHomeomorph U hU).symm := by
  apply (D.restrict U hU).contMDiff_iff_subtype_val.mpr
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact D.contMDiff_subtype_val

/-- Open restriction changes no compact native manifold. The map sends
a restricted compact point to the same original ambient point. -/
def restrictPointDiffeomorph : Diffeomorph (𝓡∂ d) (𝓡∂ d)
    (D.restrict U hU).Point D.Point ∞ where
  toEquiv := (D.restrictPointHomeomorph U hU).toEquiv
  contMDiff_toFun := D.contMDiff_restrictPointHomeomorph U hU
  contMDiff_invFun := D.contMDiff_restrictPointHomeomorph_symm U hU

@[simp] theorem restrictPointDiffeomorph_val (x : (D.restrict U hU).Point) :
    (D.restrictPointDiffeomorph U hU x).val = x.val.val := rfl

@[simp] theorem restrictPointDiffeomorph_symm_val (x : D.Point) :
    ((D.restrictPointDiffeomorph U hU).symm x).val.val = x.val := rfl

section Zero

variable (D : CompactDomain 0) (U : TopologicalSpace.Opens D.extension.Point)
  (hU : D.carrier ⊆ U)

local instance zeroRestrictionNativeChartedSpace :
    ChartedSpace (Model 0) (D.restrict U hU).Point :=
  (D.restrict U hU).zeroChartedSpace

local instance zeroRestrictionDiscreteTopology : DiscreteTopology (D.restrict U hU).Point :=
  (D.restrict U hU).discreteTopology_zero

/-- In dimension zero both actual compact point spaces have the discrete
native atlas, so the same point reassociation is a diffeomorphism. -/
def zero_restrictPointDiffeomorph :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) (D.restrict U hU).Point D.Point ∞ where
  toEquiv := (D.restrictPointHomeomorph U hU).toEquiv
  contMDiff_toFun := contMDiff_of_discreteTopology
  contMDiff_invFun := contMDiff_of_discreteTopology

@[simp] theorem zero_restrictPointDiffeomorph_val
    (x : (D.restrict U hU).Point) :
    (D.zero_restrictPointDiffeomorph U hU x).val = x.val.val := rfl

end Zero

end FsFltz.Geometry.CompactDomain
