import FsFltz.Geometry.LiouvilleNeighborhood

/-!
# Symplectic restriction before Liouville outwardness

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. A compact domain, a smooth primitive, and nondegeneracy of its
actual exterior derivative on the carrier determine an open symplectic
extension. The canonical Liouville field is smooth and satisfies contraction
on this entire extension. No field, outwardness, or Liouville-domain structure
is assumed. Strict outwardness and the existence of a completion remain
separate obligations, including for applications to a far-fiber ribbon.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
namespace CompactDomain

variable {d : ℕ} (D : CompactDomain d) (lam : D.extension.Form 1)
    (hlam : D.extension.IsSmoothForm lam)

/-- The open locus where the actual differential of the primitive is
nondegenerate. Its existence requires no Liouville field or outwardness. -/
def symplecticNeighborhood : TopologicalSpace.Opens D.extension.Point :=
  ⟨{x | D.extension.Nondegenerate (D.extension.exteriorDerivative lam) x},
    D.extension.isOpen_nondegenerate _ (D.extension.isSmoothForm_exteriorDerivative lam hlam)⟩

theorem carrier_subset_symplecticNeighborhood
    (hnd : ∀ x ∈ D.carrier, D.extension.Nondegenerate
      (D.extension.exteriorDerivative lam) x) :
    D.carrier ⊆ D.symplecticNeighborhood lam hlam := hnd

variable (hnd : ∀ x ∈ D.carrier, D.extension.Nondegenerate
    (D.extension.exteriorDerivative lam) x)

/-- The original compact domain with extension restricted to the
nondegeneracy locus of its actual primitive differential. -/
abbrev symplecticRestriction : CompactDomain d :=
  D.restrict (D.symplecticNeighborhood lam hlam)
    (D.carrier_subset_symplecticNeighborhood lam hlam hnd)

/-- The primitive is the actual pullback under the open-subset inclusion. -/
def symplecticRestrictionPrimitive : (D.symplecticRestriction lam hlam hnd).extension.Form 1 :=
  (D.symplecticRestriction lam hlam hnd).extension.pullback D.extension Subtype.val lam

/-- The localized primitive is smooth in the native restricted atlas. -/
theorem isSmoothForm_symplecticRestrictionPrimitive :
    (D.symplecticRestriction lam hlam hnd).extension.IsSmoothForm
      (D.symplecticRestrictionPrimitive lam hlam hnd) :=
  (D.symplecticRestriction lam hlam hnd).extension.isSmoothForm_pullback_one D.extension
    (D.extension.restrictInclusion (D.symplecticNeighborhood lam hlam)).map lam hlam

/-- The primitive agrees pointwise with the original one on native tangent
fibers; this is a pullback identity, not additional input data. -/
theorem symplecticRestrictionPrimitive_val
    (x : (D.symplecticRestriction lam hlam hnd).extension.Point) :
    D.symplecticRestrictionPrimitive lam hlam hnd x = lam x.val :=
  D.extension.pullback_restrict_val (D.symplecticNeighborhood lam hlam) lam x

/-- The actual exterior derivative also agrees under the inclusion. -/
theorem exteriorDerivative_symplecticRestrictionPrimitive
    (x : (D.symplecticRestriction lam hlam hnd).extension.Point) :
    (D.symplecticRestriction lam hlam hnd).extension.exteriorDerivative
      (D.symplecticRestrictionPrimitive lam hlam hnd) x =
      D.extension.exteriorDerivative lam x.val :=
  D.extension.exteriorDerivative_restrict (D.symplecticNeighborhood lam hlam) lam hlam x

/-- Nondegeneracy holds on the entire open extension, on both sides of the
original compact boundary. -/
theorem nondegenerate_symplecticRestrictionPrimitive
    (x : (D.symplecticRestriction lam hlam hnd).extension.Point) :
    (D.symplecticRestriction lam hlam hnd).extension.Nondegenerate
      ((D.symplecticRestriction lam hlam hnd).extension.exteriorDerivative
        (D.symplecticRestrictionPrimitive lam hlam hnd)) x := by
  change ∀ v, (∀ w, _) → v = 0
  intro v hv
  apply x.property v
  intro w
  have he := hv w
  unfold SmoothManifold.evalTwo at he ⊢
  rw [D.exteriorDerivative_symplecticRestrictionPrimitive lam hlam hnd x] at he
  exact he

/-- The pulled-back primitive has an actual symplectic differential globally
on the restricted extension, including closedness proved from its derivative. -/
theorem isSymplecticOn_symplecticRestrictionPrimitive :
    (D.symplecticRestriction lam hlam hnd).extension.IsSymplecticOn
      ((D.symplecticRestriction lam hlam hnd).extension.exteriorDerivative
        (D.symplecticRestrictionPrimitive lam hlam hnd)) univ :=
  ((D.symplecticRestriction lam hlam hnd).extension.isSymplecticOn_exteriorDerivative_iff _
    (D.isSmoothForm_symplecticRestrictionPrimitive lam hlam hnd) _).mpr
    (fun x _ => D.nondegenerate_symplecticRestrictionPrimitive lam hlam hnd x)

/-- The field is the canonical solution of contraction with the actual
primitive differential, rather than a supplied vector-field witness. -/
abbrev symplecticRestrictionField :=
  (D.symplecticRestriction lam hlam hnd).extension.liouvilleVector
    (D.symplecticRestrictionPrimitive lam hlam hnd)

theorem isSmoothVectorField_symplecticRestrictionField :
    (D.symplecticRestriction lam hlam hnd).extension.IsSmoothVectorField
      (D.symplecticRestrictionField lam hlam hnd) :=
  (D.symplecticRestriction lam hlam hnd).extension.isSmoothVectorField_liouvilleVector _
    (D.isSmoothForm_symplecticRestrictionPrimitive lam hlam hnd)
    (D.nondegenerate_symplecticRestrictionPrimitive lam hlam hnd)

/-- The actual contraction equation holds everywhere on the restricted
extension; it is produced from nondegeneracy, not assumed on the carrier. -/
theorem symplecticRestrictionField_contraction
    (x : (D.symplecticRestriction lam hlam hnd).extension.Point) (v) :
    SmoothManifold.evalTwo
      ((D.symplecticRestriction lam hlam hnd).extension.exteriorDerivative
        (D.symplecticRestrictionPrimitive lam hlam hnd)) x
      (D.symplecticRestrictionField lam hlam hnd x) v =
      SmoothManifold.evalOne (D.symplecticRestrictionPrimitive lam hlam hnd) x v :=
  (D.symplecticRestriction lam hlam hnd).extension.liouvilleVector_contraction _ x
    ((D.symplecticRestriction lam hlam hnd).extension.liouvilleEquation_exists _ x
      (D.nondegenerate_symplecticRestrictionPrimitive lam hlam hnd x)) v

/-- Localization retains the same canonical intrinsic vector in the native
tangent fibers of the original extension. -/
theorem symplecticRestrictionField_val
    (x : (D.symplecticRestriction lam hlam hnd).extension.Point) :
    D.symplecticRestrictionField lam hlam hnd x = D.extension.liouvilleVector lam x.val := by
  symm
  apply D.extension.liouvilleVector_eq lam x.val x.property
  intro v
  have he := D.symplecticRestrictionField_contraction lam hlam hnd x v
  unfold SmoothManifold.evalTwo SmoothManifold.evalOne at he ⊢
  rw [D.exteriorDerivative_symplecticRestrictionPrimitive lam hlam hnd x,
    D.symplecticRestrictionPrimitive_val lam hlam hnd x] at he
  exact he

/-- The entire compact carrier has the same image under the actual inclusion. -/
theorem image_symplecticRestriction_carrier :
    (Subtype.val : (D.symplecticRestriction lam hlam hnd).extension.Point → D.extension.Point) ''
      (D.symplecticRestriction lam hlam hnd).carrier = D.carrier :=
  D.image_restrict_carrier (D.symplecticNeighborhood lam hlam)
    (D.carrier_subset_symplecticNeighborhood lam hlam hnd)

/-- The boundary primitive used by a future outwardness or collar proof is
exactly the original boundary primitive. -/
theorem symplecticRestriction_boundaryForm :
    (D.symplecticRestriction lam hlam hnd).boundaryForm
      (D.symplecticRestrictionPrimitive lam hlam hnd) = D.boundaryForm lam :=
  D.boundaryForm_restrict (D.symplecticNeighborhood lam hlam)
    (D.carrier_subset_symplecticNeighborhood lam hlam hnd) lam

end CompactDomain
end FsFltz.Geometry
