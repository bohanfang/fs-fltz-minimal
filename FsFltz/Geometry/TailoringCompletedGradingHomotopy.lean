import FsFltz.Geometry.TailoringCompletedGradingTransport

/-!
# Native Maslov homotopies extend over the actual cylindrical completion

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2025–2030.
Both endpoint fields are retained literally by the same fixed-collar
extension. This allows native marked-edge comparisons to pass to the
completion without assuming a completed section homotopy.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.LiouvilleDomain.FlowCollar
open SmoothManifold
variable {n : ℕ} {D : LiouvilleDomain (2 * n)} (C : FlowCollar D)

/-- A homotopy on the native open collar neighborhood extends to the
actual completion, with both complex and tensor endpoints unchanged. -/
def cylindricalMaslovHomotopy
    {s r : MaslovRepresentative C.localizedDomain.domain.extension
      (C.localizedDomain.domain.extension.exteriorDerivative C.localizedDomain.liouville.primitive)}
    (H : MaslovHomotopy s r) : MaslovHomotopy (C.cylindricalMaslov s) (C.cylindricalMaslov r) where
  family := H.family.rescalePrimitive (fun _ _ => C.localizedDomain.liouville.smooth_primitive)
    (fun _ => C.localizedDomain.liouville.field)
    (fun a => SmoothNearInterval.constant (chartAt (Model (2 * n)) a).open_target
      (C.localizedDomain.liouville.smooth_field a))
    (fun _ _ => C.localized_contraction)
    (fun z => C.radialWeight z.val) C.smooth_radialWeight
    (fun z => C.radialWeight_positive z.val)
    (fun _ _ z => (C.normalizedRadialWeight_denominator_positive z).ne')
  sourceJ := by
    funext x
    change rankTwoShearComplex _ _ 1 (H.family.J 0 x) = _
    rw [H.sourceJ]
    rfl
  targetJ := by
    funext x
    change rankTwoShearComplex _ _ 1 (H.family.J 1 x) = _
    rw [H.targetJ]
    rfl
  sourceSection := by
    funext x
    change rankTwoShearTensor _ _ 1 (H.family.tensor 0 x) = _
    rw [H.sourceSection]
    rfl
  targetSection := by
    funext x
    change rankTwoShearTensor _ _ 1 (H.family.tensor 1 x) = _
    rw [H.targetSection]
    rfl

/-- The same two native open restrictions preserve all homotopy endpoints. -/
def cylindricalMaslovHomotopyOfNative
    {s r : MaslovRepresentative D.domain.extension
      (D.domain.extension.exteriorDerivative D.liouville.primitive)}
    (H : MaslovHomotopy s r) :
    MaslovHomotopy (C.cylindricalMaslovOfNative s) (C.cylindricalMaslovOfNative r) := by
  let F := (H.family.restrictPrimitive (fun _ _ => D.liouville.smooth_primitive)
    D.symplecticNeighborhood).restrictPrimitive
      (fun _ _ => D.neighborhoodStructure.smooth_primitive) C.neighborhood
  apply C.cylindricalMaslovHomotopy
  refine { family := F, sourceJ := ?_, targetJ := ?_, sourceSection := ?_, targetSection := ?_ }
  · funext x
    change H.family.J 0 x.val.val = s.J x.val.val
    rw [H.sourceJ]
  · funext x
    change H.family.J 1 x.val.val = r.J x.val.val
    rw [H.targetJ]
  · funext x
    change H.family.tensor 0 x.val.val = s.tensor x.val.val
    rw [H.sourceSection]
  · funext x
    change H.family.tensor 1 x.val.val = r.tensor x.val.val
    rw [H.targetSection]

/-- Consequently the actual native extension respects the concrete
Maslov homotopy relation. -/
theorem cylindricalMaslovOfNative_homotopic
    {s r : MaslovRepresentative D.domain.extension
      (D.domain.extension.exteriorDerivative D.liouville.primitive)}
    (H : MaslovHomotopic s r) :
    MaslovHomotopic (C.cylindricalMaslovOfNative s) (C.cylindricalMaslovOfNative r) := by
  obtain ⟨H⟩ := H
  exact ⟨C.cylindricalMaslovHomotopyOfNative H⟩

end FsFltz.Geometry.LiouvilleDomain.FlowCollar
